/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.CSL
public import Logic.Yield.Mod
public import Logic.Interp.Refine

/-!
# CoCSL syntax and denotation

The canonical cooperative CSL source language: expressions `CExp`, programs `CProg`, their
denotation into the shared CSL effect layer `CEff`, branch freedom of every denotation, and the
raw head/CPS equations of single source instructions under a continuation
(← `Lang/CoCSL/Mod.v`, lines 1-488).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL
open ITree (Effect)

/-! ## Syntax -/

/-- Natural-number expressions over the shared variable context. -/
inductive CExp : Type
  | var (name : String)
  | lit (value : Nat)
  | plus (a b : CExp)
  | minus (a b : CExp)
  | mult (a b : CExp)

inductive CProg : Type → Type 1
  | read (a : Nat) : CProg Nat
  | write (a v : Nat) : CProg Unit
  | emit (tag value : Nat) : CProg Unit
  | yield : CProg Unit
  | fork (body : CProg Unit) : CProg Unit
  | ret {A : Type} (value : A) : CProg A
  | bind {A B : Type} (body : CProg A) (next : A → CProg B) : CProg B
  | untilNone {A : Type} (body : CProg (Option A)) : CProg Unit
  | alloc (size : Nat) : CProg Nat
  | free (base : Nat) : CProg Unit
  | cas (a expected desired : CExp) : CProg Bool
  | eval (e : CExp) : CProg Nat
  | assign (name : String) (e : CExp) : CProg Unit
  | ite {A : Type} (test : CExp) (yes no : CProg A) : CProg A
  | «while» (test : CExp) (body : CProg Unit) : CProg Unit

/-- Any non-zero natural is true. -/
def is_true (v : Nat) : Bool := v != 0

/-! ## Denotation -/

/-- Expressions evaluate left to right. A successful variable read yields once before returning
the value it captured; a missing variable is stuck. -/
def denote_exp : CExp → CTree CEff Bn Nat
  | .var name =>
    source_get >>= fun ctx =>
      match Ctx.lookup name ctx with
      | some value => source_yield >>= fun _ => pure value
      | none => .stuck
  | .lit n => pure n
  | .plus a b => denote_exp a >>= fun x => denote_exp b >>= fun y => pure (x + y)
  | .minus a b => denote_exp a >>= fun x => denote_exp b >>= fun y => pure (x - y)
  | .mult a b => denote_exp a >>= fun x => denote_exp b >>= fun y => pure (x * y)

/-- Program flow: `none` is a halted thread (a forked child after its body), `some x` a normal
result. -/
def denote_flow : {A : Type} → CProg A → CTree CEff Bn (Option A)
  | _, .read a => heap_read a >>= fun x => pure (some x)
  | _, .write a v => heap_write a v >>= fun _ => pure (some ())
  | _, .emit q v =>
    CTree.trigger (E := CEff) (.inr (.inr (.inr (.inr (q, v))))) >>= fun _ => pure (some ())
  | _, .yield => source_yield >>= fun _ => pure (some ())
  | _, .fork body =>
    source_fork >>= fun child =>
      if child then denote_flow body >>= fun _ => pure none else pure (some ())
  | _, .ret x => pure (some x)
  | _, .bind body next =>
    denote_flow body >>= fun flow =>
      match flow with
      | none => pure none
      | some x => denote_flow (next x)
  | _, .untilNone body =>
    CTree.iter (fun (_ : Unit) =>
      denote_flow body >>= fun flow =>
        match flow with
        | none => pure (.inr none)
        | some none => pure (.inr (some ()))
        | some (some _) => pure (.inl ())) ()
  | _, .alloc size => heap_alloc size >>= fun a => pure (some a)
  | _, .free base => heap_free base >>= fun _ => pure (some ())
  | _, .cas a expected desired =>
    denote_exp a >>= fun addr =>
    denote_exp expected >>= fun old =>
    denote_exp desired >>= fun value =>
    heap_cas addr old value >>= fun b =>
    pure (some b)
  | _, .eval e => denote_exp e >>= fun value => pure (some value)
  | _, .assign name e =>
    denote_exp e >>= fun value =>
    source_get >>= fun ctx =>
    source_put (Ctx.add name value ctx) >>= fun _ =>
    pure (some ())
  | _, .ite test yes no =>
    denote_exp test >>= fun value =>
      if is_true value then denote_flow yes else denote_flow no
  | _, .while test body =>
    CTree.iter (fun (_ : Unit) =>
      denote_exp test >>= fun value =>
        if is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | some _ => pure (.inl ())
            | none => pure (.inr none)
        else pure (.inr (some ()))) ()

/-- One guarded `while` iteration: a false test exits with `some ()`, a completed body
continues, and a halted body propagates `none`. -/
def cwhile_iteration (test : CExp) (body : CProg Unit) (_ : Unit) :
    CTree CEff Bn (Unit ⊕ Option Unit) :=
  denote_exp test >>= fun value =>
    if is_true value then
      denote_flow body >>= fun flow =>
        match flow with
        | some _ => pure (.inl ())
        | none => pure (.inr none)
    else pure (.inr (some ()))

theorem denote_flow_cwhile (test : CExp) (body : CProg Unit) :
    denote_flow (.while test body) = CTree.iter (cwhile_iteration test body) () := by
  rw [denote_flow]; rfl

/-- A source thread: the flow followed by thread termination. -/
def denote (p : CProg Unit) : Thread sE Bn :=
  denote_flow p >>= fun _ => pure ⟨⟩

/-! ## Branch freedom -/

private theorem bf_vis_bind {X Y : Type} (e : CEff.I) (k : CEff.O e → X)
    (K : X → CTree CEff Bn Y) (hK : ∀ x, BranchFree (K x)) :
    BranchFree (CTree.vis (B := Bn) e (fun x => pure (k x)) >>= K) :=
  branchfree_bind _ _ (bf_vis _ _ fun _ => bf_ret _) hK

theorem denote_exp_branchfree (e : CExp) : BranchFree (denote_exp e) := by
  induction e with
  | var name =>
    refine bf_vis_bind _ _ _ fun ctx => ?_
    cases Ctx.lookup name ctx with
    | some v => exact bf_vis_bind _ _ _ fun _ => bf_ret _
    | none => exact bf_stuck
  | lit n => exact bf_ret n
  | plus a b iha ihb | minus a b iha ihb | mult a b iha ihb =>
    exact branchfree_bind _ _ iha fun _ => branchfree_bind _ _ ihb fun _ => bf_ret _

theorem denote_flow_branchfree {A : Type} (p : CProg A) : BranchFree (denote_flow p) := by
  induction p with
  | read a | write a v | emit q v | yield | alloc size | free base =>
    exact bf_vis_bind _ _ _ fun _ => bf_ret _
  | fork body ih =>
    refine bf_vis_bind _ _ _ fun child => ?_
    cases child
    · exact bf_ret _
    · exact branchfree_bind _ _ ih fun _ => bf_ret _
  | ret x => exact bf_ret _
  | bind body next ih ihn =>
    rw [denote_flow]
    refine branchfree_bind _ _ ih fun flow => ?_
    cases flow
    · exact bf_ret _
    · exact ihn _
  | untilNone body ih =>
    refine branchfree_iter _ (fun _ => branchfree_bind _ _ ih fun flow => ?_) _
    rcases flow with _ | _ | _ <;> exact bf_ret _
  | cas a expected desired =>
    exact branchfree_bind _ _ (denote_exp_branchfree a) fun _ =>
      branchfree_bind _ _ (denote_exp_branchfree expected) fun _ =>
      branchfree_bind _ _ (denote_exp_branchfree desired) fun _ =>
      bf_vis_bind _ _ _ fun _ => bf_ret _
  | eval e => exact branchfree_bind _ _ (denote_exp_branchfree e) fun _ => bf_ret _
  | assign name e =>
    exact branchfree_bind _ _ (denote_exp_branchfree e) fun _ =>
      bf_vis_bind _ _ _ fun _ => bf_vis_bind _ _ _ fun _ => bf_ret _
  | ite test yes no ihy ihn =>
    refine branchfree_bind _ _ (denote_exp_branchfree test) fun v => ?_
    cases is_true v
    · exact ihn
    · exact ihy
  | «while» test body ih =>
    refine branchfree_iter _ (fun _ =>
      branchfree_bind _ _ (denote_exp_branchfree test) fun v => ?_) _
    cases is_true v
    · exact bf_ret _
    · exact branchfree_bind _ _ ih fun flow => by cases flow <;> exact bf_ret _

theorem denote_branchfree (p : CProg Unit) : BranchFree (denote p) :=
  branchfree_bind _ _ (denote_flow_branchfree p) fun _ => bf_ret _

theorem denote_fork_bind (p : CProg Unit) (next : Unit → CProg Unit) :
    denote (.bind (.fork p) next) =
      .vis (.inr (.inl ⟨⟩)) fun child : Bool => if child then denote p else denote (next ()) := by
  simp only [denote, denote_flow, source_fork, vis_bind, bind_assoc, pure_bind']
  congr 1; funext child
  cases child <;> simp

/-! ## Head normalisation of `denote_flow`

What a single source instruction looks like at the head of a thread, before any scheduling is
applied. -/

@[grind =] theorem source_raw_read_head (a : Nat) (K : Option Nat → Thread sE Bn) :
    (denote_flow (.read a) >>= K) = .vis (.inr (.inr (.inl (.read a)))) fun v => K (some v) := by
  simp [denote_flow, heap_read, CTree.trigger', CTree.vis']; rfl

@[grind =] theorem source_raw_write_head (a v : Nat) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.write a v) >>= K) =
      .vis (.inr (.inr (.inl (.write a v)))) fun _ => K (some ()) := by
  simp [denote_flow, heap_write, CTree.trigger', CTree.vis']; rfl

/-- Immediate CAS on literal operands; general operands first evaluate with `source_raw_cas`. -/
@[grind =] theorem source_raw_cas_head (a old desired : Nat) (K : Option Bool → Thread sE Bn) :
    (denote_flow (.cas (.lit a) (.lit old) (.lit desired)) >>= K) =
      .vis (.inr (.inr (.inl (.cas a old desired)))) fun b => K (some b) := by
  simp [denote_flow, denote_exp, heap_cas, CTree.trigger', CTree.vis']; rfl

/-- Operands evaluate once, in address/expected/desired order, before the atomic heap
operation; expression yields remain inside the thread. -/
theorem source_raw_cas (a expected desired : CExp) (K : Option Bool → Thread sE Bn) :
    (denote_flow (.cas a expected desired) >>= K) =
      (denote_exp a >>= fun addr =>
       denote_exp expected >>= fun old =>
       denote_exp desired >>= fun value =>
       denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K) := by
  simp [denote_flow, denote_exp]

@[grind =] theorem source_raw_emit_head (tag value : Nat) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.emit tag value) >>= K) =
      .vis (.inr (.inr (.inr (.inr (tag, value))))) fun _ => K (some ()) := by
  simp [denote_flow, CTree.trigger]

@[grind =] theorem source_raw_yield_head (K : Option Unit → Thread sE Bn) :
    (denote_flow .yield >>= K) = .vis (.inl ⟨⟩) fun _ => K (some ()) := by
  simp [denote_flow, source_yield]

@[grind =] theorem source_raw_alloc_head (size : Nat) (K : Option Nat → Thread sE Bn) :
    (denote_flow (.alloc size) >>= K) =
      .vis (.inr (.inr (.inl (.alloc size)))) fun base => K (some base) := by
  simp [denote_flow, heap_alloc, CTree.trigger', CTree.vis']; rfl

@[grind =] theorem source_raw_free_head (base : Nat) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.free base) >>= K) =
      .vis (.inr (.inr (.inl (.free base)))) fun _ => K (some ()) := by
  simp [denote_flow, heap_free, CTree.trigger', CTree.vis']; rfl

@[grind =] theorem source_raw_fork_head (child : CProg Unit) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.fork child) >>= K) =
      .vis (.inr (.inl ⟨⟩)) fun spawned : Bool =>
        if spawned then denote_flow child >>= fun _ => K none else K (some ()) := by
  simp only [denote_flow, source_fork, vis_bind, pure_bind']
  congr 1; funext spawned
  cases spawned <;> simp

/-- The actual `untilNone` continuations, including halt flow. -/
def until_tail {A : Type} (body : CProg (Option A)) (K : Option Unit → Thread sE Bn) :
    Option (Option A) → Thread sE Bn
  | none => K none
  | some none => K (some ())
  | some (some _) => .guard (denote_flow (.untilNone body) >>= K)

/-- Raw source equations retain the outer option halt flow: `none` skips `next` and reaches the
continuation unchanged; `some x` runs `next x` before the continuation. -/
theorem source_raw_bind {A B : Type} (p : CProg A) (next : A → CProg B)
    (K : Option B → Thread sE Bn) :
    (denote_flow (.bind p next) >>= K) =
      (denote_flow p >>= fun flow =>
        match flow with
        | none => K none
        | some x => denote_flow (next x) >>= K) := by
  rw [denote_flow, bind_assoc]
  congr 1; funext flow
  cases flow <;> simp

theorem denote_read_bind (a : Nat) (next : Nat → CProg Unit) :
    denote (.bind (.read a) next) =
      .vis (E := CEff) (.inr (.inr (.inl (.read a)))) fun v => denote (next v) := by
  rw [denote, source_raw_bind, source_raw_read_head]; rfl

theorem source_raw_ret {A : Type} (x : A) (K : Option A → Thread sE Bn) :
    (denote_flow (.ret x) >>= K) = K (some x) := by
  simp [denote_flow]

theorem source_raw_until {A : Type} (body : CProg (Option A)) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.untilNone body) >>= K) = (denote_flow body >>= until_tail body K) := by
  rw (occs := .pos [1]) [denote_flow]
  rw [unfold_iter, bind_assoc, bind_assoc]
  congr 1; funext flow
  rcases flow with _ | _ | _ <;> simp [until_tail, denote_flow]

/-- Expression and control statements as raw CPS equations. -/
theorem source_raw_eval (e : CExp) (K : Option Nat → Thread sE Bn) :
    (denote_flow (.eval e) >>= K) = (denote_exp e >>= fun value => K (some value)) := by
  simp [denote_flow]

theorem source_raw_assign (name : String) (e : CExp) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.assign name e) >>= K) =
      (denote_exp e >>= fun value => source_get >>= fun ctx =>
        source_put (Ctx.add name value ctx) >>= fun _ => K (some ())) := by
  simp [denote_flow]

theorem source_raw_if {A : Type} (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) :
    (denote_flow (.ite test yes no) >>= K) =
      (denote_exp test >>= fun value =>
        if is_true value then denote_flow yes >>= K else denote_flow no >>= K) := by
  rw [denote_flow, bind_assoc]
  congr 1; funext value
  split <;> rfl

theorem source_raw_while (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.while test body) >>= K) =
      (CTree.iter (cwhile_iteration test body) () >>= K) := by
  rw [denote_flow_cwhile]

-- Not ported: nothing. Rocq `Module CoCSLSyntax` (+ `Export`) is flattened into `CoCSL`.

end CoCSL
