/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Scheduler
public import Logic.CTree.Core

/-!
# Round-robin refinement of finite branches and branch freedom

`refine_rr` resolves every finite (`Bn`) branch by the alternative selected by a round-robin
cursor, and `BranchFree` characterizes trees without any branch node
(← `CTree/Interp/Refine.v`). This standalone branch refiner supports hidden-branching
counterexamples; ordinary pool scheduling uses the event-only policy interpreter instead.
-/

@[expose] public section
namespace Tisl
open CTree Lean.Order Coinduction
open ITree (Effect)
open Tisl.Yield (rr_pick)

section Refine
variable {E : Effect.{u}} {A : Type u}

/-- Round-robin refinement: every branch node picks the alternative selected by the cursor and
advances it; a branch with no alternative is `stuck`. Guards, steps and events leave the cursor
alone. -/
def refine_rr (t : CTree E Bn A) (cursor : Nat) : CTree E Bn (A × Nat) :=
  match t.unfold with
  | .ret x => pure (x, cursor)
  | .stuck => .stuck
  | .step t' => .step (refine_rr t' cursor)
  | .guard t' => .guard (refine_rr t' cursor)
  | .vis e k => .vis e fun x => refine_rr (k x) cursor
  | .br c k =>
    match c, k with
    | ⟨0⟩, _ => .stuck
    | ⟨n + 1⟩, k => .guard (refine_rr (k ⟨rr_pick n cursor⟩) (cursor + 1))
partial_fixpoint

/-- The cursor as state. Lean's `StateT` already returns `(value, state)`, the order of
`refine_rr`, so no swap is needed (Rocq swaps into its state-first order). -/
def round_robin {E : Effect.{0}} {A : Type} (t : CTree E Bn A) : StateT Nat (CTree E Bn) A :=
  fun cursor => refine_rr t cursor

/-- Refine and forget the final cursor. -/
def run_round_robin (t : CTree E Bn A) (cursor : Nat) : CTree E Bn A :=
  Prod.fst <$> refine_rr t cursor

theorem unfold_refine_rr (t : CTree E Bn A) (cursor : Nat) :
    refine_rr t cursor = match t.unfold with
      | .ret x => pure (x, cursor)
      | .stuck => .stuck
      | .step t' => .step (refine_rr t' cursor)
      | .guard t' => .guard (refine_rr t' cursor)
      | .vis e k => .vis e fun x => refine_rr (k x) cursor
      | .br c k =>
        match c, k with
        | ⟨0⟩, _ => .stuck
        | ⟨n + 1⟩, k => .guard (refine_rr (k ⟨rr_pick n cursor⟩) (cursor + 1)) := by
  rw [refine_rr]

theorem unfold_run_round_robin (t : CTree E Bn A) (m : Nat) :
    run_round_robin t m = match t.unfold with
      | .ret x => pure x
      | .stuck => .stuck
      | .step t' => .step (run_round_robin t' m)
      | .guard t' => .guard (run_round_robin t' m)
      | .vis e k => .vis e fun x => run_round_robin (k x) m
      | .br c k =>
        match c, k with
        | ⟨0⟩, _ => .stuck
        | ⟨n + 1⟩, k => .guard (run_round_robin (k ⟨rr_pick n m⟩) (m + 1)) := by
  unfold run_round_robin
  rw [unfold_refine_rr]
  cases t with
  | br c k => rcases c with ⟨_ | n⟩ <;> simp
  | _ => simp

end Refine

/-! ## Branch-free trees: no `br` node anywhere (steps and `stuck` allowed) -/

section BranchFreedom
variable {E B : Effect.{u}} {A X : Type u}

/-- One layer of branch freedom over the head node of a tree. -/
inductive branchfreeF (R : CTree E B A → Prop) : CTreeF E B A (CTree E B A) → Prop
  | ret (x : A) : branchfreeF R (.ret x)
  | stuck : branchfreeF R .stuck
  | step (t : CTree E B A) : R t → branchfreeF R (.step t)
  | guard (t : CTree E B A) : R t → branchfreeF R (.guard t)
  | vis (e : E.I) (k : E.O e → CTree E B A) : (∀ x, R (k x)) → branchfreeF R (.vis e k)

theorem branchfreeF_mono {R S : CTree E B A → Prop} (h : ∀ t, R t → S t)
    {c : CTreeF E B A (CTree E B A)} : branchfreeF R c → branchfreeF S c
  | .ret x => .ret x
  | .stuck => .stuck
  | .step t ht => .step t (h t ht)
  | .guard t ht => .guard t (h t ht)
  | .vis e k hk => .vis e k fun x => h _ (hk x)

def fbranchfree : Mon (Pred (CTree E B A)) where
  body R t := branchfreeF R t.unfold
  mono h _ := branchfreeF_mono h

/-- `t` has no branch node. -/
def BranchFree (t : CTree E B A) : Prop := gfp fbranchfree t

theorem branchfree_unfold (t : CTree E B A) : BranchFree t ↔ branchfreeF BranchFree t.unfold :=
  ⟨fun h => gfp_pfp (b := fbranchfree) t h, fun h => b_chain (gfp_chain fbranchfree) t h⟩

/-- A one-node invariant establishes branch freedom of the whole tree; clients need only
classify their program's phases. -/
theorem branchfree_invariant (R : CTree E B A → Prop)
    (hstep : ∀ t, R t → branchfreeF R t.unfold) : ∀ t, R t → BranchFree t := fun t ht =>
  coinduction₁ (b := fbranchfree) (fun i : {t // R t} => i.1)
    (fun _ _ CIH ⟨t, ht⟩ => branchfreeF_mono (fun t' ht' => CIH ⟨t', ht'⟩) (hstep t ht)) ⟨t, ht⟩

theorem branchfree_equ_impl (t u : CTree E B A) (h : t = u) (ht : BranchFree t) :
    BranchFree u :=
  h ▸ ht

theorem bf_ret (x : A) : BranchFree (pure x : CTree E B A) :=
  (branchfree_unfold _).2 (by simpa using .ret x)

theorem bf_stuck : BranchFree (.stuck : CTree E B A) :=
  (branchfree_unfold _).2 (by simpa using .stuck)

theorem bf_step (t : CTree E B A) (ht : BranchFree t) : BranchFree (.step t) :=
  (branchfree_unfold _).2 (by simpa using .step t ht)

theorem bf_vis (e : E.I) (k : E.O e → CTree E B A) (hk : ∀ x, BranchFree (k x)) :
    BranchFree (.vis e k) :=
  (branchfree_unfold _).2 (by simpa using .vis e k hk)

/-- Up-to-bind: binding a branch-free tree to continuations in a chain element. -/
theorem branchfree_bind_chain {R : Pred (CTree E B A)} (hR : Chain fbranchfree R) :
    ∀ (t : CTree E B X) (k : X → CTree E B A), BranchFree t → (∀ x, R (k x)) → R (t >>= k) := by
  refine tower (P := fun R : Pred (CTree E B A) => ∀ (t : CTree E B X)
    (k : X → CTree E B A), BranchFree t → (∀ x, R (k x)) → R (t >>= k)) ?_ ?_ R hR
  · intro T hT t k ht hk
    exact Pred.inf_apply.2 fun R hRT => hT R hRT t k ht fun x => Pred.inf_apply.1 (hk x) R hRT
  · intro R hR ih t k ht hk
    have hk' : ∀ x, R (k x) := fun x => b_chain hR (k x) (hk x)
    show branchfreeF R (t >>= k).unfold
    rw [branchfree_unfold] at ht
    cases t with
    | ret x => rw [pure_bind']; exact hk x
    | stuck => simpa using .stuck
    | step t =>
      simp only [unfold_step] at ht
      cases ht with | step _ ht => simpa using .step _ (ih t k ht hk')
    | guard t =>
      simp only [unfold_guard] at ht
      cases ht with | guard _ ht => simpa using .guard _ (ih t k ht hk')
    | vis e k' =>
      simp only [unfold_vis] at ht
      cases ht with | vis _ _ ht => simpa using .vis e _ fun x => ih (k' x) k (ht x) hk'
    | br c k' =>
      simp only [unfold_br] at ht
      nomatch ht

theorem branchfree_bind (t : CTree E B X) (k : X → CTree E B A) (ht : BranchFree t)
    (hk : ∀ x, BranchFree (k x)) : BranchFree (t >>= k) :=
  branchfree_bind_chain (gfp_chain _) t k ht hk

theorem branchfree_iter {I : Type u} (body : I → CTree E B (I ⊕ A))
    (hbody : ∀ i, BranchFree (body i)) : ∀ i, BranchFree (CTree.iter body i) :=
  coinduction₁ (b := fbranchfree) (fun i => CTree.iter body i) fun R hR CIH i => by
    rw [unfold_iter]
    refine branchfree_bind_chain (.step hR) _ _ (hbody i) fun x => ?_
    show branchfreeF R (match x with
      | .inl l => CTree.guard (CTree.iter body l) | .inr r => pure r).unfold
    cases x with
    | inl l => simpa using .guard _ (CIH l)
    | inr r => simpa using .ret r

end BranchFreedom

-- Not ported: `refine_rr_equ`, `run_round_robin_equ`, `branchfree_chain_equ`,
-- `branchfree_bchain_equ`, `branchfree_equ` (`Proper` instances for `equ`, i.e. equality).

end Tisl
