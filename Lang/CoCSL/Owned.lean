/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Sequential
public import Logic.Sep.OwnedInterp

/-!
# Source admission and coupling for CoCSL owned components

Initial owned configurations of a forked CoCSL program, the admission condition on the two
components and their reserved heaps, and the `coupled` invariant of configurations reachable from
an admitted fork; admitted forks are (actively) erasable and their owned runner is the original
nondeterministic runner (← `Lang/CoCSL/Owned.v`).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx Tisl.Pcm
open ITree (Effect)

universe u

def init_owned (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx) (base : Nat) :
    OwnedCfg :=
  init_owned_threads (denote child) (denote parent) h h' ctx base

def init_local (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx) (base : Nat)
    (focused : Bool) : OwnedCfg :=
  init_local_thread i (denote p) h ctx base focused

def component_ok {A : Type} (p : CProg A) : Prop := prog_ok (okE_thread component_event_ok) p

def admissible (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx) (base : Nat) :
    Prop :=
  managed_wf h ∧ managed_wf h' ∧ h # h' ∧
  component_ok child ∧ component_ok parent ∧
  confined h (project .child (init_owned child parent h h' ctx base)) ∧
  confined h' (project .parent (init_owned child parent h h' ctx base))

def coupled (c : OwnedCfg) : Prop :=
  ∃ child parent h h' ctx base d,
    admissible child parent h h' ctx base ∧
    Star owned_next (init_owned child parent h h' ctx base) d ∧
    owned_equ d c

theorem project_init_child (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    owned_equ (project .child (init_owned child parent h h' ctx base))
      (init_local .child child h ctx base false) :=
  project_init_threads_child _ _ h h' ctx base

theorem project_init_parent (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    owned_equ (project .parent (init_owned child parent h h' ctx base))
      (init_local .parent parent h' ctx base true) :=
  project_init_threads_parent _ _ h h' ctx base

theorem init_local_select (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx)
    (base : Nat) (a : OwnedAction) (d : OwnedCfg) :
    owned_step (init_local i p h ctx base false) a d ↔
      a = act i .select ∧ d = init_local i p h ctx base true :=
  init_local_thread_select i _ h ctx base a d

theorem init_owned_wf (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    managed_wf h → managed_wf h' → h # h' → owned_wf (init_owned child parent h h' ctx base) :=
  init_owned_threads_wf _ _ h h' ctx base

theorem coupled_init (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx) (base : Nat) :
    admissible child parent h h' ctx base → coupled (init_owned child parent h h' ctx base) :=
  fun Ha => ⟨child, parent, h, h', ctx, base, _, Ha, .refl, owned_equ_Equivalence.refl _⟩

theorem coupled_equ (c d : OwnedCfg) : owned_equ c d → coupled c → coupled d := by
  intro He Hc; obtain rfl := owned_equ_eq He; exact Hc

theorem coupled_step (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    coupled c → owned_step c a c' → coupled c' := by
  rintro ⟨ch, pa, h, h', ctx, base, d, Ha, Hr, He⟩ Hs
  obtain rfl := owned_equ_eq He
  exact ⟨ch, pa, h, h', ctx, base, c', Ha, Hr.tail ⟨a, Hs⟩, owned_equ_Equivalence.refl _⟩

theorem coupled_weak (i : Side) (c c' : OwnedCfg) : coupled c → weak_next i c c' → coupled c' := by
  rintro Hc ⟨mid, Hstar, a, Hs, -⟩
  refine coupled_step mid a c' ?_ Hs
  clear Hs
  induction Hstar with
  | refl => exact Hc
  | tail _ hyz ih => obtain ⟨b, Hb, -⟩ := hyz; exact coupled_step _ b _ ih Hb

theorem coupled_wf (c : OwnedCfg) : coupled c → owned_wf c := by
  rintro ⟨ch, pa, h, h', ctx, base, d, ⟨Hw, Hw', Hd, -⟩, Hr, He⟩
  refine owned_wf_equ d c He ?_
  clear He
  induction Hr with
  | refl => exact init_owned_wf ch pa h h' ctx base Hw Hw' Hd
  | tail _ hyz ih => obtain ⟨a, Ha⟩ := hyz; exact owned_step_wf _ a _ ih Ha

/-- Every heap primitive of the program touches an address reserved in `r`; a CAS address must be
a literal. -/
def addr_ok (r : ManagedHeap) : {A : Type} → CProg A → Prop
  | _, .read a => r.1 a ≠ none
  | _, .write a _ => r.1 a ≠ none
  | _, .free b => b = 0 ∨ r.2 b ≠ none
  | _, .cas (.lit a) _ _ => r.1 a ≠ none
  | _, .cas _ _ _ => False
  | _, .fork body => addr_ok r body
  | _, .bind body next => addr_ok r body ∧ ∀ x, addr_ok r (next x)
  | _, .untilNone body => addr_ok r body
  | _, .ite _ yes no => addr_ok r yes ∧ addr_ok r no
  | _, .while _ body => addr_ok r body
  | _, _ => True

private theorem framable_guards {E B : Effect.{u}} {A : Type u} (okE : E.I → Prop) (n : Nat)
    (t : CTree E B A) : Framable okE (guards n t) → Framable okE t := by
  induction n with
  | zero => exact id
  | succ n ih =>
    intro H
    rw [guards_succ, framable_unfold, unfold_guard] at H
    cases H with | guard _ H => exact ih H

private theorem headed_framable (r : ManagedHeap) (t u : Thread sE Bn) :
    Framable (okE_thread (prim_addr_ok r)) t → headed t u →
      Framable (okE_thread (prim_addr_ok r)) u :=
  fun Ht ⟨n, Hn⟩ => framable_guards _ n u (Hn ▸ Ht)

private theorem framable_vis_inv {E B : Effect.{u}} {A : Type u} (okE : E.I → Prop) (e : E.I)
    (k : E.O e → CTree E B A) : Framable okE (.vis e k) → okE e ∧ ∀ x, Framable okE (k x) := by
  intro H
  rw [framable_unfold, unfold_vis] at H
  cases H with | vis _ _ he hk => exact ⟨he, hk⟩

private theorem framable_step_inv {E B : Effect.{u}} {A : Type u} (okE : E.I → Prop)
    (t : CTree E B A) : Framable okE (.step t) → Framable okE t := by
  intro H
  rw [framable_unfold, unfold_step] at H
  cases H with | step _ H => exact H

private theorem exp_framable (r : ManagedHeap) (e : CExp) :
    Framable (okE_thread (prim_addr_ok r)) (denote_exp e) := by
  refine denote_exp_framable _ e ?_
  induction e with
  | var _ => exact ⟨trivial, trivial⟩
  | lit _ => trivial
  | plus _ _ ha hb | minus _ _ ha hb | mult _ _ ha hb => exact ⟨ha, hb⟩

private theorem addr_ok_framable (r : ManagedHeap) {A : Type} (p : CProg A) :
    addr_ok r p → Framable (okE_thread (prim_addr_ok r)) (denote_flow p) := by
  induction p with
  | read a | write a v | free base => exact fun Hp => fr_heap _ _ Hp _ fun _ => fr_ret _ _
  | alloc size => exact fun _ => fr_heap _ _ trivial _ fun _ => fr_ret _ _
  | emit q v | yield => exact fun _ => fr_trig _ _ trivial _ fun _ => fr_ret _ _
  | fork body ih =>
    intro Hp
    refine fr_trig _ _ trivial _ fun child => ?_
    cases child
    · exact fr_ret _ _
    · exact framable_bind _ _ _ (ih Hp) fun _ => fr_ret _ _
  | ret x => exact fun _ => fr_ret _ _
  | bind body next ih ihn =>
    rintro ⟨Hb, Hn⟩
    rw [denote_flow]
    refine framable_bind _ _ _ (ih Hb) fun flow => ?_
    cases flow
    · exact fr_ret _ _
    · exact ihn _ (Hn _)
  | untilNone body ih =>
    intro Hp
    refine framable_iter _ _ (fun _ => framable_bind _ _ _ (ih Hp) fun flow => ?_) _
    rcases flow with _ | _ | _ <;> exact fr_ret _ _
  | cas a expected desired =>
    cases a with
    | lit a =>
      intro Hp
      simp only [denote_flow, denote_exp, pure_bind']
      exact framable_bind _ _ _ (exp_framable r expected) fun old =>
        framable_bind _ _ _ (exp_framable r desired) fun value =>
        fr_heap _ _ Hp _ fun _ => fr_ret _ _
    | _ => exact False.elim
  | eval e => exact fun _ => framable_bind _ _ _ (exp_framable r e) fun _ => fr_ret _ _
  | assign name e =>
    exact fun _ => framable_bind _ _ _ (exp_framable r e) fun v =>
      fr_trig _ _ trivial _ fun ctx => fr_trig _ _ trivial _ fun _ => fr_ret _ _
  | ite test yes no ihy ihn =>
    rintro ⟨Hy, Hn⟩
    refine framable_bind _ _ _ (exp_framable r test) fun v => ?_
    cases is_true v
    · exact ihn Hn
    · exact ihy Hy
  | «while» test body ih =>
    intro Hp
    refine framable_iter _ _ (fun _ =>
      framable_bind _ _ _ (exp_framable r test) fun v => ?_) _
    cases is_true v
    · exact fr_ret _ _
    · exact framable_bind _ _ _ (ih Hp) fun flow => by cases flow <;> exact fr_ret _ _

private def confined_pool_ok (r : ManagedHeap) (c : OwnedCfg) : Prop :=
  pool_framable (prim_addr_ok r) c.pool.threads

private theorem confined_pool_ok_step (r : ManagedHeap) (c : OwnedCfg) (a : OwnedAction)
    (c' : OwnedCfg) : confined_pool_ok r c → owned_step c a c' → confined_pool_ok r c' := by
  intro Hv Hs
  unfold confined_pool_ok at *
  rcases hp : c.pool with ⟨_ | n, v, g, _ | j⟩
  · exact (owned_step_empty c a c' (by rw [hp]) Hs).elim
  · exact (owned_step_empty c a c' (by rw [hp]) Hs).elim
  · obtain ⟨j, rfl, rfl⟩ := (owned_step_sel c n v g a c' hp).1 Hs
    rw [hp] at Hv; exact Hv
  · rw [hp] at Hv
    have Ht := fun u (h : headed v[j] u) => headed_framable r _ u (Hv j) h
    rcases (owned_step_focus c n v g j a c' hp).1 Hs with
      ⟨t, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨Hh, rfl, rfl⟩ |
      ⟨e, k, kind, y, c1, Hh, -, rfl, rfl⟩
    · exact pool_framable_replace _ v j t Hv (framable_step_inv _ _ (Ht _ Hh))
    · exact pool_framable_replace _ v j _ Hv ((framable_vis_inv _ _ _ (Ht _ Hh)).2 _)
    · have Hk := (framable_vis_inv _ _ _ (Ht _ Hh)).2
      exact pool_framable_cons _ _ _ (Hk true) (pool_framable_replace _ v j _ Hv (Hk false))
    · exact pool_framable_remove _ v j Hv
    · exact pool_framable_replace _ v j _ Hv ((framable_vis_inv _ _ _ (Ht _ Hh)).2 y)

private theorem pool_ok_reach (r : ManagedHeap) (c c' : OwnedCfg) :
    Star owned_next c c' → confined_pool_ok r c → confined_pool_ok r c' := by
  intro H Hc
  induction H with
  | refl => exact Hc
  | tail _ hyz ih => obtain ⟨a, Hs⟩ := hyz; exact confined_pool_ok_step r _ a _ ih Hs

theorem addr_ok_confined (r : ManagedHeap) (i : Side) (p : CProg Unit) (h : ManagedHeap)
    (ctx : Ctx) (base : Nat) (focused : Bool) :
    addr_ok r p → confined r (init_local i p h ctx base focused) := by
  intro Hp c Hc t j e k Hf Hh
  have Hv : confined_pool_ok r c := pool_ok_reach r _ _ Hc fun x => by
    obtain rfl := fin1_eq x
    exact framable_bind _ _ _ (addr_ok_framable r p Hp) fun _ => fr_ret _ _
  unfold focused_thread at Hf
  split at Hf
  · rename_i x _
    cases Hf
    exact (framable_vis_inv _ _ _ (headed_framable r _ _ (Hv x) Hh)).1
  · cases Hf

theorem admissible_intro (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    managed_wf h → managed_wf h' → h # h' →
    component_ok child → component_ok parent →
    addr_ok h child → addr_ok h' parent →
    admissible child parent h h' ctx base :=
  fun W W' D Oc Op Ac Ap => ⟨W, W', D, Oc, Op,
    confined_equ _ _ _ (owned_equ_Equivalence.symm (project_init_child child parent h h' ctx base))
      (addr_ok_confined _ _ _ _ _ _ _ Ac),
    confined_equ _ _ _ (owned_equ_Equivalence.symm (project_init_parent child parent h h' ctx base))
      (addr_ok_confined _ _ _ _ _ _ _ Ap)⟩

theorem admissible_head_confined (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) (d : OwnedCfg) :
    admissible child parent h h' ctx base →
    Star owned_next (init_owned child parent h h' ctx base) d →
    head_confined d := by
  rintro ⟨-, -, -, -, -, HC, HP⟩ Hd t i e k Hf Hh
  have Ha : d.anchor = (init_owned child parent h h' ctx base).anchor := by
    clear Hf Hh
    induction Hd with
    | refl => rfl
    | tail _ hyz ih => obtain ⟨a, Hs⟩ := hyz; exact (owned_step_frozen _ a _ Hs).1.trans ih
  rw [Ha]
  have Hfp := focused_project i _ _ Hf
  obtain ⟨d0, Hr0, Heq0⟩ := reach_project i _ _ Hd
  obtain rfl := owned_equ_eq Heq0
  cases i
  · exact HC _ Hr0 t .child e k Hfp Hh
  · exact HP _ Hr0 t .parent e k Hfp Hh

private theorem denote_thread_ok (p : CProg Unit) :
    component_ok p →
      Framable (okE_thread component_event_ok) (denote p) ∧ BranchFree (denote p) :=
  fun Hp => ⟨framable_bind _ _ _ (denote_flow_framable _ p Hp) fun _ => fr_ret _ _,
    denote_branchfree p⟩

theorem admissible_erasable (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    admissible child parent h h' ctx base → erasable (init_owned child parent h h' ctx base) := by
  intro Ha
  obtain ⟨Wh, Wh', D, Oc, Op, -⟩ := id Ha
  obtain ⟨Fc, Bc⟩ := denote_thread_ok child Oc
  obtain ⟨Fp, Bp⟩ := denote_thread_ok parent Op
  refine ⟨init_owned_wf child parent h h' ctx base Wh Wh' D, fun j => ?_, fun j => ?_,
    fun d Hd => admissible_head_confined _ _ _ _ _ _ _ Ha Hd⟩
  · match j with
    | ⟨0, _⟩ => exact Fc
    | ⟨1, _⟩ => exact Fp
  · match j with
    | ⟨0, _⟩ => exact Bc
    | ⟨1, _⟩ => exact Bp

theorem coupled_erasable (c : OwnedCfg) : coupled c → erasable c := by
  rintro ⟨child, parent, h, h', ctx, base, d, Ha, Hd, E⟩
  exact erasable_equ d c E (erasable_reach _ d (admissible_erasable _ _ _ _ _ _ Ha) Hd)

theorem admissible_active_erasable (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    admissible child parent h h' ctx base →
    active_erasable (init_owned child parent h h' ctx base) := by
  intro Ha
  have He := admissible_erasable _ _ _ _ _ _ Ha
  obtain ⟨-, -, -, -, -, HC, HP⟩ := Ha
  obtain ⟨W, F, Bf, -⟩ := id He
  have HL : ∀ i, erasable (project i (init_owned child parent h h' ctx base)) := by
    intro i
    refine erasable_single_side i _ (owned_wf_project i _ W) (fun r => ?_) (fun r => ?_)
      (fun r => ?_) ?_
    · obtain ⟨j, -, -, -, Htag⟩ := project_index_inv i _ r; exact Htag
    · obtain ⟨j, -, -, Et, -⟩ := project_index_inv i _ r
      have H := F j; rw [← Et] at H; exact H
    · obtain ⟨j, -, -, Et, -⟩ := project_index_inv i _ r
      have H := Bf j; rw [← Et] at H; exact H
    · cases i
      · exact HC
      · exact HP
  exact ⟨He, HL .child, HL .parent⟩

theorem coupled_active_erasable (c : OwnedCfg) : coupled c → active_erasable c := by
  rintro ⟨child, parent, h, h', ctx, base, d, Ha, Hd, E⟩
  refine active_erasable_equ d c E ?_
  clear E
  have H0 := admissible_active_erasable _ _ _ _ _ _ Ha
  induction Hd with
  | refl => exact H0
  | tail _ hyz ih => obtain ⟨a, Hs⟩ := hyz; exact active_erasable_step _ a _ ih Hs

/-- The owned runner of an outer fork is the original nondeterministic runner on the joined heap. -/
theorem owned_fork_runner (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) :
    owned_interp (init_owned child (k ()) h h' ctx base) ~
      run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base)) :=
  sbisim_symm (run_nd_fork_bind child k _)

-- Not ported: `framable_equ` (Rocq `≅` is Lean `=`; rewriting suffices), Ltac `fr_trig` (the
-- lemmas `fr_trig`/`fr_heap` of `Lang/CoCSL/Frame.lean`), `okR` (inlined as `prim_addr_ok r`).
-- `confined_pool_ok` and the Rocq `Local Lemma`s are `private`.

end CoCSL
