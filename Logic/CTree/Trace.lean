/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Core
public import Logic.Events.Writer
public import Logic.World

/-!
# Finite observation traces

Finite log prefixes (`emit_list`), finite label executions (`FiniteSteps`), infinite chunked
executions (`realizes`), guard/log alignment (`rr_aligned`), token prefixes and repeated
observation batches (`emit_batches`) (← `CTree/Trace.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinductive CTree.Coinduction
open ITree (Effect)

variable {E B : Effect.{u}} {W V I A X Y : Type u}

/-! ## Finite observation traces and their operational laws -/

/-- Log every element of `xs`, then continue as `t`. -/
def emit_list (xs : List W) (t : ctreeW W B X) : ctreeW W B X :=
  xs.foldr (fun o k => log o >>= fun _ => k) t

/-- The logged values of a label list. -/
def label_logs (labels : List (Label (writerE W))) : List W :=
  labels.flatMap fun | .obs o _ => [o] | _ => []

/-- The number of silent labels in a label list. -/
def label_taus (labels : List (Label (writerE W))) : Nat :=
  (labels.filter fun | .tau => true | _ => false).length

/-- The world reached after observing the logs `xs` from `w`. -/
def after_logs : List W → World (writerE W) → World (writerE W)
  | [], w => w
  | o :: rest, _ => after_logs rest (.obs (E := writerE W) o ⟨⟩)

theorem after_logs_not_done (xs : List W) {w : World (writerE W)} (h : NotDone w) :
    NotDone (after_logs xs w) := by
  induction xs generalizing w with
  | nil => exact h
  | cons o rest ih => exact ih (.obs _ _)

theorem after_logs_app (xs ys : List W) (w : World (writerE W)) :
    after_logs (xs ++ ys) w = after_logs ys (after_logs xs w) := by
  induction xs generalizing w with
  | nil => rfl
  | cons o xs ih => exact ih _

/-- Relabelling preserves the final observation of a finite log prefix. -/
theorem after_logs_map (f : W → V) (xs : List W) (initial final : W)
    (h : after_logs xs (.obs (E := writerE W) initial ⟨⟩) = .obs (E := writerE W) final ⟨⟩) :
    after_logs (xs.map f) (.obs (E := writerE V) (f initial) ⟨⟩) =
      .obs (E := writerE V) (f final) ⟨⟩ := by
  induction xs generalizing initial with
  | nil => cases h; rfl
  | cons o xs ih => exact ih o h

@[simp] theorem emit_list_nil (t : ctreeW W B X) : emit_list [] t = t := rfl

@[simp] theorem emit_list_cons (o : W) (xs : List W) (t : ctreeW W B X) :
    emit_list (o :: xs) t = .vis (E := writerE W) o fun _ => emit_list xs t :=
  log_vis o _

theorem emit_list_app (xs ys : List W) (t : ctreeW W B X) :
    emit_list (xs ++ ys) t = emit_list xs (emit_list ys t) :=
  List.foldr_append

theorem emit_list_equ (xs : List W) {t u : ctreeW W B X} (h : t = u) :
    emit_list xs t = emit_list xs u :=
  h ▸ rfl

theorem emit_list_sbisim (xs : List W) {t u : ctreeW W B X} (h : t ~ u) :
    emit_list xs t ~ emit_list xs u := by
  induction xs with
  | nil => exact h
  | cons o xs ih => simpa using sb_vis (E := writerE W) o fun _ => ih

theorem emit_list_bind (xs : List W) (t : ctreeW W B X) (k : X → ctreeW W B Y) :
    (emit_list xs t >>= k) = emit_list xs (t >>= k) := by
  induction xs with
  | nil => rfl
  | cons o xs ih => simp [ih]

theorem emit_list_ret_bind (xs : List W) (x : X) (k : X → ctreeW W B Y) :
    (emit_list xs (pure x) >>= k) = emit_list xs (k x) := by
  simp [emit_list_bind]

/-- Return values are observable labels: equal responses, not merely pointwise-equal ones. -/
theorem emit_list_ret_injective (xs ys : List W) (x y : X)
    (h : emit_list (B := B) xs (pure x) ~ emit_list (B := B) ys (pure y)) : xs = ys ∧ x = y := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, sbisim_ret_inv h⟩
    | cons p ys => simp only [emit_list_nil, emit_list_cons] at h; exact (sbisim_ret_vis_inv h).elim
  | cons o xs ih =>
    cases ys with
    | nil =>
      simp only [emit_list_nil, emit_list_cons] at h
      exact (sbisim_ret_vis_inv (sbisim_symm h)).elim
    | cons p ys =>
      simp only [emit_list_cons] at h
      cases sbisim_vis_invT (E := writerE W) PUnit.unit h
      obtain ⟨rfl, rfl⟩ := ih ys (sbisim_vis_inv h ⟨⟩)
      exact ⟨rfl, rfl⟩

theorem emit_list_ret_not_stuck (xs : List W) (x : X) :
    ¬ emit_list (B := B) xs (pure x) ~ (CTree.stuck : ctreeW W B X) := by
  intro h
  have hs := isStuck_sbisim h stuck_isStuck
  cases xs with
  | nil => exact hs _ _ (trans_ret x)
  | cons o xs =>
    simp only [emit_list_cons] at hs
    exact hs _ _ (trans_vis (E := writerE W) PUnit.unit _)

theorem emit_list_chain {R : Rel (ctreeW W B X) (ctreeW W B X)} (hR : Chain (sb Eq) R)
    (logs : List W) {t u : ctreeW W B X} (h : R t u) : R (emit_list logs t) (emit_list logs u) := by
  induction logs with
  | nil => exact h
  | cons o rest ih => simpa using vis_chain hR (E := writerE W) o fun _ => ih

/-- A finite execution of `t` along the labels `labels`, ending in `v`. -/
inductive FiniteSteps {X : Type u} : CTree E B X → List (Label E) → CTree E B X → Prop
  | nil (t : CTree E B X) : FiniteSteps t [] t
  | cons {t u v : CTree E B X} {l : Label E} {labels : List (Label E)} :
      trans l t u → FiniteSteps u labels v → FiniteSteps t (l :: labels) v

/-- The labels of one turn: a silent step followed by the turn's logs. -/
def turn_labels (logs : List W) : List (Label (writerE W)) :=
  .tau :: logs.map fun o => .obs (E := writerE W) o ⟨⟩

theorem turn_labels_nonempty (logs : List W) : turn_labels logs ≠ [] := nofun

theorem label_logs_turn_labels (logs : List W) : label_logs (turn_labels logs) = logs := by
  induction logs with
  | nil => rfl
  | cons o logs ih => simpa [turn_labels, label_logs] using ih

theorem label_taus_turn_labels (logs : List W) : label_taus (turn_labels logs) = 1 := by
  induction logs with
  | nil => rfl
  | cons o logs ih => simp [turn_labels, label_taus]

theorem finite_steps_app {t u v : CTree E B X} {left right : List (Label E)}
    (h₁ : FiniteSteps t left u) (h₂ : FiniteSteps u right v) : FiniteSteps t (left ++ right) v := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

theorem finite_steps_sbisim {t t' : CTree E B X} {labels : List (Label E)}
    (h : FiniteSteps t labels t') : ∀ u : CTree E B X, t ~ u →
      ∃ u', FiniteSteps u labels u' ∧ t' ~ u' := by
  induction h with
  | nil t => exact fun u he => ⟨u, .nil u, he⟩
  | cons hs _ ih =>
    intro u he
    obtain ⟨_, mid', hs', hmid, rfl⟩ := (sbisim_unfold.1 he).1 _ _ hs
    obtain ⟨last', ht, hl⟩ := ih mid' hmid
    exact ⟨last', .cons hs' ht, hl⟩

theorem finite_steps_emit_list (logs : List W) (t : ctreeW W B X) :
    FiniteSteps (emit_list logs t) (logs.map fun o => .obs (E := writerE W) o ⟨⟩) t := by
  induction logs with
  | nil => exact .nil t
  | cons o logs ih =>
    refine .cons ?_ ih
    rw [emit_list_cons]
    exact trans_vis (E := writerE W) PUnit.unit _

/-- Observation-only prefixes: the residual is identified up to strong bisimulation, which absorbs
finite administrative guards. -/
def steps (t : ctreeW W B X) (logs : List W) (u : ctreeW W B X) : Prop :=
  ∃ residual, FiniteSteps t (logs.map fun o => .obs (E := writerE W) o ⟨⟩) residual ∧ residual ~ u

theorem steps_sbisim {t t' u : ctreeW W B X} {logs : List W} (he : t ~ t')
    (h : steps t logs u) : steps t' logs u := by
  obtain ⟨r, hs, hr⟩ := h
  obtain ⟨r', hs', hrr⟩ := finite_steps_sbisim hs t' he
  exact ⟨r', hs', sbisim_trans (sbisim_symm hrr) hr⟩

theorem steps_emit_list (logs : List W) (t : ctreeW W B X) : steps (emit_list logs t) logs t :=
  ⟨t, finite_steps_emit_list logs t, sbisim_refl t⟩

/-! ## Realizing an infinite sequence of finite label chunks

Each chunk must be nonempty: an empty chunk cannot witness progress of a stuck tree, so the
productivity of the realization is genuine. -/

/-- One round of `realizes`: chunk `k` is nonempty and leads to a tree realizing chunk `k+1`. -/
def realizesF (chunks : Nat → List (Label E)) : Mon (Rel Nat (CTree E B X)) where
  body R k t := ∃ next, chunks k ≠ [] ∧ FiniteSteps t (chunks k) next ∧ R (k + 1) next
  mono h _ _ := fun ⟨next, hne, hs, hR⟩ => ⟨next, hne, hs, h _ _ hR⟩

/-- `t` executes `chunks k`, `chunks (k+1)`, … forever (Rocq coinductive `realizes`). -/
def realizes (chunks : Nat → List (Label E)) : Rel Nat (CTree E B X) := gfp (realizesF chunks)

theorem realizes_unfold {chunks : Nat → List (Label E)} {k : Nat} {t : CTree E B X} :
    realizes chunks k t ↔
      ∃ next, chunks k ≠ [] ∧ FiniteSteps t (chunks k) next ∧ realizes chunks (k + 1) next :=
  ⟨fun h => gfp_pfp (b := realizesF chunks) k t h,
   fun h => b_chain (gfp_chain (realizesF chunks)) k t h⟩

/-- The Rocq constructor `realizes_next`. -/
theorem realizes_next {chunks : Nat → List (Label E)} {k : Nat} {t : CTree E B X}
    (next : CTree E B X) (hne : chunks k ≠ []) (hs : FiniteSteps t (chunks k) next)
    (h : realizes chunks (k + 1) next) : realizes chunks k t :=
  realizes_unfold.2 ⟨next, hne, hs, h⟩

/-- Coinduction principle for `realizes` (Rocq `cofix`). -/
theorem realizes_coind {chunks : Nat → List (Label E)} (P : Nat → CTree E B X → Prop)
    (h : ∀ k t, P k t → ∃ next, chunks k ≠ [] ∧ FiniteSteps t (chunks k) next ∧ P (k + 1) next)
    {k : Nat} {t : CTree E B X} (hP : P k t) : realizes chunks k t :=
  le_gfp (b := realizesF chunks) (x := P) h k t hP

theorem realizes_sbisim {chunks : Nat → List (Label E)} {k : Nat} {t u : CTree E B X}
    (he : t ~ u) (h : realizes chunks k t) : realizes chunks k u := by
  refine realizes_coind (fun k u => ∃ t, t ~ u ∧ realizes chunks k t) ?_ ⟨t, he, h⟩
  rintro k u ⟨t, he, h⟩
  obtain ⟨next, hne, hs, hn⟩ := realizes_unfold.1 h
  obtain ⟨next', hs', hn'⟩ := finite_steps_sbisim hs u he
  exact ⟨next', hne, hs', next, hn', hn⟩

/-- Initialization extends chunk zero without changing later turn indices. -/
def prepend_chunk (pre : List (Label E)) (chunks : Nat → List (Label E)) : Nat → List (Label E)
  | 0 => pre ++ chunks 0
  | j + 1 => chunks (j + 1)

theorem realizes_prepend_succ (pre : List (Label E)) (chunks : Nat → List (Label E)) (k : Nat)
    (t : CTree E B X) (h : realizes chunks (k + 1) t) :
    realizes (prepend_chunk pre chunks) (k + 1) t := by
  refine realizes_coind (fun k t => ∃ j, k = j + 1 ∧ realizes chunks k t) ?_ ⟨k, rfl, h⟩
  rintro _ t ⟨j, rfl, h⟩
  obtain ⟨next, hne, hs, hn⟩ := realizes_unfold.1 h
  exact ⟨next, hne, hs, j + 1, rfl, hn⟩

theorem realizes_emit_list_prefix (init : List W) (chunks : Nat → List (Label (writerE W)))
    (t : ctreeW W B X) (h : realizes chunks 0 t) :
    realizes (prepend_chunk (init.map fun o => .obs (E := writerE W) o ⟨⟩) chunks) 0
      (emit_list init t) := by
  obtain ⟨next, hne, hs, hn⟩ := realizes_unfold.1 h
  refine realizes_next next ?_ (finite_steps_app (finite_steps_emit_list init t) hs)
    (realizes_prepend_succ _ _ 0 next hn)
  simp only [prepend_chunk, ne_eq, List.append_eq_nil_iff, not_and]
  exact fun _ => hne

/-- Any tree bisimilar to a root of a chunked sequence realizes its suffix. -/
theorem realizes_from_steps (chunks : Nat → List (Label E)) (roots : Nat → CTree E B X)
    (hne : ∀ k, chunks k ≠ [])
    (hstep : ∀ k, ∃ next, FiniteSteps (roots k) (chunks k) next ∧ next ~ roots (k + 1)) :
    ∀ k (t : CTree E B X), t ~ roots k → realizes chunks k t := by
  intro k t he
  refine realizes_coind (fun k t => t ~ roots k) ?_ he
  intro k t he
  obtain ⟨next, hs, hn⟩ := hstep k
  obtain ⟨next', hs', hn'⟩ := finite_steps_sbisim hs t (sbisim_symm he)
  exact ⟨next', hne k, hs', sbisim_trans (sbisim_symm hn') hn⟩

/-! ## Guard/log alignment and finite prefixes -/

/-- `n` guards around `t` (the writer instance of `guards`). -/
abbrev rr_guards (n : Nat) (t : ctreeW W B X) : ctreeW W B X := guards n t

theorem rr_guards_trans (n : Nat) {l : Label (writerE W)} {t u : ctreeW W B X} (h : trans l t u) :
    trans l (rr_guards n t) u := by
  induction n with
  | zero => exact h
  | succ n ih => exact trans_guard ih

/-- One round of `rr_aligned`: consume a nonempty guard block on both sides, or matching logs
after finite guard blocks. -/
inductive RrAlignF (R : Rel (ctreeW W B X) (ctreeW W B X)) : Rel (ctreeW W B X) (ctreeW W B X)
  | guard {t u : ctreeW W B X} (n m : Nat) (t' u' : ctreeW W B X) :
      t = rr_guards (n + 1) t' → u = rr_guards (m + 1) u' → R t' u' → RrAlignF R t u
  | log {t u : ctreeW W B X} (n m : Nat) (o : W) (t' u' : ctreeW W B X) :
      t = rr_guards n (.vis (E := writerE W) o fun _ => t') →
      u = rr_guards m (.vis (E := writerE W) o fun _ => u') → R t' u' → RrAlignF R t u

/-- The functor of `rr_aligned`. -/
def rr_alignF : Mon (Rel (ctreeW W B X) (ctreeW W B X)) where
  body := RrAlignF
  mono h _ _
    | .guard n m t' u' ht hu hR => .guard n m t' u' ht hu (h _ _ hR)
    | .log n m o t' u' ht hu hR => .log n m o t' u' ht hu (h _ _ hR)

/-- Guard/log alignment: a silent round consumes a guard on both sides, so finite prefixes cannot
turn silent divergence into a visible event (Rocq coinductive `rr_aligned`). -/
def rr_aligned : Rel (ctreeW W B X) (ctreeW W B X) := gfp (rr_alignF (W := W) (B := B) (X := X))

theorem rr_aligned_unfold {t u : ctreeW W B X} : rr_aligned t u ↔ RrAlignF rr_aligned t u :=
  ⟨fun h => gfp_pfp (b := rr_alignF) t u h, fun h => b_chain (gfp_chain rr_alignF) t u h⟩

/-- Coinduction principle for `rr_aligned` (Rocq `cofix`). -/
theorem rr_aligned_coind (R : Rel (ctreeW W B X) (ctreeW W B X))
    (h : ∀ t u, R t u → RrAlignF R t u) {t u : ctreeW W B X} (hR : R t u) : rr_aligned t u :=
  le_gfp (b := rr_alignF) (x := R) h t u hR

/-- The Rocq constructor `rr_align_guard`. -/
theorem rr_align_guard {t u : ctreeW W B X} (n m : Nat) (t' u' : ctreeW W B X)
    (ht : t = rr_guards (n + 1) t') (hu : u = rr_guards (m + 1) u') (h : rr_aligned t' u') :
    rr_aligned t u :=
  rr_aligned_unfold.2 (.guard n m t' u' ht hu h)

/-- The Rocq constructor `rr_align_log`. -/
theorem rr_align_log {t u : ctreeW W B X} (n m : Nat) (o : W) (t' u' : ctreeW W B X)
    (ht : t = rr_guards n (.vis (E := writerE W) o fun _ => t'))
    (hu : u = rr_guards m (.vis (E := writerE W) o fun _ => u')) (h : rr_aligned t' u') :
    rr_aligned t u :=
  rr_aligned_unfold.2 (.log n m o t' u' ht hu h)

theorem rr_aligned_equ {t u a b : ctreeW W B X} (ht : t = a) (hu : u = b) (h : rr_aligned t u) :
    rr_aligned a b :=
  ht ▸ hu ▸ h

theorem rr_aligned_sym {t u : ctreeW W B X} (h : rr_aligned t u) : rr_aligned u t := by
  refine rr_aligned_coind (fun u t => rr_aligned t u) ?_ h
  intro u t h
  match rr_aligned_unfold.1 h with
  | .guard n m t' u' ht hu h => exact .guard m n u' t' hu ht h
  | .log n m o t' u' ht hu h => exact .log m n o u' t' hu ht h

/-- An aligned tree is a stack of guards over a guard or a log, so neither `br`, `step` nor `ret`
can appear at its head. Rocq's `go T` is a tree `t` with `t.unfold = T`. -/
theorem rr_aligned_match {l : Label (writerE W)} {T : CTreeF (writerE W) B X (ctreeW W B X)}
    {next : ctreeW W B X} (tr : Trans_ l T next) :
    ∀ t u, t.unfold = T → rr_aligned t u → ∃ u', trans l u u' ∧ rr_aligned next u' := by
  induction tr with
  | br x _ _ =>
    intro t u ht h
    cases rr_aligned_unfold.1 h with
    | guard n m t' u' e _ _ => subst e; simp at ht
    | log n m o t' u' e _ _ => subst e; cases n <;> simp at ht
  | @guard t0 _ _ _ ih =>
    intro t u ht h
    cases rr_aligned_unfold.1 h with
    | guard n m t' u' et eu ha =>
      subst et eu
      simp only [guards_succ, unfold_guard, CTreeF.guard.injEq] at ht
      subst ht
      cases n with
      | zero =>
        obtain ⟨v, hv, hn⟩ := ih t' u' rfl ha
        exact ⟨v, rr_guards_trans (m + 1) hv, hn⟩
      | succ n => exact ih _ _ rfl (rr_align_guard n m t' u' rfl rfl ha)
    | log n m o t' u' et eu ha =>
      subst et eu
      cases n with
      | zero => simp at ht
      | succ n =>
        simp only [guards_succ, unfold_guard, CTreeF.guard.injEq] at ht
        subst ht
        exact ih _ _ rfl (rr_align_log n m o t' u' rfl rfl ha)
  | step =>
    intro t u ht h
    cases rr_aligned_unfold.1 h with
    | guard n m t' u' e _ _ => subst e; simp at ht
    | log n m o t' u' e _ _ => subst e; cases n <;> simp at ht
  | @obs e k x =>
    intro t u ht h
    cases rr_aligned_unfold.1 h with
    | guard n m t' u' et _ _ => subst et; simp at ht
    | log n m o t' u' et eu ha =>
      subst et eu
      cases n with
      | succ n => simp at ht
      | zero =>
        simp only [guards_zero, unfold_vis] at ht
        cases ht
        exact ⟨u', rr_guards_trans m (trans_vis (E := writerE W) x _), ha⟩
  | val =>
    intro t u ht h
    cases rr_aligned_unfold.1 h with
    | guard n m t' u' e _ _ => subst e; simp at ht
    | log n m o t' u' e _ _ => subst e; cases n <;> simp at ht

theorem rr_aligned_trans {t u next : ctreeW W B X} {l : Label (writerE W)} (h : rr_aligned t u)
    (tr : trans l t next) : ∃ other, trans l u other ∧ rr_aligned next other :=
  rr_aligned_match tr t u rfl h

theorem rr_aligned_sbisim {t u : ctreeW W B X} (h : rr_aligned t u) : t ~ u := by
  refine le_gfp (b := sb Eq) (x := rr_aligned) (fun t u h => ⟨?_, ?_⟩) t u h
  · intro l next tr
    obtain ⟨other, tr', ha⟩ := rr_aligned_trans h tr
    exact ⟨l, other, tr', ha, rfl⟩
  · intro l next tr
    obtain ⟨other, tr', ha⟩ := rr_aligned_trans (rr_aligned_sym h) tr
    exact ⟨l, other, tr', rr_aligned_sym ha, rfl⟩

theorem rr_guards_equ (n : Nat) {t u : ctreeW W B X} (h : t = u) :
    rr_guards n t = rr_guards n u :=
  h ▸ rfl

theorem rr_guards_add (n m : Nat) (t : ctreeW W B X) :
    rr_guards (n + m) t = rr_guards n (rr_guards m t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_right_comm]; simp [ih]

theorem rr_guards_guard (n : Nat) (t : ctreeW W B X) :
    rr_guards n (.guard t) = rr_guards (n + 1) t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rr_guards, guards_succ] at ih ⊢; rw [ih]

/-- A finite proof prefix, not an additional evaluator or scheduler (Rocq `rr_token`). -/
inductive RRToken (W : Type u)
  | guard
  | log (o : W)

/-- Interpret tokens as guard or log nodes. -/
def rr_prefix : List (RRToken W) → ctreeW W B X → ctreeW W B X
  | [], t => t
  | .guard :: rest, t => .guard (rr_prefix rest t)
  | .log o :: rest, t => .vis (E := writerE W) o fun _ => rr_prefix rest t

/-- The logged payloads of a token word. -/
def rr_prefix_events : List (RRToken W) → List W
  | [] => []
  | .guard :: rest => rr_prefix_events rest
  | .log o :: rest => o :: rr_prefix_events rest

theorem rr_prefix_app (left right : List (RRToken W)) (t : ctreeW W B X) :
    rr_prefix (left ++ right) t = rr_prefix left (rr_prefix right t) := by
  induction left with
  | nil => rfl
  | cons tk rest ih => cases tk <;> simp [rr_prefix, ih]

theorem rr_prefix_equ (word : List (RRToken W)) {t u : ctreeW W B X} (h : t = u) :
    rr_prefix word t = rr_prefix word u :=
  h ▸ rfl

theorem rr_prefix_events_app (left right : List (RRToken W)) :
    rr_prefix_events (left ++ right) = rr_prefix_events left ++ rr_prefix_events right := by
  induction left with
  | nil => rfl
  | cons tk rest ih => cases tk <;> simp [rr_prefix_events, ih]

theorem rr_prefix_events_logs (logs : List W) : rr_prefix_events (logs.map .log) = logs := by
  induction logs with
  | nil => rfl
  | cons o logs ih => simp [rr_prefix_events, ih]

theorem rr_prefix_emit (logs : List W) (t : ctreeW W B X) :
    rr_prefix (logs.map .log) t = emit_list logs t := by
  induction logs with
  | nil => rfl
  | cons o rest ih => simp [rr_prefix, ih]

theorem rr_prefix_emit_sbisim (word : List (RRToken W)) (t : ctreeW W B X) :
    rr_prefix word t ~ emit_list (rr_prefix_events word) t := by
  induction word with
  | nil => exact sbisim_refl t
  | cons tk rest ih =>
    cases tk with
    | guard => exact sb_guard_l ih
    | log o => simpa [rr_prefix, rr_prefix_events] using sb_vis (E := writerE W) o fun _ => ih

/-! ## Repeating finite observation batches

Each round emits the finite batch of its index and advances the index. Batches may be empty, but
an empty batch cannot satisfy the productivity premise of `emit_batches_bisim`. -/

/-- The batch loop: round `j` logs `batch j` and continues with `next j`. -/
def emit_batches (batch : I → List W) (next : I → I) (i : I) : ctreeW W B X :=
  CTree.iter (fun j => emit_list (batch j) (pure (Sum.inl (next j)))) i

/-- The raw unfolding: the administrative guard of `iter` is retained. -/
theorem emit_batches_unfold (batch : I → List W) (next : I → I) (i : I) :
    (emit_batches batch next i : ctreeW W B X) =
      emit_list (batch i) (.guard (emit_batches batch next (next i))) := by
  rw [emit_batches, unfold_iter, emit_list_ret_bind]
  rfl

/-- The same unfolding after absorbing the administrative guard. -/
theorem emit_batches_unfold_sbisim (batch : I → List W) (next : I → I) (i : I) :
    (emit_batches batch next i : ctreeW W B X) ~
      emit_list (batch i) (emit_batches batch next (next i) : ctreeW W B X) := by
  rw [emit_batches_unfold]
  exact emit_list_sbisim _ (sb_guard _)

/-- A root family that emits its own batch each round is the batch loop. The nonempty-batch
premise is essential: silent self-equations alone do not justify this coinduction. -/
theorem emit_batches_bisim (batch : I → List W) (next : I → I) (Inv : I → Prop)
    (root : I → ctreeW W B X) (hnext : ∀ i, Inv i → Inv (next i))
    (hnonempty : ∀ i, Inv i → batch i ≠ [])
    (hroot : ∀ i, Inv i → root i ~ emit_list (batch i) (root (next i))) :
    ∀ i, Inv i → root i ~ (emit_batches batch next i : ctreeW W B X) := by
  intro i hi
  refine coinduction (b := sb Eq) (ι := {i // Inv i}) (fun i => root i.1)
    (fun i => emit_batches batch next i.1) ?_ ⟨i, hi⟩
  rintro R hR cih ⟨i, hi⟩
  refine sbisim_clos_sb (.step hR) _ _ (emit_list (batch i) (emit_batches batch next (next i)))
    _ (hroot i hi) ?_ (sbisim_symm (emit_batches_unfold_sbisim batch next i))
  match hb : batch i, hnonempty i hi with
  | o :: rest, _ =>
    simp only [emit_list_cons]
    exact step_sb_vis_id_gen (E := writerE W) o _ _ fun _ =>
      ⟨emit_list_chain hR rest (cih ⟨next i, hnext i hi⟩), rfl⟩

theorem emit_batches_prefix_sbisim (batch : I → List W) (next : I → I) (n : Nat) (i : I) :
    (emit_batches batch next i : ctreeW W B X) ~
      emit_list ((List.range' 0 n).flatMap fun j => batch (Nat.repeat next j i))
        (emit_batches batch next (Nat.repeat next n i) : ctreeW W B X) := by
  induction n with
  | zero => exact sbisim_refl _
  | succ n ih =>
    rw [List.range'_concat, List.flatMap_append, emit_list_app]
    refine sbisim_trans ih (emit_list_sbisim _ ?_)
    simpa [Nat.repeat] using
      emit_batches_unfold_sbisim (B := B) (X := X) batch next (Nat.repeat next n i)

theorem emit_batches_prefix (batch : I → List W) (next : I → I) (n : Nat) (i : I) :
    steps (emit_batches batch next i : ctreeW W B X)
      ((List.range' 0 n).flatMap fun j => batch (Nat.repeat next j i))
      (emit_batches batch next (Nat.repeat next n i) : ctreeW W B X) :=
  steps_sbisim (sbisim_symm (emit_batches_prefix_sbisim batch next n i)) (steps_emit_list _ _)

/-- Identical bodies followed by scheduler steps yield bisimilar families; the index retains every
state component used by either run. -/
theorem sbisim_step_family (left right : I → CTree E B X) (body : I → CTree E B A)
    (next : I → A → I) (Inv : I → Prop)
    (hleft : ∀ i, Inv i → left i ~ (body i >>= fun a => .step (left (next i a))))
    (hright : ∀ i, Inv i → right i ~ (body i >>= fun a => .step (right (next i a))))
    (hnext : ∀ i a, Inv i → Inv (next i a)) :
    ∀ i, Inv i → left i ~ right i := by
  intro i hi
  refine coinduction (b := sb Eq) (ι := {i // Inv i}) (fun i => left i.1) (fun i => right i.1)
    ?_ ⟨i, hi⟩
  rintro R hR cih ⟨i, hi⟩
  refine sbisim_clos_sb (.step hR) _ _ _ _ (hleft i hi) ?_ (sbisim_symm (hright i hi))
  exact sb_chain_bind_eq (.step hR) (body i) fun a =>
    step_sb_step_gen rfl (cih ⟨next i a, hnext i a hi⟩)

/-- Identical bodies and logged scheduler picks yield bisimilar families. -/
theorem sbisim_log_family (left right : I → ctreeW W B X) (body : I → ctreeW W B A)
    (pick : I → W) (next : I → A → I) (Inv : I → Prop)
    (hleft : ∀ i, Inv i →
      left i ~ (body i >>= fun a => .vis (E := writerE W) (pick i) fun _ => left (next i a)))
    (hright : ∀ i, Inv i →
      right i ~ (body i >>= fun a => .vis (E := writerE W) (pick i) fun _ => right (next i a)))
    (hnext : ∀ i a, Inv i → Inv (next i a)) :
    ∀ i, Inv i → left i ~ right i := by
  intro i hi
  refine coinduction (b := sb Eq) (ι := {i // Inv i}) (fun i => left i.1) (fun i => right i.1)
    ?_ ⟨i, hi⟩
  rintro R hR cih ⟨i, hi⟩
  refine sbisim_clos_sb (.step hR) _ _ _ _ (hleft i hi) ?_ (sbisim_symm (hright i hi))
  exact sb_chain_bind_eq (.step hR) (body i) fun a =>
    step_sb_vis_id_gen (E := writerE W) (pick i) _ _ fun _ => ⟨cih ⟨next i a, hnext i a hi⟩, rfl⟩

-- Not ported: nothing (every Rocq declaration has a Lean counterpart; `≅` lemmas such as
-- `emit_list_equ`, `rr_guards_equ`, `rr_prefix_equ`, `rr_aligned_equ` are kept as `=` lemmas).

end Tisl
