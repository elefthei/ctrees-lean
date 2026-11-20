/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.Owned

/-!
# Owned action machine: guarded heads and projection onto one lineage

Characterisation of `focus_step` once the focused thread is known up to guards; ordered slot
views of the vector pool and their behaviour under replacement, removal and fork; the projection
of the owned machine onto one lineage: own actions are local actions of the projection
(`owned_step_own`), foreign actions leave it unchanged up to `owned_equ` (`owned_step_foreign`),
and `weak_next` is sound and conditionally complete for the projected clock
(← `CTree/Interp/CSL/Owned.v`, lines 969-2003).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield
open ITree (Effect)

/-! ## Heads of a focused slot -/

/-- A head that is not itself a guard. -/
def unguarded (u : Thread sE Bn) : Prop := ∀ w, u ≠ .guard w

/-- Finite guard prefixes before unguarded heads are unique. -/
theorem guards_unique (m m' : Nat) (u u' : Thread sE Bn) :
    guards m u = guards m' u' → unguarded u → unguarded u' → u = u' := by
  intro h hu hu'
  rcases guards_cancel _ _ _ _ h with ⟨d, hd, -⟩ | ⟨d, hd, -⟩
  · cases d with
    | zero => exact hd
    | succ d => exact absurd hd (hu _)
  · cases d with
    | zero => exact hd.symm
    | succ d => exact absurd hd (hu' _)

theorem headed_unique (t u u' : Thread sE Bn) :
    headed t u → headed t u' → unguarded u → unguarded u' → u = u' := by
  rintro ⟨m, h⟩ ⟨m', h'⟩
  exact guards_unique m m' u u' (h.symm.trans h')

/-- Every head of a `focus_step` disjunct is unguarded. -/
local macro "unguarded_tac" : tactic => `(tactic| exact fun _ h => by simp at h)

/-- Two distinct non-guard heads are never equal. -/
local macro "clash" h:ident : tactic =>
  `(tactic| (have hc := congrArg CTree.unfold $h; simp at hc <;>
    (obtain ⟨h1, -⟩ := hc; injection h1 with h1; injection h1)))

/-- Shared forward direction: the head the focused slot exposes is `u0`. -/
private theorem focus_step_heads {c : OwnedCfg} {n : Nat} {v : Pool sE Bn (n + 1)}
    {g : Vector Side (n + 1)} {j : Fin (n + 1)} {a : OwnedAction} {c' : OwnedCfg}
    {u0 : Thread sE Bn} (H0 : headed v[j] u0) (hu0 : unguarded u0)
    (H : focus_step c n v g j a c') :
    (∃ t, u0 = .step t ∧ a = act g[j] .step ∧
      c' = set_pool c (mk_pool (n + 1) (v.set j t) g (some j))) ∨
    (∃ k : PUnit → Thread sE Bn, u0 = .vis (E := CEff) (.inl ⟨⟩) k ∧
      a = act g[j] .yield ∧ c' = set_pool c (mk_pool (n + 1) (v.set j (k ⟨⟩)) g none)) ∨
    (∃ k : Bool → Thread sE Bn, u0 = .vis (E := CEff) (.inr (.inl ⟨⟩)) k ∧
      a = act g[j] .fork ∧
      c' = set_pool c (mk_pool (n + 2) (Vector.cons (k true) (v.set j (k false)))
        (Vector.cons g[j] g) (some j.succ))) ∨
    (u0 = pure ⟨⟩ ∧ a = act g[j] .ret ∧
      c' = set_pool c (mk_pool n (vector_remove v j) (vector_remove g j) none)) ∨
    (∃ (e : sE.I) (k : sE.O e → Thread sE Bn) (kind : OwnedKind) (y : sE.O e) (c1 : OwnedCfg),
      u0 = .vis (E := CEff) (.inr (.inr e)) k ∧
      prim_step g[j] c e = some (kind, y, c1) ∧ a = act g[j] kind ∧
      c' = set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j))) := by
  rcases H with ⟨t, Hh, Ha, Hc⟩ | ⟨k, Hh, Ha, Hc⟩ | ⟨k, Hh, Ha, Hc⟩ | ⟨Hh, Ha, Hc⟩ |
    ⟨e, k, kind, y, c1, Hh, Hs, Ha, Hc⟩
  · exact .inl ⟨t, headed_unique _ _ _ H0 Hh hu0 (by unguarded_tac), Ha, Hc⟩
  · exact .inr (.inl ⟨k, headed_unique _ _ _ H0 Hh hu0 (by unguarded_tac), Ha, Hc⟩)
  · exact .inr (.inr (.inl ⟨k, headed_unique _ _ _ H0 Hh hu0 (by unguarded_tac), Ha, Hc⟩))
  · exact .inr (.inr (.inr (.inl ⟨headed_unique _ _ _ H0 Hh hu0 (by unguarded_tac), Ha, Hc⟩)))
  · exact .inr (.inr (.inr (.inr
      ⟨e, k, kind, y, c1, headed_unique _ _ _ H0 Hh hu0 (by unguarded_tac), Hs, Ha, Hc⟩)))

theorem focus_step_head_step (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (t0 : Thread sE Bn) (m : Nat) (a : OwnedAction)
    (c' : OwnedCfg) (hv : v[j] = guards m (.step t0)) :
    focus_step c n v g j a c' ↔
      ∃ t, t = t0 ∧ a = act g[j] .step ∧
        c' = set_pool c (mk_pool (n + 1) (v.set j t) g (some j)) := by
  constructor
  · intro H
    rcases focus_step_heads ⟨m, hv⟩ (by unguarded_tac) H with ⟨t, Hu, Ha, Hc⟩ | ⟨k, Hu, -⟩ |
      ⟨k, Hu, -⟩ | ⟨Hu, -⟩ | ⟨e, k, kind, y, c1, Hu, -⟩
    · exact ⟨t, (step_eq_step_iff.1 Hu).symm, Ha, Hc⟩
    all_goals clash Hu
  · rintro ⟨t, rfl, rfl, rfl⟩
    exact .inl ⟨t, ⟨m, hv⟩, rfl, rfl⟩

theorem focus_step_head_yield (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (k0 : PUnit → Thread sE Bn) (m : Nat)
    (a : OwnedAction) (c' : OwnedCfg) (hv : v[j] = guards m (.vis (E := CEff) (.inl ⟨⟩) k0)) :
    focus_step c n v g j a c' ↔
      ∃ k : PUnit → Thread sE Bn, (∀ x, k x = k0 x) ∧ a = act g[j] .yield ∧
        c' = set_pool c (mk_pool (n + 1) (v.set j (k ⟨⟩)) g none) := by
  constructor
  · intro H
    rcases focus_step_heads ⟨m, hv⟩ (by unguarded_tac) H with ⟨t, Hu, -⟩ | ⟨k, Hu, Ha, Hc⟩ |
      ⟨k, Hu, -⟩ | ⟨Hu, -⟩ | ⟨e, k, kind, y, c1, Hu, -⟩
    · clash Hu
    · exact ⟨k, fun x => congrFun (vis_eq_vis_iff.1 Hu).symm x, Ha, Hc⟩
    all_goals clash Hu
  · rintro ⟨k, hk, rfl, rfl⟩
    refine .inr (.inl ⟨k, ⟨m, ?_⟩, rfl, rfl⟩)
    rw [hv, show k = k0 from funext hk]

theorem focus_step_head_fork (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (k0 : Bool → Thread sE Bn) (m : Nat)
    (a : OwnedAction) (c' : OwnedCfg)
    (hv : v[j] = guards m (.vis (E := CEff) (.inr (.inl ⟨⟩)) k0)) :
    focus_step c n v g j a c' ↔
      ∃ k : Bool → Thread sE Bn, (∀ x, k x = k0 x) ∧ a = act g[j] .fork ∧
        c' = set_pool c (mk_pool (n + 2) (Vector.cons (k true) (v.set j (k false)))
          (Vector.cons g[j] g) (some j.succ)) := by
  constructor
  · intro H
    rcases focus_step_heads ⟨m, hv⟩ (by unguarded_tac) H with ⟨t, Hu, -⟩ | ⟨k, Hu, -⟩ |
      ⟨k, Hu, Ha, Hc⟩ | ⟨Hu, -⟩ | ⟨e, k, kind, y, c1, Hu, -⟩
    · clash Hu
    · clash Hu
    · exact ⟨k, fun x => congrFun (vis_eq_vis_iff.1 Hu).symm x, Ha, Hc⟩
    all_goals clash Hu
  · rintro ⟨k, hk, rfl, rfl⟩
    refine .inr (.inr (.inl ⟨k, ⟨m, ?_⟩, rfl, rfl⟩))
    rw [hv, show k = k0 from funext hk]

theorem focus_step_head_ret (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (m : Nat) (a : OwnedAction) (c' : OwnedCfg)
    (hv : v[j] = guards m (pure ⟨⟩)) :
    focus_step c n v g j a c' ↔
      a = act g[j] .ret ∧
        c' = set_pool c (mk_pool n (vector_remove v j) (vector_remove g j) none) := by
  constructor
  · intro H
    rcases focus_step_heads ⟨m, hv⟩ (by unguarded_tac) H with ⟨t, Hu, -⟩ | ⟨k, Hu, -⟩ |
      ⟨k, Hu, -⟩ | ⟨-, Ha, Hc⟩ | ⟨e, k, kind, y, c1, Hu, -⟩
    · clash Hu
    · clash Hu
    · clash Hu
    · exact ⟨Ha, Hc⟩
    · clash Hu
  · rintro ⟨rfl, rfl⟩
    exact .inr (.inr (.inr (.inl ⟨⟨m, hv⟩, rfl, rfl⟩)))

theorem focus_step_head_prim (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (e0 : sE.I) (k0 : sE.O e0 → Thread sE Bn)
    (m : Nat) (a : OwnedAction) (c' : OwnedCfg)
    (hv : v[j] = guards m (.vis (E := CEff) (.inr (.inr e0)) k0)) :
    focus_step c n v g j a c' ↔
      ∃ (k : sE.O e0 → Thread sE Bn) (kind : OwnedKind) (y : sE.O e0) (c1 : OwnedCfg),
        (∀ x, k x = k0 x) ∧ prim_step g[j] c e0 = some (kind, y, c1) ∧ a = act g[j] kind ∧
        c' = set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j)) := by
  constructor
  · intro H
    rcases focus_step_heads ⟨m, hv⟩ (by unguarded_tac) H with ⟨t, Hu, -⟩ | ⟨k, Hu, -⟩ |
      ⟨k, Hu, -⟩ | ⟨Hu, -⟩ | ⟨e, k, kind, y, c1, Hu, Hs, Ha, Hc⟩
    · clash Hu
    · clash Hu
    · clash Hu
    · clash Hu
    · have hu := congrArg CTree.unfold Hu
      simp only [unfold_vis, CTreeF.vis.injEq] at hu
      obtain ⟨h1, hk⟩ := hu
      injection h1 with h1; injection h1 with h1; subst h1
      cases hk
      exact ⟨_, kind, y, c1, fun _ => rfl, Hs, Ha, Hc⟩
  · rintro ⟨k, kind, y, c1, hk, Hs, rfl, rfl⟩
    refine .inr (.inr (.inr (.inr ⟨e0, k, kind, y, c1, ⟨m, ?_⟩, Hs, rfl, rfl⟩)))
    rw [hv, show k = k0 from funext hk]

theorem focus_step_head_stuck (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (m : Nat) (a : OwnedAction) (c' : OwnedCfg)
    (hv : v[j] = guards m .stuck) : ¬ focus_step c n v g j a c' := by
  intro H
  rcases focus_step_heads ⟨m, hv⟩ (by unguarded_tac) H with ⟨t, Hu, -⟩ | ⟨k, Hu, -⟩ |
    ⟨k, Hu, -⟩ | ⟨Hu, -⟩ | ⟨e, k, kind, y, c1, Hu, -⟩
  all_goals clash Hu

/-! ## Ordered slot views of the vector pool

Lists below are only extensional views; all updates and transitions use the original vectors
and finite indices. -/

def cfg_slots (c : OwnedCfg) : List (Thread sE Bn × Side) := tp_slots c.pool
def cfg_focus (c : OwnedCfg) : Option Nat := focus_nat c.pool

theorem fin_nat_FS {n : Nat} (j : Fin n) : fin_nat j.succ = fin_nat j + 1 := rfl

theorem fin_nat_of_nat {n k : Nat} (H : k < n) : fin_nat (⟨k, H⟩ : Fin n) = k := rfl

theorem fin_nat_injective {n : Nat} (j k : Fin n) : fin_nat j = fin_nat k → j = k := Fin.ext

theorem owned_by_other (i s : Side) (t : Thread sE Bn) : s ≠ i → owned_by i (t, s) = false := by
  intro h; cases i <;> cases s <;> simp_all [owned_by, side_eqb]

theorem owned_by_true (i : Side) (x : Thread sE Bn × Side) : owned_by i x = true → x.2 = i :=
  (side_eqb_spec _ _).1

theorem cfg_slots_project (i : Side) (c : OwnedCfg) :
    cfg_slots (project i c) = (cfg_slots c).filter (owned_by i) :=
  (tp_slots_project i c.pool).trans (proj_slots_filter i c.pool)

theorem pool_cut (p : TaggedPool) (j : Fin p.size) :
    ∃ pre post, tp_slots p = pre ++ (p.threads[j], p.tags[j]) :: post ∧ pre.length = fin_nat j :=
  list_cut _ _ _ (tp_slots_nth_error p j)

/-- Replacement in the vector is replacement in its slot view. -/
private theorem slots_set (n : Nat) (v : Pool sE Bn n) (g : Vector Side n) (j : Fin n)
    (t : Thread sE Bn) (f f' : Option (Fin n)) :
    tp_slots (mk_pool n (v.set j t) g f') = (tp_slots (mk_pool n v g f)).set j (t, g[j]) := by
  apply List.ext_getElem
  · simp [tp_slots, mk_pool]
  · intro k h1 h2
    simp only [tp_slots, mk_pool, List.getElem_zip, List.getElem_set, Vector.toList_set]
    split <;> simp_all

/-- Removal in the vector is removal in its slot view. -/
private theorem slots_erase (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (f : Option (Fin (n + 1))) (f' : Option (Fin n)) :
    tp_slots (mk_pool n (vector_remove v j) (vector_remove g j) f') =
      (tp_slots (mk_pool (n + 1) v g f)).eraseIdx j := by
  apply List.ext_getElem
  · simp [tp_slots, mk_pool, List.length_eraseIdx]
  · intro k h1 h2
    simp only [tp_slots, mk_pool, List.getElem_zip, List.getElem_eraseIdx, vector_remove,
      Vector.toList_eraseIdx]
    split <;> simp

/-- The only replacement/removal equations are equations of vector views. -/
theorem slots_replace_view (n : Nat) (v : Pool sE Bn n) (g : Vector Side n) (j : Fin n)
    (f f' : Option (Fin n)) (t : Thread sE Bn) (pre : List (Thread sE Bn × Side))
    (old : Thread sE Bn × Side) (post : List (Thread sE Bn × Side)) :
    tp_slots (mk_pool n v g f) = pre ++ old :: post → fin_nat j = pre.length →
    tp_slots (mk_pool n (v.set j t) g f') = pre ++ (t, old.2) :: post := by
  intro H Hlen
  have Hn := tp_slots_nth_error (mk_pool n v g f) j
  rw [H, Hlen] at Hn
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
    Option.some.injEq] at Hn
  rw [slots_set n v g j t f f', H, show (t, g[j]) = (t, old.2) by rw [Hn]; rfl]
  simp only [fin_nat] at Hlen
  rw [Hlen]
  simp

theorem slots_remove_view (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (f : Option (Fin (n + 1))) (f' : Option (Fin n))
    (pre : List (Thread sE Bn × Side)) (old : Thread sE Bn × Side)
    (post : List (Thread sE Bn × Side)) :
    tp_slots (mk_pool (n + 1) v g f) = pre ++ old :: post → fin_nat j = pre.length →
    tp_slots (mk_pool n (vector_remove v j) (vector_remove g j) f') = pre ++ post := by
  intro H Hlen
  rw [slots_erase n v g j f f', H]
  simp only [fin_nat] at Hlen
  rw [Hlen, List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

theorem slots_cons (n : Nat) (v : Pool sE Bn n) (g : Vector Side n) (x : Thread sE Bn) (s : Side)
    (f : Option (Fin (n + 1))) (f' : Option (Fin n)) :
    tp_slots (mk_pool (n + 1) (Vector.cons x v) (Vector.cons s g) f) =
      (x, s) :: tp_slots (mk_pool n v g f') := by
  simp [tp_slots, mk_pool, Vector.cons, Vector.toList]

private theorem pool_cut_mk (n : Nat) (v : Pool sE Bn n) (g : Vector Side n) (f : Option (Fin n))
    (j : Fin n) :
    ∃ pre post, tp_slots (mk_pool n v g f) = pre ++ (v[j], g[j]) :: post ∧ pre.length = fin_nat j :=
  pool_cut (mk_pool n v g f) j

private theorem project_pool_threads (i : Side) (p : TaggedPool)
    (r : Fin (project_pool i p).size) :
    (project_pool i p).threads[r] = ((proj_slots i p)[r.val]'r.isLt).1 := Vector.getElem_map ..

private theorem project_pool_tags (i : Side) (p : TaggedPool)
    (r : Fin (project_pool i p).size) :
    (project_pool i p).tags[r] = ((proj_slots i p)[r.val]'r.isLt).2 := Vector.getElem_map ..

/-- Every filtered rank has its original finite index, constructively. -/
theorem project_index (i : Side) (p : TaggedPool) (j : Fin p.size) (hj : p.tags[j] = i) :
    ∃ r : Fin (project_pool i p).size,
      fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ∧
      (project_pool i p).threads[r] = p.threads[j] ∧ (project_pool i p).tags[r] = i := by
  have Hr := nth_error_rank (owned_by i) _ _ _ (tp_slots_nth_error p j) (by simp [owned_by, hj])
  rw [← proj_slots_filter] at Hr
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 Hr
  refine ⟨⟨_, hlt⟩, rfl, ?_, ?_⟩
  · rw [project_pool_threads]; exact congrArg Prod.fst heq
  · rw [project_pool_tags]; exact (congrArg Prod.snd heq).trans hj

theorem project_index_inv (i : Side) (p : TaggedPool) (r : Fin (project_pool i p).size) :
    ∃ j : Fin p.size, p.tags[j] = i ∧
      fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ∧
      (project_pool i p).threads[r] = p.threads[j] ∧ (project_pool i p).tags[r] = i := by
  have Hr : (proj_slots i p)[fin_nat r]? =
      some ((project_pool i p).threads[r], (project_pool i p).tags[r]) := by
    rw [List.getElem?_eq_getElem (by exact r.isLt), project_pool_threads, project_pool_tags]
  rw [proj_slots_filter] at Hr
  obtain ⟨k, hk, ho, hrank⟩ := rank_inv _ _ _ _ Hr
  have hlt : k < p.size := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    simpa [tp_slots] using this
  have Hn := tp_slots_nth_error p ⟨k, hlt⟩
  rw [fin_nat, hk, Option.some.injEq, Prod.mk.injEq] at Hn
  have Ho := owned_by_true _ _ ho
  exact ⟨⟨k, hlt⟩, Hn.2 ▸ Ho, hrank.symm, Hn.1, Ho⟩

/-- The projected focus of an owned focus is its rank. -/
private theorem focus_nat_project_owned (i : Side) (p : TaggedPool) (j : Fin p.size)
    (hf : p.focus = some j) (hj : p.tags[j] = i) :
    focus_nat (project_pool i p) = some (rank (owned_by i) (tp_slots p) (fin_nat j)) := by
  simp only [Fin.getElem_fin] at hj
  simp [focus_nat, project_pool, proj_focus, hf, hj, rank]

theorem project_focus_owned (i : Side) (p : TaggedPool) (j : Fin p.size)
    (r : Fin (project_pool i p).size) :
    p.focus = some j → p.tags[j] = i →
    fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) →
    (project_pool i p).focus = some r := by
  intro hf hj hr
  have H := focus_nat_project_owned i p j hf hj
  rw [← hr, focus_nat] at H
  rcases hq : (project_pool i p).focus with _ | r'
  · simp [hq] at H
  · simp only [hq, Option.map_some, Option.some.injEq] at H
    exact congrArg some (Fin.ext H)

theorem project_focus_foreign (i : Side) (p : TaggedPool) (j : Fin p.size) :
    p.focus = some j → p.tags[j] ≠ i → (project_pool i p).focus = none := by
  intro hf hj
  simp only [Fin.getElem_fin] at hj
  simp [project_pool, proj_focus, hf, hj]

theorem project_focus_none (i : Side) (p : TaggedPool) :
    p.focus = none → (project_pool i p).focus = none := by
  intro hf
  simp [project_pool, proj_focus, hf]

theorem tp_equ_views (p q : TaggedPool) :
    tp_slots p = tp_slots q → focus_nat p = focus_nat q → tp_equ p q := by
  intro hs hf
  exact ⟨hs ▸ Forall2_slot_refl _, hf⟩

/-- The owned slot cut at `j` and its image in a filtered pool cut at its rank `r`. -/
private theorem cut_views (i : Side) (n m : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (w : Pool sE Bn m) (h : Vector Side m) (j : Fin n) (r : Fin m)
    (Hq : tp_slots (mk_pool m w h none) = (tp_slots (mk_pool n v g none)).filter (owned_by i))
    (Hj : g[j] = i)
    (Hr : fin_nat r = rank (owned_by i) (tp_slots (mk_pool n v g none)) (fin_nat j)) :
    ∃ pre post, tp_slots (mk_pool n v g none) = pre ++ (v[j], i) :: post ∧
      pre.length = fin_nat j ∧
      tp_slots (mk_pool m w h none) =
        pre.filter (owned_by i) ++ (v[j], i) :: post.filter (owned_by i) ∧
      fin_nat r = (pre.filter (owned_by i)).length := by
  obtain ⟨pre, post, Hc, Hlen⟩ := pool_cut_mk n v g none j
  rw [Hj] at Hc
  refine ⟨pre, post, Hc, Hlen, ?_, ?_⟩
  · rw [Hq, Hc, List.filter_append, List.filter_cons_of_pos (owned_by_self i _)]
  · rw [Hr, rank, Hc, ← Hlen, firstn_cut]

/-- Filtering commutes with replacement: the selected projected index is its finite ordered
rank, not a second scheduler slot. -/
theorem project_replace_equ (i : Side) (n m : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (w : Pool sE Bn m) (h : Vector Side m) (j : Fin n) (r : Fin m) (t : Thread sE Bn)
    (focused : Bool) :
    tp_slots (mk_pool m w h none) = (tp_slots (mk_pool n v g none)).filter (owned_by i) →
    g[j] = i → fin_nat r = rank (owned_by i) (tp_slots (mk_pool n v g none)) (fin_nat j) →
    tp_equ
      (project_pool i (mk_pool n (v.set j t) g (if focused then some j else none)))
      (mk_pool m (w.set r t) h (if focused then some r else none)) := by
  intro Hq Hj Hr
  obtain ⟨pre, post, Hc, Hlen, Hqc, Hr'⟩ := cut_views i n m v g w h j r Hq Hj Hr
  have Hu := slots_replace_view n v g j none (if focused then some j else none) t pre _ post Hc
    Hlen.symm
  have Hu' := slots_replace_view m w h r none (if focused then some r else none) t _ _ _ Hqc Hr'
  refine tp_equ_views _ _ ?_ ?_
  · rw [tp_slots_project, proj_slots_filter, Hu, Hu', List.filter_append,
      List.filter_cons_of_pos (owned_by_self i _)]
  · cases focused
    · simp [focus_nat, project_pool, proj_focus, mk_pool]
    · rw [focus_nat_project_owned i _ j rfl Hj, Hu]
      simp only [focus_nat, mk_pool, ite_true, Option.map_some, Hr', rank, ← Hlen]
      rw [firstn_cut]

theorem project_remove_equ (i : Side) (n m : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (w : Pool sE Bn (m + 1)) (h : Vector Side (m + 1))
    (j : Fin (n + 1)) (r : Fin (m + 1)) :
    tp_slots (mk_pool (m + 1) w h none) =
      (tp_slots (mk_pool (n + 1) v g none)).filter (owned_by i) →
    g[j] = i →
    fin_nat r = rank (owned_by i) (tp_slots (mk_pool (n + 1) v g none)) (fin_nat j) →
    tp_equ (project_pool i (mk_pool n (vector_remove v j) (vector_remove g j) none))
      (mk_pool m (vector_remove w r) (vector_remove h r) none) := by
  intro Hq Hj Hr
  obtain ⟨pre, post, Hc, Hlen, Hqc, Hr'⟩ := cut_views i _ _ v g w h j r Hq Hj Hr
  refine tp_equ_views _ _ ?_ (by simp [focus_nat, project_pool, proj_focus, mk_pool])
  rw [tp_slots_project, proj_slots_filter, slots_remove_view n v g j none none pre _ post Hc
    Hlen.symm, slots_remove_view m w h r none none _ _ _ Hqc Hr', List.filter_append]

theorem project_fork_equ (i : Side) (n m : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (w : Pool sE Bn (m + 1)) (h : Vector Side (m + 1))
    (j : Fin (n + 1)) (r : Fin (m + 1)) (x y : Thread sE Bn) :
    tp_slots (mk_pool (m + 1) w h none) =
      (tp_slots (mk_pool (n + 1) v g none)).filter (owned_by i) →
    g[j] = i → h[r] = i →
    fin_nat r = rank (owned_by i) (tp_slots (mk_pool (n + 1) v g none)) (fin_nat j) →
    tp_equ
      (project_pool i (mk_pool (n + 2) (Vector.cons x (v.set j y)) (Vector.cons g[j] g)
        (some j.succ)))
      (mk_pool (m + 2) (Vector.cons x (w.set r y)) (Vector.cons h[r] h) (some r.succ)) := by
  intro Hq Hj Hh Hr
  obtain ⟨pre, post, Hc, Hlen, Hqc, Hr'⟩ := cut_views i _ _ v g w h j r Hq Hj Hr
  have Hu := slots_replace_view _ v g j none none y pre _ post Hc Hlen.symm
  have Hu' := slots_replace_view _ w h r none none y _ _ _ Hqc Hr'
  have Hs : tp_slots (mk_pool (n + 2) (Vector.cons x (v.set j y)) (Vector.cons g[j] g)
      (some j.succ)) = (x, i) :: pre ++ (y, i) :: post := by
    rw [slots_cons _ _ _ _ _ _ none, Hu, Hj]; rfl
  refine tp_equ_views _ _ ?_ ?_
  · rw [tp_slots_project, proj_slots_filter, Hs, slots_cons _ _ _ _ _ _ none, Hu', Hh]
    simp [List.filter_append, owned_by_self]
  · rw [focus_nat_project_owned i _ j.succ rfl (by
      show (Vector.cons g[j] g)[j.val + 1]'(by omega) = i
      rw [Vector.getElem_cons_succ]; exact Hj), Hs]
    simp only [focus_nat, mk_pool, Option.map_some, rank, fin_nat_FS, Hr', ← Hlen,
      List.cons_append, List.take_succ_cons, firstn_cut,
      List.filter_cons_of_pos (owned_by_self i _), List.length_cons]

/-- Pool-free fields agree pointwise. -/
def fields_eq (c d : OwnedCfg) : Prop :=
  (∀ j, c.anchor j = d.anchor j) ∧ (∀ j, c.heap j = d.heap j) ∧ c.ctx = d.ctx ∧
  c.base = d.base ∧ (∀ j, c.count j = d.count j) ∧ (∀ j, c.last j = d.last j)

theorem fields_eq_refl (c : OwnedCfg) : fields_eq c c :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem fields_eq_sym (c d : OwnedCfg) : fields_eq c d → fields_eq d c := by
  rintro ⟨ha, hh, hx, hb, hc, hl⟩
  exact ⟨fun j => (ha j).symm, fun j => (hh j).symm, hx.symm, hb.symm, fun j => (hc j).symm,
    fun j => (hl j).symm⟩

theorem fields_eq_trans (c d e : OwnedCfg) : fields_eq c d → fields_eq d e → fields_eq c e := by
  rintro ⟨ha, hh, hx, hb, hc, hl⟩ ⟨ha', hh', hx', hb', hc', hl'⟩
  exact ⟨fun j => (ha j).trans (ha' j), fun j => (hh j).trans (hh' j), hx.trans hx',
    hb.trans hb', fun j => (hc j).trans (hc' j), fun j => (hl j).trans (hl' j)⟩

theorem fields_eq_project (i : Side) (c d : OwnedCfg) :
    fields_eq c d → fields_eq (project i c) (project i d) := by
  rintro ⟨ha, hh, hx, hb, hc, hl⟩
  refine ⟨fun j => ?_, fun j => ?_, hx, hb, fun j => ?_, fun j => ?_⟩ <;>
    simp [project, side_only, ha, hh, hc, hl]

theorem owned_equ_pool_fields (c d : OwnedCfg) :
    tp_equ c.pool d.pool → fields_eq c d → owned_equ c d := by
  rintro hp ⟨ha, hh, hx, hb, hc, hl⟩
  exact ⟨hp, fun j => by rw [ha j]; exact peq_refl _, fun j => by rw [hh j]; exact peq_refl _,
    hx, hb, hc, hl⟩

theorem owned_equ_intro (c d : OwnedCfg) :
    cfg_slots c = cfg_slots d → cfg_focus c = cfg_focus d → fields_eq c d → owned_equ c d :=
  fun hs hf hfields => owned_equ_pool_fields c d (tp_equ_views _ _ hs hf) hfields

theorem project_set_pool (i : Side) (c : OwnedCfg) (p : TaggedPool) :
    project i (set_pool c p) = set_pool (project i c) (project_pool i p) := rfl

theorem projection_slots (i : Side) (p : TaggedPool) (n : Nat) (w : Pool sE Bn n)
    (h : Vector Side n) (f : Option (Fin n)) :
    project_pool i p = mk_pool n w h f →
    tp_slots (mk_pool n w h none) = (tp_slots p).filter (owned_by i) := by
  intro H
  rw [← proj_slots_filter, ← tp_slots_project, H]; rfl

theorem projection_focus_none (i : Side) (p : TaggedPool) :
    p.focus = none → focus_nat (project_pool i p) = none := by
  intro H; simp [focus_nat, project_focus_none i p H]

theorem project_action_owner (i : Side) (c : OwnedCfg) (a : OwnedAction) :
    (project_action i c a).owner = a.owner := by
  unfold project_action; split <;> rfl

theorem project_focused_index (i : Side) (p : TaggedPool) (j : Fin p.size) :
    p.focus = some j → p.tags[j] = i →
    ∃ r : Fin (project_pool i p).size,
      fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ∧
      (project_pool i p).threads[r] = p.threads[j] ∧
      (project_pool i p).tags[r] = i ∧ (project_pool i p).focus = some r := by
  intro hf hj
  obtain ⟨r, hr, ht, hg⟩ := project_index i p j hj
  exact ⟨r, hr, ht, hg, project_focus_owned i p j r hf hj hr⟩

/-- `project_index` for a projected pool already split into its fields. -/
theorem project_index_at (i : Side) (p : TaggedPool) (j : Fin p.size) (hj : p.tags[j] = i)
    (m : Nat) (w : Pool sE Bn m) (h : Vector Side m) (f : Option (Fin m))
    (hQ : project_pool i p = mk_pool m w h f) :
    ∃ r : Fin m, fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ∧
      w[r] = p.threads[j] ∧ h[r] = i := by
  cases hQ; exact project_index i p j hj

/-- `project_focused_index` for a projected pool already split into its fields. -/
theorem project_focused_index_at (i : Side) (p : TaggedPool) (j : Fin p.size)
    (hf : p.focus = some j) (hj : p.tags[j] = i)
    (m : Nat) (w : Pool sE Bn m) (h : Vector Side m) (f : Option (Fin m))
    (hQ : project_pool i p = mk_pool m w h f) :
    ∃ r : Fin m, fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ∧
      w[r] = p.threads[j] ∧ h[r] = i ∧ f = some r := by
  cases hQ; exact project_focused_index i p j hf hj

/-- `project_index_inv` for a projected pool already split into its fields. -/
theorem project_index_inv_at (i : Side) (p : TaggedPool)
    (m : Nat) (w : Pool sE Bn m) (h : Vector Side m) (f : Option (Fin m))
    (hQ : project_pool i p = mk_pool m w h f) (r : Fin m) :
    ∃ j : Fin p.size, p.tags[j] = i ∧ fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ∧
      w[r] = p.threads[j] ∧ h[r] = i := by
  cases hQ; exact project_index_inv i p r

theorem project_select_equ (i : Side) (n m : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (w : Pool sE Bn m) (h : Vector Side m) (j : Fin n) (r : Fin m) :
    tp_slots (mk_pool m w h none) = (tp_slots (mk_pool n v g none)).filter (owned_by i) →
    g[j] = i → fin_nat r = rank (owned_by i) (tp_slots (mk_pool n v g none)) (fin_nat j) →
    tp_equ (project_pool i (mk_pool n v g (some j))) (mk_pool m w h (some r)) := by
  intro Hq Hj Hr
  refine tp_equ_views _ _ ?_ ?_
  · rw [tp_slots_project, proj_slots_filter]; exact Hq.symm
  · rw [focus_nat_project_owned i _ j rfl Hj]
    show some (rank (owned_by i) (tp_slots (mk_pool n v g none)) (fin_nat j)) = _
    rw [← Hr]; rfl

theorem foreign_replace_slots (i : Side) (n : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (j : Fin n) (t : Thread sE Bn) : g[j] ≠ i →
    (tp_slots (mk_pool n (v.set j t) g none)).filter (owned_by i) =
      (tp_slots (mk_pool n v g none)).filter (owned_by i) := by
  intro Hj; simp only [Fin.getElem_fin] at Hj
  obtain ⟨pre, post, Hc, Hlen⟩ := pool_cut_mk n v g none j
  rw [slots_replace_view n v g j none none t pre _ post Hc Hlen.symm, Hc]
  simp [List.filter_append, owned_by_other i _ _ Hj]

theorem foreign_remove_slots (i : Side) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) : g[j] ≠ i →
    (tp_slots (mk_pool n (vector_remove v j) (vector_remove g j) none)).filter (owned_by i) =
      (tp_slots (mk_pool (n + 1) v g none)).filter (owned_by i) := by
  intro Hj; simp only [Fin.getElem_fin] at Hj
  obtain ⟨pre, post, Hc, Hlen⟩ := pool_cut_mk (n + 1) v g none j
  rw [slots_remove_view n v g j none none pre _ post Hc Hlen.symm, Hc]
  simp [List.filter_append, owned_by_other i _ _ Hj]

theorem project_foreign_select_equ (i : Side) (n : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (j : Fin n) : g[j] ≠ i →
    tp_equ (project_pool i (mk_pool n v g (some j))) (project_pool i (mk_pool n v g none)) := by
  intro Hj; simp only [Fin.getElem_fin] at Hj
  exact tp_equ_views _ _ rfl (by simp [focus_nat, project_pool, proj_focus, mk_pool, Hj])

theorem project_foreign_replace_equ (i : Side) (n : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (j : Fin n) (t : Thread sE Bn) (focused : Bool) : g[j] ≠ i →
    tp_equ (project_pool i (mk_pool n (v.set j t) g (if focused then some j else none)))
      (project_pool i (mk_pool n v g (some j))) := by
  intro Hj; simp only [Fin.getElem_fin] at Hj
  refine tp_equ_views _ _ ?_ ?_
  · rw [tp_slots_project, tp_slots_project, proj_slots_filter, proj_slots_filter]
    exact foreign_replace_slots i n v g j t Hj
  · cases focused <;> simp [focus_nat, project_pool, proj_focus, mk_pool, Hj]

theorem project_foreign_fork_equ (i : Side) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (x y : Thread sE Bn) : g[j] ≠ i →
    tp_equ
      (project_pool i (mk_pool (n + 2) (Vector.cons x (v.set j y)) (Vector.cons g[j] g)
        (some j.succ)))
      (project_pool i (mk_pool (n + 1) v g (some j))) := by
  intro Hj; simp only [Fin.getElem_fin] at Hj
  refine tp_equ_views _ _ ?_ ?_
  · rw [tp_slots_project, tp_slots_project, proj_slots_filter, proj_slots_filter,
      slots_cons _ _ _ _ _ _ none, List.filter_cons_of_neg (by simp [owned_by_other i _ _ Hj])]
    exact foreign_replace_slots i _ v g j y Hj
  · simp [focus_nat, project_pool, proj_focus, mk_pool, Hj]

theorem project_foreign_remove_equ (i : Side) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) : g[j] ≠ i →
    tp_equ (project_pool i (mk_pool n (vector_remove v j) (vector_remove g j) none))
      (project_pool i (mk_pool (n + 1) v g (some j))) := by
  intro Hj; simp only [Fin.getElem_fin] at Hj
  refine tp_equ_views _ _ ?_ ?_
  · rw [tp_slots_project, tp_slots_project, proj_slots_filter, proj_slots_filter]
    exact foreign_remove_slots i n v g j Hj
  · simp [focus_nat, project_pool, proj_focus, mk_pool, Hj]

/-! ## Primitives on the projection -/

/-- A primitive of lineage `i` behaves identically on its projection. -/
theorem prim_project (i : Side) (c : OwnedCfg) (e : sE.I) :
    match prim_step i c e, prim_step i (project i c) e with
    | some (kind, y, c1), some (kind', y', c1') =>
      y = y' ∧ project_action i c (act i kind) = act i kind' ∧ fields_eq c1' (project i c1)
    | none, none => True
    | _, _ => False := by
  have hh : (project i c).heap i = c.heap i := by simp [project, side_only]
  have hf : ∀ m, fields_eq (set_heap (project i c) i m) (project i (set_heap c i m)) := by
    intro m
    refine ⟨fun j => rfl, fun j => ?_, rfl, rfl, fun j => rfl, fun j => rfl⟩
    cases i <;> cases j <;> rfl
  rcases e with ((a | ⟨a, v⟩ | sz | b | ⟨a, ex, de⟩) | ((_ | x) | p))
  all_goals simp only [prim_step, heap_prim, ctx_prim, emit_prim, hh]
  · cases (c.heap i).1 a <;> simp [project_action, act, fields_eq_refl]
  · cases (c.heap i).1 a <;> simp [project_action, act, hf]
  · cases managed_free (c.heap i) b <;> simp [project_action, act, hf]
  · cases (c.heap i).1 a with
    | none => trivial
    | some x => by_cases hx : x = ex <;> simp [hx, project_action, act, hf, fields_eq_refl]
  · exact ⟨rfl, rfl, fields_eq_refl _⟩
  · refine ⟨trivial, ?_, ?_⟩
    · cases i <;> simp [project_action, act, global_count, project, side_only]
    · refine ⟨fun j => rfl, fun j => rfl, rfl, rfl, fun j => ?_, fun j => ?_⟩ <;>
        cases i <;> cases j <;> rfl

theorem prim_foreign (s i : Side) (c : OwnedCfg) (e : sE.I) (kind : OwnedKind) (y : sE.O e)
    (c1 : OwnedCfg) :
    s ≠ i → prim_step s c e = some (kind, y, c1) → fields_eq (project i c1) (project i c) := by
  intro hs
  have hf : ∀ m, fields_eq (project i (set_heap c s m)) (project i c) := by
    intro m
    refine ⟨fun j => rfl, fun j => ?_, rfl, rfl, fun j => rfl, fun j => rfl⟩
    cases s <;> cases i <;> cases j <;> first | rfl | exact absurd rfl hs
  rcases e with ((a | ⟨a, v⟩ | sz | b | ⟨a, ex, de⟩) | ((_ | x) | p))
  all_goals simp only [prim_step, heap_prim, ctx_prim, emit_prim]
  · cases (c.heap s).1 a <;> simp; rintro rfl rfl rfl; exact fields_eq_refl _
  · cases (c.heap s).1 a <;> simp; intros; subst_vars; exact hf _
  · simp
  · cases managed_free (c.heap s) b <;> simp; intros; subst_vars; exact hf _
  · cases (c.heap s).1 a with
    | none => simp
    | some x =>
      by_cases hx : x = ex <;> simp [hx] <;> rintro rfl rfl rfl <;>
        first | exact hf _ | exact fields_eq_refl _
  · rintro ⟨⟩; exact fields_eq_refl _
  · simp
  · rintro ⟨⟩
    refine ⟨fun j => rfl, fun j => rfl, rfl, rfl, fun j => ?_, fun j => ?_⟩ <;>
      cases s <;> cases i <;> cases j <;> first | rfl | exact absurd rfl hs

/-! ## Direct projection of vector transitions -/

theorem focus_step_owner (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (a : OwnedAction) (c' : OwnedCfg) :
    focus_step c n v g j a c' → a.owner = g[j] := by
  rintro (⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, rfl, _⟩ |
    ⟨_, _, _, _, _, _, _, rfl, _⟩) <;> rfl

/-- `owned_step` on a configuration whose pool is focused. -/
private theorem owned_step_focused {c : OwnedCfg} {m : Nat} {w : Pool sE Bn (m + 1)}
    {h : Vector Side (m + 1)} {r : Fin (m + 1)} (hp : c.pool = mk_pool (m + 1) w h (some r))
    {a : OwnedAction} {c' : OwnedCfg} : owned_step c a c' ↔ focus_step c m w h r a c' := by
  unfold owned_step; rw [hp]; rfl

/-- `owned_step` on a configuration whose pool is unfocused and nonempty. -/
private theorem owned_step_unfocused' {c : OwnedCfg} {m : Nat} {w : Pool sE Bn (m + 1)}
    {h : Vector Side (m + 1)} (hp : c.pool = mk_pool (m + 1) w h none)
    {a : OwnedAction} {c' : OwnedCfg} : owned_step c a c' ↔ sel_step c m w h a c' := by
  unfold owned_step; rw [hp]; rfl

theorem owned_step_focused_owner (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step c a c' → ∀ j, c.pool.focus = some j → a.owner = c.pool.tags[j] := by
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  intro H j hf
  cases n with
  | zero => exact H.elim
  | succ n =>
    cases f with
    | none => cases hf
    | some k => cases hf; exact focus_step_owner _ _ _ _ _ _ _ H

theorem owned_step_unfocused (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    c.pool.focus = none → owned_step c a c' → a.action_kind = .select := by
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  intro hf H
  cases n with
  | zero => exact H.elim
  | succ n =>
    cases f with
    | some k => cases hf
    | none => obtain ⟨j, rfl, -⟩ := H; rfl

theorem unfocused_progress (c : OwnedCfg) :
    c.pool.focus = none → 0 < c.pool.size → hcan_step owned_next c := by
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  intro hf hn
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ n =>
    cases f with
    | some k => cases hf
    | none => exact ⟨_, act g[0] .select, 0, rfl, rfl⟩

/-- An action of lineage `i` is one local action of its projection. -/
theorem owned_step_own (i : Side) (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step c a c' → a.owner = i →
    ∃ d', owned_step (project i c) (project_action i c a) d' ∧ owned_equ (project i c') d' := by
  intro H Ho
  have Hpp := prim_project i c
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  cases n with
  | zero => exact H.elim
  | succ n =>
  cases f with
  | some j =>
    have H : focus_step _ n v g j a c' := H
    have Hj : g[j] = i := (focus_step_owner _ _ _ _ _ _ _ H).symm.trans Ho
    rcases Hq : project_pool i (mk_pool (n + 1) v g (some j)) with ⟨m, w, h, fq⟩
    obtain ⟨r, Hr, Ht, Hg, Hf⟩ :=
      project_focused_index_at i (mk_pool (n + 1) v g (some j)) j rfl Hj _ _ _ _ Hq
    have Hpool : (project i ⟨⟨n + 1, v, g, some j⟩, an, he, cx, b, co, la⟩).pool =
      mk_pool m w h fq := Hq
    cases m with
    | zero => exact r.elim0
    | succ m =>
    subst Hf
    have Hslots := projection_slots i _ _ w h _ Hq
    have HS := fun {a} {c'} => owned_step_focused (a := a) (c' := c') Hpool
    rcases H with ⟨t, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨Hh, rfl, rfl⟩ |
      ⟨e, k, kind, y, c1, Hh, Hprim, rfl, rfl⟩
    · refine ⟨_, HS.2 (.inl ⟨t, Ht ▸ Hh, ?_, rfl⟩), owned_equ_pool_fields _ _
        (project_replace_equ i _ _ v g w h j r t true Hslots Hj Hr) (fields_eq_refl _)⟩
      simp [project_action, act, Hg, Hj]
    · refine ⟨_, HS.2 (.inr (.inl ⟨k, Ht ▸ Hh, ?_, rfl⟩)), owned_equ_pool_fields _ _
        (project_replace_equ i _ _ v g w h j r (k ⟨⟩) false Hslots Hj Hr) (fields_eq_refl _)⟩
      simp [project_action, act, Hg, Hj]
    · refine ⟨_, HS.2 (.inr (.inr (.inl ⟨k, Ht ▸ Hh, ?_, rfl⟩))), owned_equ_pool_fields _ _
        (project_fork_equ i _ _ v g w h j r _ _ Hslots Hj Hg Hr) (fields_eq_refl _)⟩
      simp [project_action, act, Hg, Hj]
    · refine ⟨_, HS.2 (.inr (.inr (.inr (.inl ⟨Ht ▸ Hh, ?_, rfl⟩)))), owned_equ_pool_fields _ _
        (project_remove_equ i _ _ v g w h j r Hslots Hj Hr) (fields_eq_refl _)⟩
      simp [project_action, act, Hg, Hj]
    · rw [Hj] at Hprim
      have Hpp := Hpp e
      rw [Hprim] at Hpp
      rcases Hprim' : prim_step i (project i ⟨⟨n + 1, v, g, some j⟩, an, he, cx, b, co, la⟩) e
        with _ | ⟨kind', y', c1'⟩
      · rw [Hprim'] at Hpp; exact Hpp.elim
      rw [Hprim'] at Hpp
      obtain ⟨rfl, Hact, Hfields⟩ := Hpp
      refine ⟨_, HS.2 (.inr (.inr (.inr (.inr ⟨e, k, kind', y, c1', Ht ▸ Hh,
        by rw [Hg]; exact Hprim', ?_, rfl⟩)))), owned_equ_pool_fields _ _
        (project_replace_equ i _ _ v g w h j r (k y) true Hslots Hj Hr)
        (fields_eq_sym _ _ Hfields)⟩
      rw [Hj, Hg]; exact Hact
  | none =>
    obtain ⟨j, rfl, rfl⟩ := H
    have Ho : g[j] = i := Ho
    rcases Hq : project_pool i (mk_pool (n + 1) v g none) with ⟨m, w, h, fq⟩
    obtain ⟨r, Hr, Ht, Hg⟩ := project_index_at i (mk_pool (n + 1) v g none) j Ho _ _ _ _ Hq
    have Hnone : fq = none := by
      have := project_focus_none i (mk_pool (n + 1) v g none) rfl; rw [Hq] at this; exact this
    have Hpool : (project i ⟨⟨n + 1, v, g, none⟩, an, he, cx, b, co, la⟩).pool =
      mk_pool m w h fq := Hq
    cases m with
    | zero => exact r.elim0
    | succ m =>
    cases Hnone
    refine ⟨_, (owned_step_unfocused' Hpool).2 ⟨r, ?_, rfl⟩, owned_equ_pool_fields _ _
      (project_select_equ i _ _ v g w h j r (projection_slots i _ _ w h _ Hq) Ho Hr)
      (fields_eq_refl _)⟩
    simp [project_action, act, Hg, Ho]

/-- A foreign action leaves the projection unchanged. -/
theorem owned_step_foreign (i : Side) (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step c a c' → a.owner ≠ i → owned_equ (project i c') (project i c) := by
  intro H Ho
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  cases n with
  | zero => exact H.elim
  | succ n =>
  cases f with
  | some j =>
    have H : focus_step _ n v g j a c' := H
    have Hj : g[j] ≠ i := fun h => Ho ((focus_step_owner _ _ _ _ _ _ _ H).trans h)
    rcases H with ⟨t, -, rfl, rfl⟩ | ⟨k, -, rfl, rfl⟩ | ⟨k, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ |
      ⟨e, k, kind, y, c1, -, Hprim, rfl, rfl⟩
    · exact owned_equ_pool_fields _ _ (project_foreign_replace_equ i _ v g j t true Hj)
        (fields_eq_refl _)
    · exact owned_equ_pool_fields _ _ (project_foreign_replace_equ i _ v g j (k ⟨⟩) false Hj)
        (fields_eq_refl _)
    · exact owned_equ_pool_fields _ _ (project_foreign_fork_equ i n v g j _ _ Hj)
        (fields_eq_refl _)
    · exact owned_equ_pool_fields _ _ (project_foreign_remove_equ i n v g j Hj)
        (fields_eq_refl _)
    · exact owned_equ_pool_fields _ _ (project_foreign_replace_equ i _ v g j (k y) true Hj)
        (prim_foreign _ i _ e kind y c1 Hj Hprim)
  | none =>
    obtain ⟨j, rfl, rfl⟩ := H
    exact owned_equ_pool_fields _ _ (project_foreign_select_equ i _ v g j Ho) (fields_eq_refl _)

/-- Every local successor lifts when focus is absent or belongs to `i`. -/
theorem owned_step_lift (i : Side) (c : OwnedCfg) (a' : OwnedAction) (d' : OwnedCfg) :
    (c.pool.focus = none ∨ ∃ j, c.pool.focus = some j ∧ c.pool.tags[j] = i) →
    owned_step (project i c) a' d' →
    ∃ a c', owned_step c a c' ∧ a.owner = i ∧ project_action i c a = a' ∧
      owned_equ (project i c') d' := by
  intro Hfocus Hlocal
  have Hpp := prim_project i c
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  cases f with
  | some j =>
    obtain ⟨j', Hf, Hj⟩ : ∃ j', some j = some j' ∧ g[j'] = i := by
      rcases Hfocus with h | h
      · cases h
      · exact h
    cases Hf
    cases n with
    | zero => exact j.elim0
    | succ n =>
    rcases Hq : project_pool i (mk_pool (n + 1) v g (some j)) with ⟨m, w, h, fq⟩
    obtain ⟨r, Hr, Ht, Hg, Hf⟩ :=
      project_focused_index_at i (mk_pool (n + 1) v g (some j)) j rfl Hj _ _ _ _ Hq
    cases m with
    | zero => exact r.elim0
    | succ m =>
    subst Hf
    have Hpool : (project i ⟨⟨n + 1, v, g, some j⟩, an, he, cx, b, co, la⟩).pool =
      mk_pool (m + 1) w h (some r) := Hq
    have Hslots := projection_slots i _ _ w h _ Hq
    have HS := fun {a} {c'} =>
      owned_step_focused (c := ⟨⟨n + 1, v, g, some j⟩, an, he, cx, b, co, la⟩) (a := a)
        (c' := c') rfl
    rcases (owned_step_focused Hpool).1 Hlocal with ⟨t, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ |
      ⟨k, Hh, rfl, rfl⟩ | ⟨Hh, rfl, rfl⟩ | ⟨e, k, kind', y, c1', Hh, Hprim', rfl, rfl⟩
    · exact ⟨act i .step, _, HS.2 (.inl ⟨t, Ht ▸ Hh, congrArg (act · .step) Hj.symm, rfl⟩), rfl,
        by simp [project_action, act, Hg], owned_equ_pool_fields _ _
          (project_replace_equ i _ _ v g w h j r t true Hslots Hj Hr) (fields_eq_refl _)⟩
    · exact ⟨act i .yield, _,
        HS.2 (.inr (.inl ⟨k, Ht ▸ Hh, congrArg (act · .yield) Hj.symm, rfl⟩)), rfl,
        by simp [project_action, act, Hg], owned_equ_pool_fields _ _
          (project_replace_equ i _ _ v g w h j r (k ⟨⟩) false Hslots Hj Hr) (fields_eq_refl _)⟩
    · exact ⟨act i .fork, _,
        HS.2 (.inr (.inr (.inl ⟨k, Ht ▸ Hh, congrArg (act · .fork) Hj.symm, rfl⟩))), rfl,
        by simp [project_action, act, Hg], owned_equ_pool_fields _ _
          (project_fork_equ i _ _ v g w h j r _ _ Hslots Hj Hg Hr) (fields_eq_refl _)⟩
    · exact ⟨act i .ret, _,
        HS.2 (.inr (.inr (.inr (.inl ⟨Ht ▸ Hh, congrArg (act · .ret) Hj.symm, rfl⟩)))), rfl,
        by simp [project_action, act, Hg], owned_equ_pool_fields _ _
          (project_remove_equ i _ _ v g w h j r Hslots Hj Hr) (fields_eq_refl _)⟩
    · rw [Hg] at Hprim'
      have Hpp := Hpp e
      rw [Hprim'] at Hpp
      rcases Hprim : prim_step i ⟨⟨n + 1, v, g, some j⟩, an, he, cx, b, co, la⟩ e
        with _ | ⟨kind, y0, c1⟩
      · rw [Hprim] at Hpp; exact Hpp.elim
      rw [Hprim] at Hpp
      obtain ⟨rfl, Hact, Hfields⟩ := Hpp
      exact ⟨act i kind, _, HS.2 (.inr (.inr (.inr (.inr ⟨e, k, kind, y0, c1, Ht ▸ Hh,
        by rw [Hj]; exact Hprim, congrArg (act · kind) Hj.symm, rfl⟩)))), rfl,
        by rw [Hg]; exact Hact, owned_equ_pool_fields _ _
          (project_replace_equ i _ _ v g w h j r (k y0) true Hslots Hj Hr)
          (fields_eq_sym _ _ Hfields)⟩
  | none =>
    rcases Hq : project_pool i (mk_pool n v g none) with ⟨m, w, h, fq⟩
    have Hnone : fq = none := by
      have := project_focus_none i (mk_pool n v g none) rfl; rw [Hq] at this; exact this
    subst Hnone
    cases m with
    | zero =>
      exact (owned_step_empty _ _ _ (by
        show (project_pool i (mk_pool n v g none)).size = 0; rw [Hq]) Hlocal).elim
    | succ m =>
    have Hpool : (project i ⟨⟨n, v, g, none⟩, an, he, cx, b, co, la⟩).pool =
      mk_pool (m + 1) w h none := Hq
    obtain ⟨r, rfl, rfl⟩ := (owned_step_unfocused' Hpool).1 Hlocal
    obtain ⟨j, Hj, Hr, Ht, Hg⟩ := project_index_inv_at i (mk_pool n v g none) _ _ _ _ Hq r
    cases n with
    | zero => exact j.elim0
    | succ n =>
    exact ⟨act i .select, _, (owned_step_unfocused' rfl).2
      ⟨j, congrArg (act · .select) Hj.symm, rfl⟩, rfl, by simp [project_action, act, Hg],
      owned_equ_pool_fields _ _
        (project_select_equ i _ _ v g w h j r (projection_slots i _ _ w h _ Hq) Hj Hr)
        (fields_eq_refl _)⟩

theorem own_enabled_intro (i : Side) (c : OwnedCfg) :
    (c.pool.focus = none ∨ ∃ j, c.pool.focus = some j ∧ c.pool.tags[j] = i) →
    hcan_step owned_next (project i c) → OwnEnabled i c :=
  fun Hf Hcan => ⟨Hcan, fun _ _ => owned_step_lift i c _ _ Hf⟩

/-- Positive progress excludes a stuck owned focus from the stutter case. -/
theorem scheduler_shape (i : Side) (c : OwnedCfg) :
    hcan_step owned_next c → StutterOnly i c ∨ OwnEnabled i c := by
  rintro ⟨c', a, Hstep⟩
  rcases Hfocus : c.pool.focus with _ | j
  · rcases Hsize : (project i c).pool.size with _ | n
    · left; intro b d Hd Ho
      obtain ⟨d', Hd', -⟩ := owned_step_own i _ _ _ Hd Ho
      exact owned_step_empty _ _ _ Hsize Hd'
    · exact .inr (own_enabled_intro i c (.inl Hfocus)
        (unfocused_progress _ (project_focus_none _ _ Hfocus) (by rw [Hsize]; omega)))
  · by_cases Hj : c.pool.tags[j] = i
    · refine .inr (own_enabled_intro i c (.inr ⟨j, Hfocus, Hj⟩) ?_)
      obtain ⟨d, Hd, -⟩ :=
        owned_step_own i _ _ _ Hstep ((owned_step_focused_owner _ _ _ Hstep j Hfocus).trans Hj)
      exact ⟨d, _, Hd⟩
    · left; intro b d Hd; rw [owned_step_focused_owner _ _ _ Hd j Hfocus]; exact Hj

theorem stutter_select (i : Side) (c : OwnedCfg) :
    hcan_step owned_next c → StutterOnly i c → 0 < (project i c).pool.size →
    (project i c).pool.focus = none ∧ hcan_step owned_next (project i c) ∧
    ∀ a d, owned_step (project i c) a d → a.action_kind = .select := by
  rintro ⟨d, a, Hstep⟩ Hst Hsize
  have Hnone : (project i c).pool.focus = none := by
    rcases Hfocus : c.pool.focus with _ | j
    · exact project_focus_none _ _ Hfocus
    · refine project_focus_foreign i c.pool j Hfocus ?_
      rw [← owned_step_focused_owner _ _ _ Hstep j Hfocus]; exact Hst _ _ Hstep
  exact ⟨Hnone, unfocused_progress _ Hnone Hsize, fun _ _ He => owned_step_unfocused _ _ _ Hnone He⟩

theorem foreign_star_project (i : Side) (c c' : OwnedCfg) :
    Star (foreign_next i) c c' → owned_equ (project i c') (project i c) := by
  intro h
  induction h with
  | refl => exact owned_equ_Equivalence.refl _
  | tail _ hbc ih =>
    obtain ⟨a, Ha, Ho⟩ := hbc
    exact owned_equ_Equivalence.trans (owned_step_foreign _ _ _ _ Ha Ho) ih

theorem weak_next_equ (i : Side) (c d c' : OwnedCfg) :
    owned_equ c d → weak_next i c c' → ∃ d', weak_next i d d' ∧ owned_equ c' d' := by
  intro E H; obtain rfl := owned_equ_eq E; exact ⟨c', H, owned_equ_Equivalence.refl _⟩

theorem weak_next_sound (i : Side) (c c' : OwnedCfg) :
    weak_next i c c' → ∃ d', owned_next (project i c) d' ∧ owned_equ (project i c') d' := by
  rintro ⟨mid, Hstar, a, Hst, Ho⟩
  obtain ⟨d', Hd, He⟩ := owned_step_own _ _ _ _ Hst Ho
  obtain ⟨d'', Hd'', He''⟩ := owned_step_equ _ _ _ _ (foreign_star_project _ _ _ Hstar) Hd
  exact ⟨d'', ⟨_, Hd''⟩, owned_equ_Equivalence.trans He He''⟩

/-- One weak successor witnesses that every local successor is realized. -/
theorem weak_next_complete (i : Side) (c : OwnedCfg) :
    hcan_step (weak_next i) c →
    ∀ d', owned_next (project i c) d' → ∃ c', weak_next i c c' ∧ owned_equ (project i c') d' := by
  rintro ⟨c1, mid, Hstar, a, Hst, Ho⟩ d' ⟨a', Hd⟩
  obtain ⟨d'', Hd'', He⟩ :=
    owned_step_equ _ _ _ _ (owned_equ_Equivalence.symm (foreign_star_project _ _ _ Hstar)) Hd
  rcases scheduler_shape i mid ⟨c1, a, Hst⟩ with Hstut | ⟨-, Hlift⟩
  · exact (Hstut a c1 Hst Ho).elim
  · obtain ⟨b, c', Hb, Hob, -, He'⟩ := Hlift _ _ Hd''
    exact ⟨c', ⟨mid, Hstar, b, Hb, Hob⟩,
      owned_equ_Equivalence.trans He' (owned_equ_Equivalence.symm He)⟩

theorem reach_project (i : Side) (c0 c : OwnedCfg) :
    Star owned_next c0 c → ∃ d, Star owned_next (project i c0) d ∧ owned_equ d (project i c) := by
  intro H
  induction H with
  | refl => exact ⟨_, .refl, owned_equ_Equivalence.refl _⟩
  | tail _ hyz ih =>
    obtain ⟨d, Hd, He⟩ := ih
    obtain ⟨a, Ha⟩ := hyz
    by_cases Ho : a.owner = i
    · obtain ⟨e, He1, He2⟩ := owned_step_own _ _ _ _ Ha Ho
      obtain ⟨e', He', Hee⟩ := owned_step_equ _ _ _ _ (owned_equ_Equivalence.symm He) He1
      exact ⟨e', .tail Hd ⟨_, He'⟩,
        owned_equ_Equivalence.symm (owned_equ_Equivalence.trans He2 Hee)⟩
    · exact ⟨d, Hd, owned_equ_Equivalence.trans He
        (owned_equ_Equivalence.symm (owned_step_foreign _ _ _ _ Ha Ho))⟩

theorem owned_wf_project (i : Side) (c : OwnedCfg) : owned_wf c → owned_wf (project i c) := by
  rintro ⟨H1, H2, H3, H4, H5, H6, H7, H8⟩
  cases i
  · exact ⟨H1, managed_wf_empty, H3, managed_wf_empty, pdef_emp_r _, H6, support_le_refl _,
      pdef_emp_r _⟩
  · exact ⟨managed_wf_empty, H2, managed_wf_empty, H4, pdef_emp _, support_le_refl _, H7,
      pdef_emp _⟩

theorem project_size_terminal (i : Side) (c : OwnedCfg) :
    c.pool.size = 0 → (project i c).pool.size = 0 := by
  intro H
  show (proj_slots i c.pool).length = 0
  have Hl := tp_slots_length c.pool
  rw [H] at Hl
  rw [proj_slots_filter, List.eq_nil_of_length_eq_zero Hl]; rfl

theorem same_view_equivalence : Equivalence same_view where
  refl _ := ⟨fun _ => peq_refl _, rfl, rfl, fun _ => rfl, fun _ => rfl, Iff.rfl⟩
  symm := fun ⟨hh, hx, hb, hn, hl, ht⟩ =>
    ⟨fun i => peq_sym _ _ (hh i), hx.symm, hb.symm, fun i => (hn i).symm, fun i => (hl i).symm,
      ht.symm⟩
  trans := fun ⟨hh, hx, hb, hn, hl, ht⟩ ⟨gh, gx, gb, gn, gl, gt⟩ =>
    ⟨fun i => peq_trans _ _ _ (hh i) (gh i), hx.trans gx, hb.trans gb,
      fun i => (hn i).trans (gn i), fun i => (hl i).trans (gl i), ht.trans gt⟩

theorem owned_equ_same_view (c d : OwnedCfg) : owned_equ c d → same_view c d := by
  rintro ⟨Ep, -, Eh, Ex, Eb, En, El⟩
  exact ⟨Eh, Ex, Eb, En, El, by rw [tp_equ_size _ _ Ep]⟩

theorem same_view_project (i : Side) (c d : OwnedCfg) :
    c.pool.size = 0 → same_view c d → same_view (project i c) (project i d) := by
  rintro Hc ⟨Hh, Hx, Hb, Hn, Hl, Ht⟩
  have Hd := Ht.1 Hc
  refine ⟨fun j => ?_, Hx, Hb, fun j => ?_, fun j => ?_,
    ⟨fun _ => project_size_terminal i d Hd, fun _ => project_size_terminal i c Hc⟩⟩ <;>
    simp only [project, side_only] <;> cases side_eqb j i
  all_goals first | exact peq_refl _ | exact Hh j | rfl | exact Hn j | exact Hl j

/-! ## Focused threads and confinement -/

/-- The focused thread is invariant under `tp_equ` (Rocq: up to `≅`, here equality). -/
theorem focused_thread_equ (p q : TaggedPool) (t : Thread sE Bn) (i : Side) :
    tp_equ p q → focused_thread q = some (t, i) →
    ∃ t', focused_thread p = some (t', i) ∧ t' = t := by
  intro h H; obtain rfl := tp_equ_eq h; exact ⟨t, H, rfl⟩

/-- The focused owned thread is the focused thread of the projection. -/
theorem focused_project (i : Side) (p : TaggedPool) (t : Thread sE Bn) :
    focused_thread p = some (t, i) → focused_thread (project_pool i p) = some (t, i) := by
  unfold focused_thread
  rcases Hf : p.focus with _ | j
  · intro H; cases H
  · intro H; cases H
    obtain ⟨r, -, Hr, Htag, Hfocus⟩ := project_focused_index _ p j Hf rfl
    rw [Hfocus]; dsimp only; rw [Hr, Htag]

theorem confined_equ (r : ManagedHeap) (c d : OwnedCfg) :
    owned_equ c d → confined r c → confined r d := by
  intro E; obtain rfl := owned_equ_eq E; exact id

-- Not ported: Ltac helpers `unguarded_tac`, `fields_tac`, `destr_inner`, `step_inv` (tactics);
-- `forall2_nth_error` (local helper of `focused_thread_equ`, which follows from `tp_equ_eq`).
end Tisl.CSL
