/- SPDX-License-Identifier: MIT -/
module

/-!
# List utilities

Pure list operations shared by abstract and heap-backed queues: rotation, first-match search,
pointwise relations (`Forall2`), relation-polymorphic linking of node lists, window facts over
`List.range'`, and periodic choice sequences (← `Utils/Lists.v`).
-/

@[expose] public section
namespace Tisl

theorem hd_app {A} (l1 l2 : List A) (d : A) :
    (l1 ++ l2).headD d = l1.headD (l2.headD d) := by
  cases l1 <;> rfl

theorem hd_default {A} (l : List A) (d d' : A) : l ≠ [] → l.headD d = l.headD d' := by
  cases l <;> simp

theorem last_in {A} (l : List A) (d : A) : l ≠ [] → l.getLastD d ∈ l := by
  intro h
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  exact List.getLast_mem h

/-- Rotate left by one: the head moves to the end. -/
def rotl {A} (l : List A) : List A :=
  match l with
  | [] => []
  | x :: xs => xs ++ [x]

@[simp] theorem rotl_cons {A} (x : A) (xs : List A) : rotl (x :: xs) = xs ++ [x] := rfl

theorem rotl_perm {A} (l : List A) : List.Perm l (rotl l) := by
  cases l with
  | nil => exact .nil
  | cons x xs => exact (List.perm_append_singleton x xs).symm

theorem rotl_nonnil {A} (l : List A) : l ≠ [] → rotl l ≠ [] := by
  cases l <;> simp [rotl]

/-- Rotate left `n` times. -/
def rotlN {A} (n : Nat) (l : List A) : List A :=
  Nat.repeat rotl n l

/-- Zero-based FIRST matching position. Duplicate payloads are allowed. The comparator is explicit;
only the lemmas connecting matches to propositional equality require correctness. -/
def find_index {A} (eqb : A → A → Bool) (t : A) : List A → Option Nat
  | [] => none
  | h :: ts => if eqb h t then some 0 else Option.map Nat.succ (find_index eqb t ts)

theorem find_index_cons {A} (eqb : A → A → Bool) (t h : A) (ts : List A) :
    find_index eqb t (h :: ts) =
      (if eqb h t then some 0 else Option.map Nat.succ (find_index eqb t ts)) := rfl

theorem find_index_app_l {A} (eqb : A → A → Bool) (t : A) (ts : List A) (n : Nat) (l : List A) :
    find_index eqb t ts = some n → find_index eqb t (ts ++ l) = some n := by
  induction ts generalizing n with
  | nil => simp [find_index]
  | cons a ts ih =>
    simp only [List.cons_append, find_index]
    split
    · exact id
    · cases hf : find_index eqb t ts with
      | none => simp
      | some m => simp [ih m hf]

theorem find_index_nonnil {A} (eqb : A → A → Bool) (t : A) (l : List A) (n : Nat) :
    find_index eqb t l = some n → l ≠ [] := by
  cases l <;> simp [find_index]

/-- A non-head occurrence moves one position closer, even with duplicates. -/
theorem find_index_rotl {A} (eqb : A → A → Bool) (t v : A) (vs : List A) (d : Nat) :
    find_index eqb t (v :: vs) = some (d + 1) → find_index eqb t (rotl (v :: vs)) = some d := by
  simp only [find_index, rotl]
  split
  · simp
  · cases hf : find_index eqb t vs with
    | none => simp
    | some m => simp only [Option.map_some, Option.some.injEq, Nat.succ.injEq]; rintro rfl
                exact find_index_app_l eqb t vs m _ hf

section EqualitySearch
variable {A : Type _} (eqb : A → A → Bool) (eqb_correct : ∀ x y, eqb x y = true ↔ x = y)
include eqb_correct

theorem find_index_last_ex (t : A) (ts : List A) :
    ∃ n, find_index eqb t (ts ++ [t]) = some n := by
  induction ts with
  | nil => exact ⟨0, by simp [find_index, (eqb_correct t t).2 rfl]⟩
  | cons a ts ih =>
    simp only [List.cons_append, find_index]
    split
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, by simp [hn]⟩

theorem find_index_in (t : A) (l : List A) (n : Nat) : find_index eqb t l = some n → t ∈ l := by
  induction l generalizing n with
  | nil => simp [find_index]
  | cons a l ih =>
    simp only [find_index]
    split
    · rename_i ha; intro; exact .head _ |> ((eqb_correct a t).1 ha ▸ ·)
    · cases hf : find_index eqb t l with
      | none => simp
      | some m => intro; exact .tail _ (ih m hf)

theorem find_index_none (t : A) (l : List A) : find_index eqb t l = none ↔ t ∉ l := by
  induction l with
  | nil => simp [find_index]
  | cons a l ih =>
    simp only [find_index, List.mem_cons, not_or]
    split
    · rename_i ha; simp [(eqb_correct a t).1 ha]
    · rename_i ha
      have hne : t ≠ a := fun h => ha ((eqb_correct a t).2 h.symm)
      simp [ih, hne]

theorem find_index_head (t v : A) (vs : List A) : find_index eqb t (v :: vs) = some 0 → v = t := by
  simp only [find_index]
  split
  · rename_i hv; intro; exact (eqb_correct v t).1 hv
  · cases find_index eqb t vs <;> simp

/-- A head occurrence wraps around; an earlier duplicate may become first. -/
theorem find_index_rotl_pres (t v : A) (vs : List A) (d : Nat) :
    find_index eqb t (v :: vs) = some d → ∃ d', find_index eqb t (rotl (v :: vs)) = some d' := by
  intro h
  cases d with
  | zero =>
    obtain rfl := find_index_head eqb eqb_correct t v vs h
    exact find_index_last_ex eqb eqb_correct v vs
  | succ d => exact ⟨d, find_index_rotl eqb t v vs d h⟩

theorem find_index_rotation_progress (target a : A) (rest : List A) (d : Nat) :
    find_index eqb target (a :: rest) = some d →
    ∀ kb c, ∃ d', find_index eqb target (rotl (a :: rest)) = some d' ∧
      ((a = target ∧ kb ≤ c) ∨ (kb - (c + 1) < kb - c) ∨ (kb - (c + 1) = kb - c ∧ d' < d)) := by
  intro h kb c
  cases d with
  | zero =>
    obtain ⟨d', hd'⟩ := find_index_rotl_pres eqb eqb_correct target a rest 0 h
    have ha := find_index_head eqb eqb_correct target a rest h
    refine ⟨d', hd', ?_⟩
    by_cases hk : kb ≤ c
    · exact .inl ⟨ha, hk⟩
    · exact .inr (.inl (by omega))
  | succ d =>
    refine ⟨d, find_index_rotl eqb target a rest d h, .inr ?_⟩
    by_cases hk : kb ≤ c
    · exact .inr ⟨by omega, by omega⟩
    · exact .inl (by omega)

end EqualitySearch

/-- Pointwise relation between two lists (Rocq `Forall2`). -/
inductive Forall2 {A B} (R : A → B → Prop) : List A → List B → Prop
  | nil : Forall2 R [] []
  | cons {x y l l'} : R x y → Forall2 R l l' → Forall2 R (x :: l) (y :: l')

@[simp] theorem Forall2_nil_nil {A B} (R : A → B → Prop) : Forall2 R [] [] ↔ True :=
  ⟨fun _ => trivial, fun _ => .nil⟩

@[simp] theorem Forall2_cons_iff {A B} (R : A → B → Prop) (x : A) (y : B) l l' :
    Forall2 R (x :: l) (y :: l') ↔ R x y ∧ Forall2 R l l' :=
  ⟨fun | .cons h1 h2 => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => .cons h1 h2⟩

theorem Forall2_length {A B} {R : A → B → Prop} {xs ys} (h : Forall2 R xs ys) :
    xs.length = ys.length := by
  induction h <;> simp [*]

/-- Membership-aware strengthening keeps pairwise witnesses in their lists. -/
theorem Forall2_impl' {A B} (R S : A → B → Prop) (xs : List A) (ys : List B) :
    Forall2 R xs ys → (∀ x y, x ∈ xs → y ∈ ys → R x y → S x y) → Forall2 S xs ys := by
  intro h
  induction h with
  | nil => intro; exact .nil
  | cons hxy _ ih =>
    intro hS
    exact .cons (hS _ _ (.head _) (.head _) hxy)
      (ih fun a b ha hb hab => hS a b (.tail _ ha) (.tail _ hb) hab)

theorem Forall2_in_combine {A B} (R : A → B → Prop) (xs : List A) (ys : List B) :
    Forall2 R xs ys ↔ xs.length = ys.length ∧ ∀ x y, (x, y) ∈ xs.zip ys → R x y := by
  constructor
  · intro h
    refine ⟨Forall2_length h, ?_⟩
    induction h with
    | nil => simp
    | cons hxy _ ih =>
      intro a b hin
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hin
      rcases hin with ⟨rfl, rfl⟩ | hin
      · exact hxy
      · exact ih a b hin
  · induction xs generalizing ys with
    | nil => rintro ⟨hlen, -⟩; cases ys <;> simp_all
    | cons x xs ih =>
      rintro ⟨hlen, hall⟩
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        exact .cons (hall x y (by simp))
          (ih ys ⟨by simpa using hlen, fun a b hin => hall a b (by simp [hin])⟩)

theorem Forall2_left_exists {A B} (R : A → B → Prop) (xs : List A) (ys : List B) :
    Forall2 R xs ys → ∀ x, x ∈ xs → ∃ y, y ∈ ys ∧ R x y := by
  intro h
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro x hin
    rcases List.mem_cons.1 hin with rfl | hin
    · exact ⟨_, .head _, hab⟩
    · obtain ⟨y, hy, hxy⟩ := ih x hin; exact ⟨y, .tail _ hy, hxy⟩

theorem Forall2_map_right {A B C} (R : A → C → Prop) (f : B → C) (xs : List A) (ys : List B) :
    Forall2 (fun x y => R x (f y)) xs ys → Forall2 R xs (ys.map f) := by
  intro h
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons hxy ih

theorem map_fst_combine {A B} (xs : List A) (ys : List B) :
    xs.length = ys.length → (xs.zip ys).map Prod.fst = xs :=
  List.map_fst_zip ∘ Nat.le_of_eq

theorem map_snd_combine {A B} (xs : List A) (ys : List B) :
    xs.length = ys.length → (xs.zip ys).map Prod.snd = ys :=
  fun h => List.map_snd_zip (Nat.le_of_eq h.symm)

theorem flat_map_fixed_length {A B} (f : A → List B) (xs : List A) (k : Nat) :
    (∀ x, x ∈ xs → (f x).length = k) → (xs.flatMap f).length = k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro h
    simp only [List.flatMap_cons, List.length_append, List.length_cons, h x (.head _),
      ih fun y hy => h y (.tail _ hy)]
    rw [Nat.mul_succ, Nat.add_comm]

/-- Splitting a pointwise relation across an append needs the prefix lengths. -/
theorem Forall2_app_inv_len {A B} (R : A → B → Prop) (l1 l2 : List A) (l1' l2' : List B) :
    l1.length = l1'.length → Forall2 R (l1 ++ l2) (l1' ++ l2') →
      Forall2 R l1 l1' ∧ Forall2 R l2 l2' := by
  induction l1 generalizing l1' with
  | nil => intro hlen h; cases l1' <;> simp_all
  | cons a l1 ih =>
    intro hlen h
    cases l1' with
    | nil => simp at hlen
    | cons b l1' =>
      simp only [List.cons_append, Forall2_cons_iff] at h
      obtain ⟨h1, h2⟩ := ih l1' (by simpa using hlen) h.2
      exact ⟨.cons h.1 h1, h2⟩

/-! ## Heads of lists that may be empty -/

/-- The head of a possibly-empty list is either the supplied default or an actual member. -/
theorem head_in_or_default {A} (d : A) (xs : List A) : xs.headD d = d ∨ xs.headD d ∈ xs := by
  cases xs <;> simp

theorem head_not_in {A} (d x : A) (xs : List A) : x ∉ xs → d ≠ x → xs.headD d ≠ x := by
  cases xs with
  | nil => simp
  | cons a xs => intro hn _ he; exact hn (he ▸ .head _)

/-! ## Relation-polymorphic linking of a list of nodes

`linked edge nodes last` says consecutive members of `nodes` are related by `edge`, with the final
member related to `last`. The terminator is a parameter, so a client can retarget the last link by
`linked_split` + `linked_app`. -/

/-- Consecutive members are `edge`-related; the final member is related to `last`. -/
def linked {A : Type _} (edge : A → A → Prop) : List A → A → Prop
  | [], _ => True
  | a :: rest, last => edge a (rest.headD last) ∧ linked edge rest last

theorem linked_app {A} (edge : A → A → Prop) (xs ys : List A) (last : A) :
    linked edge xs (ys.headD last) → linked edge ys last → linked edge (xs ++ ys) last := by
  induction xs with
  | nil => intro _ h; exact h
  | cons a xs ih =>
    rintro ⟨ha, hxs⟩ h2
    exact ⟨show edge a ((xs ++ ys).headD last) by rw [hd_app]; exact ha, ih hxs h2⟩

theorem linked_split {A} (edge : A → A → Prop) (xs ys : List A) (last : A) :
    linked edge (xs ++ ys) last → linked edge xs (ys.headD last) ∧ linked edge ys last := by
  induction xs with
  | nil => intro h; exact ⟨trivial, h⟩
  | cons a xs ih =>
    rintro ⟨ha, hrest⟩
    obtain ⟨h1, h2⟩ := ih hrest
    change edge a ((xs ++ ys).headD last) at ha
    rw [hd_app] at ha
    exact ⟨⟨ha, h1⟩, h2⟩

theorem linked_mono {A} (edge edge' : A → A → Prop) (nodes : List A) (last : A) :
    (∀ a b, a ∈ nodes → edge a b → edge' a b) →
      linked edge nodes last → linked edge' nodes last := by
  induction nodes with
  | nil => intros; trivial
  | cons a rest ih =>
    rintro hmono ⟨ha, hrest⟩
    exact ⟨hmono _ _ (.head _) ha, ih (fun x y hx => hmono x y (.tail _ hx)) hrest⟩

/-- Every list-suffix lookup licenses the whole chain at once. -/
theorem linked_of_splits {A} (edge : A → A → Prop) (nodes : List A) (last : A) :
    (∀ pre a rest, nodes = pre ++ a :: rest → edge a (rest.headD last)) →
      linked edge nodes last := by
  induction nodes with
  | nil => intro; trivial
  | cons a rest ih =>
    intro links
    exact ⟨links [] a rest rfl,
      ih fun pre b rest' e => links (a :: pre) b rest' (by simp [e])⟩

theorem linked_of_Forall2 {A} (edge : A → A → Prop) (nodes : List A) (last : A) :
    Forall2 edge nodes (nodes.tail ++ [last]) → linked edge nodes last := by
  induction nodes generalizing last with
  | nil => intro; trivial
  | cons a rest ih =>
    cases rest with
    | nil => intro h; simp only [List.tail_cons, List.nil_append, Forall2_cons_iff] at h
             exact ⟨h.1, trivial⟩
    | cons b rest =>
      intro h
      simp only [List.tail_cons, List.cons_append, Forall2_cons_iff] at h
      exact ⟨h.1, ih last (by simpa using h.2)⟩

/-! ## Small `map`/`range'`/`take` facts used to read windows -/

/-- A window is determined by its pointwise values. -/
theorem map_seq_eq {A} (lo len : Nat) (f : Nat → A) (xs : List A) (d : A) :
    xs.length = len → (∀ i, i < len → f (lo + i) = xs.getD i d) →
      (List.range' lo len).map f = xs := by
  intro hlen hnth
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.length_map, List.length_range'] at h1
  have := hnth i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this
  simp [List.getElem_range', this]

theorem firstn_seq (lo len k : Nat) : k ≤ len → (List.range' lo len).take k = List.range' lo k := by
  induction k generalizing lo len with
  | zero => simp
  | succ k ih =>
    intro hk
    cases len with
    | zero => omega
    | succ len => simp [List.range'_succ, ih (lo + 1) len (by omega)]

theorem map_seq_firstn {A} (f : Nat → A) (lo len k : Nat) :
    k ≤ len → ((List.range' lo len).map f).take k = (List.range' lo k).map f := by
  intro hk; rw [← List.map_take, firstn_seq lo len k hk]

/-! ## Periodic choice sequences

`first :: rest` makes the period nonempty without an arbitrary default for an empty cycle. -/

/-- The `k`-th choice: read from `prefix`, then cycle through `first :: rest`. -/
def periodic_choices {A : Type _} (pre : List A) (first : A) (rest : List A) (k : Nat) : A :=
  if k < pre.length then pre.getD k first
  else (first :: rest).getD ((k - pre.length) % (rest.length + 1)) first

theorem periodic_choices_before {A} (pre : List A) (first : A) (rest : List A) (k : Nat) :
    k < pre.length → periodic_choices pre first rest k = pre.getD k first := by
  intro hk; simp [periodic_choices, hk]

theorem periodic_choices_after {A} (pre : List A) (first : A) (rest : List A) (k : Nat) :
    pre.length ≤ k → periodic_choices pre first rest k =
      (first :: rest).getD ((k - pre.length) % (rest.length + 1)) first := by
  intro hk; simp [periodic_choices, Nat.not_lt.2 hk]

theorem periodic_choices_nth {A} (pre : List A) (first : A) (rest : List A) (j : Nat) :
    periodic_choices pre first rest (pre.length + j) =
      (first :: rest).getD (j % (rest.length + 1)) first := by
  rw [periodic_choices_after _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- The `i`-th choice of any whole round. -/
theorem periodic_choices_round {A} (pre : List A) (first : A) (rest : List A) (rounds i : Nat) :
    i < rest.length + 1 →
    periodic_choices pre first rest (pre.length + rounds * (rest.length + 1) + i) =
      (first :: rest).getD i first := by
  intro hi
  rw [show pre.length + rounds * (rest.length + 1) + i
      = pre.length + (i + rounds * (rest.length + 1)) by omega,
    periodic_choices_nth, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem periodic_prefix_script {A} (pre : List A) (first : A) (rest : List A) :
    (List.range' 0 pre.length).map (periodic_choices pre first rest) = pre :=
  map_seq_eq 0 pre.length _ pre first rfl fun i hi => by
    rw [Nat.zero_add]; exact periodic_choices_before pre first rest i hi

theorem periodic_cycle_script {A} (pre : List A) (first : A) (rest : List A) (rounds : Nat) :
    (List.range' (pre.length + rounds * (rest.length + 1)) (rest.length + 1)).map
        (periodic_choices pre first rest) = first :: rest :=
  map_seq_eq _ (rest.length + 1) _ (first :: rest) first (by simp) fun i hi =>
    periodic_choices_round pre first rest rounds i hi

theorem nth_error_combine_some {A B : Type _} (l : List A) (l' : List B) (k : Nat) (x : A)
    (y : B) : l[k]? = some x → l'[k]? = some y → (l.zip l')[k]? = some (x, y) := by
  intro h h'; simp [List.getElem?_zip_eq_some, h, h']

theorem filter_firstn_lt {A : Type _} (p : A → Bool) (l : List A) (k : Nat) (x : A) :
    l[k]? = some x → p x = true → ((l.take k).filter p).length < (l.filter p).length := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => intro hn hp; simp at hn; subst hn; simp [hp]
    | succ k =>
      intro hn hp; simp only [List.getElem?_cons_succ] at hn
      have := ih k hn hp
      simp only [List.take_succ_cons, List.filter_cons]; split <;> simp <;> omega

theorem Forall2_firstn {A B : Type _} (R : A → B → Prop) (k : Nat) (l : List A) (l' : List B) :
    Forall2 R l l' → Forall2 R (l.take k) (l'.take k) := by
  intro h
  induction h generalizing k with
  | nil => simp only [List.take_nil]; exact .nil
  | cons hxy _ ih =>
    cases k with
    | zero => exact .nil
    | succ k => exact .cons hxy (ih k)

/-- Number of `p`-elements among the first `k` entries of `l`. -/
def rank {A : Type _} (p : A → Bool) (l : List A) (k : Nat) : Nat :=
  ((l.take k).filter p).length

theorem nth_error_rank {A : Type _} (p : A → Bool) (l : List A) (k : Nat) (y : A) :
    l[k]? = some y → p y = true → (l.filter p)[rank p l k]? = some y := by
  unfold rank
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    intro h hy
    cases k with
    | zero => simp at h; subst h; simp [hy]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      by_cases ha : p a = true
      · simp [ha, ih k h hy]
      · simp [ha, ih k h hy]

theorem rank_inv {A : Type _} (p : A → Bool) (l : List A) (r : Nat) (y : A) :
    (l.filter p)[r]? = some y → ∃ k, l[k]? = some y ∧ p y = true ∧ rank p l k = r := by
  unfold rank
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
    intro h
    by_cases ha : p a = true
    · simp only [List.filter_cons, ha, ite_true] at h
      cases r with
      | zero => simp at h; subst h; exact ⟨0, by simp, ha, by simp⟩
      | succ r =>
        obtain ⟨k, hk, hy, hr⟩ := ih r (by simpa using h)
        exact ⟨k + 1, by simpa using hk, hy, by simp [ha, hr]⟩
    · simp only [List.filter_cons, ha] at h
      obtain ⟨k, hk, hy, hr⟩ := ih r (by simpa using h)
      exact ⟨k + 1, by simpa using hk, hy, by simp [ha, hr]⟩

theorem list_cut {A : Type _} (l : List A) (k : Nat) (x : A) :
    l[k]? = some x → ∃ pre post, l = pre ++ x :: post ∧ pre.length = k := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    intro h
    cases k with
    | zero => simp at h; subst h; exact ⟨[], l, rfl, rfl⟩
    | succ k =>
      obtain ⟨pre, post, rfl, hl⟩ := ih k (by simpa using h)
      exact ⟨a :: pre, post, rfl, by simp [hl]⟩

theorem firstn_cut {A : Type _} (pre post : List A) : (pre ++ post).take pre.length = pre := by
  simp

end Tisl
