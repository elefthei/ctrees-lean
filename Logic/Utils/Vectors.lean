/- SPDX-License-Identifier: MIT -/
module

/-!
# Vector and finite-index utilities

`Vector.cons` (missing from core), slot arithmetic on `Fin`, pointwise lemmas for removal/update,
index enumerations and small list helpers used by the thread-pool scheduler (← `Utils/Vectors.v`).
-/

@[expose] public section

/-- Prepend an element to a vector (Rocq `x :: v`). -/
def Vector.cons {α : Type _} {n : Nat} (x : α) (v : Vector α n) : Vector α (n + 1) :=
  ⟨#[x] ++ v.toArray, by simp [Nat.add_comm]⟩

@[simp] theorem Vector.getElem_cons_zero {α : Type _} {n : Nat} (x : α) (v : Vector α n) :
    (Vector.cons x v)[0] = x := by
  simp [Vector.cons]

@[simp] theorem Vector.getElem_cons_succ {α : Type _} {n : Nat} (x : α) (v : Vector α n) (i : Nat)
    (h : i + 1 < n + 1) : (Vector.cons x v)[i + 1] = v[i] := by
  simp [Vector.cons, Array.getElem_append_right]

namespace Tisl

universe u v

/-- The last slot of `Fin (n+1)`. -/
def fin_max (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

@[simp] theorem fin_max_sanity {n : Nat} : (fin_max n).val = n := rfl

/-- The numeric index of a finite slot. -/
abbrev slot_index {n : Nat} (j : Fin n) : Nat := j.val

theorem fin1_eq (a : Fin 1) : a = 0 := Fin.ext (by omega)

/-- The successor slot of `p < n`, in `Fin (n+1)` (Rocq `FS (of_nat_lt H)`). -/
def of_nat_lt' {n p : Nat} (H : p < n) : Fin (n + 1) := (⟨p, H⟩ : Fin n).succ

/-- Drop the head of a nonempty vector (Rocq `init`, which is the tail). -/
def init {T : Type u} {n : Nat} (v : Vector T (n + 1)) : Vector T n := v.tail

/-- Remove slot `i` (Rocq `v -- i`). -/
abbrev vector_remove {A : Type u} {n : Nat} (v : Vector A (n + 1)) (i : Fin (n + 1)) :
    Vector A n :=
  v.eraseIdx i i.isLt

theorem vector_remove_getElem {A : Type u} {n : Nat} (v : Vector A (n + 1)) (i : Fin (n + 1))
    (j : Fin n) : (vector_remove v i)[j] = if j.val < i.val then v[j.val] else v[j.val + 1] := by
  rw [Fin.getElem_fin, Vector.getElem_eraseIdx]; rfl

/-- Removing the head slot keeps the tail unchanged. -/
theorem vector_remove_head {A : Type u} {n : Nat} (x : A) (v : Vector A n) :
    vector_remove (Vector.cons x v) 0 = v := by
  ext j hj
  have := vector_remove_getElem (Vector.cons x v) 0 ⟨j, hj⟩
  simp_all

/-- Removing a non-head slot keeps the head and recurses on the tail. -/
theorem vector_remove_tail {A : Type u} {n : Nat} (x : A) (v : Vector A (n + 1))
    (i : Fin (n + 1)) :
    vector_remove (Vector.cons x v) i.succ = Vector.cons x (vector_remove v i) := by
  ext j hj
  have h1 := vector_remove_getElem (Vector.cons x v) i.succ ⟨j, hj⟩
  simp only [Fin.getElem_fin] at h1
  rw [h1]
  cases j with
  | zero => simp
  | succ j =>
    have h2 := vector_remove_getElem v i ⟨j, by omega⟩
    simp only [Fin.getElem_fin] at h2
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right, Vector.getElem_cons_succ, h2]

/-- Removing the last slot of a literal pair. -/
theorem vector_remove_pair {A : Type u} (x y : A) : vector_remove #v[x, y] 1 = #v[x] :=
  (vector_remove_tail x #v[y] 0).trans (congrArg (Vector.cons x) (vector_remove_head y #v[]))

/-- Removing the only slot of a literal singleton. -/
theorem vector_remove_single {A : Type u} (x : A) : vector_remove #v[x] 0 = #v[] :=
  vector_remove_head x #v[]

/-- `vector_remove` forgets an update of the removed slot. -/
theorem vector_remove_replace {A : Type u} {n : Nat} (v : Vector A (n + 1)) (j : Fin (n + 1))
    (x : A) : vector_remove (v.set j x) j = vector_remove v j := by
  show (v.set j x).eraseIdx j = v.eraseIdx j
  ext i hi
  simp only [Vector.getElem_eraseIdx]
  split <;> rw [Vector.getElem_set_ne] <;> simp <;> omega

/-- Pointwise agreement away from the removed slot survives the removal. -/
theorem vector_remove_pointwise {A : Type u} {n : Nat} (R : A → A → Prop)
    (v1 v2 : Vector A (n + 1)) (i : Fin (n + 1)) (h : ∀ j, i ≠ j → R v1[j] v2[j]) :
    ∀ j : Fin n, R (vector_remove v1 i)[j] (vector_remove v2 i)[j] := by
  intro j
  rw [vector_remove_getElem, vector_remove_getElem]
  split
  · exact h ⟨j, by omega⟩ (fun e => by have := congrArg Fin.val e; simp at this; omega)
  · exact h ⟨j + 1, by omega⟩ (fun e => by have := congrArg Fin.val e; simp at this; omega)

/-- Updating related vectors preserves their relation at every slot. -/
theorem vector_replace_pointwise {A : Type u} {n : Nat} (R : A → A → Prop) (v1 v2 : Vector A n)
    (i : Fin n) (x1 x2 : A) (h : ∀ j, i ≠ j → R v1[j] v2[j]) (hx : R x1 x2) :
    ∀ j : Fin n, R (v1.set i x1)[j] (v2.set i x2)[j] := by
  intro j
  by_cases e : i = j
  · subst e; simpa using hx
  · have ne : i.val ≠ j.val := fun h' => e (Fin.ext h')
    simp only [Fin.getElem_fin, Vector.getElem_set_ne _ _ ne]
    exact h j e

theorem vector_cons_pointwise {A : Type u} {n : Nat} (R : A → A → Prop) (x1 x2 : A)
    (v1 v2 : Vector A n) (hx : R x1 x2) (hv : ∀ j : Fin n, R v1[j] v2[j]) :
    ∀ i : Fin (n + 1), R (Vector.cons x1 v1)[i] (Vector.cons x2 v2)[i] := by
  intro i
  cases i using Fin.cases with
  | zero => simpa using hx
  | succ j => simpa using hv j

/-- Apply `f` at slot `i` (Rocq `v @ i do f`). -/
def nth_map {A : Type u} {n : Nat} (v : Vector A n) (i : Fin n) (f : A → A) : Vector A n :=
  v.set i (f v[i])

/-- Boolean conjunction of `f` over a vector. -/
def forallb {A : Type u} {m : Nat} (f : A → Bool) (a : Vector A m) : Bool := a.all f

theorem forall_reflect {A : Type u} {m : Nat} (f : A → Bool) (l : Vector A m) :
    forallb f l = true ↔ ∀ x ∈ l, f x = true := by
  simp only [forallb, Vector.all_eq_true, Vector.mem_iff_getElem]
  constructor
  · rintro h x ⟨i, hi, rfl⟩; exact h i hi
  · intro h i hi; exact h _ ⟨i, hi, rfl⟩

/-- `some` of the values when every slot is `some`, otherwise `none`. -/
def seq_opt {n : Nat} {X : Type u} (v : Vector (Option X) (n + 1)) : Option (Vector X (n + 1)) :=
  v.mapM id

/-- A nonempty vector of `n+1` copies of `a`. -/
def vector_repeat {A : Type u} (n : Nat) (a : A) : Vector A (n + 1) := Vector.replicate (n + 1) a

/-- All slots of `Fin n`, in increasing order. -/
def fin_all (n : Nat) : List (Fin n) := List.finRange n

/-- Rocq's `fin_all_v`, copied literally: its head is slot `1`, not `0`
(`fin_all_v 1 = #v[1, 1]`). -/
def fin_all_v : (n : Nat) → Vector (Fin (n + 1)) (n + 1)
  | 0 => #v[0]
  | n + 1 => Vector.cons (Fin.succ 0) ((fin_all_v n).map Fin.succ)

theorem fin_all_In {n : Nat} (f : Fin n) : f ∈ fin_all n := List.mem_finRange f

theorem fin_case (n : Nat) (f : Fin (n + 1)) : f = 0 ∨ ∃ f', f = Fin.succ f' := by
  cases f using Fin.cases with
  | zero => exact .inl rfl
  | succ f' => exact .inr ⟨f', rfl⟩

/-- Pointwise pairing of two vectors. -/
def zip {A : Type u} {B : Type v} {n : Nat} (a : Vector A n) (b : Vector B n) :
    Vector (A × B) n :=
  a.zip b

/-- `R` holds between the slots of `a` and `b`. -/
def pairwise {A : Type u} {B : Type v} {n : Nat} (R : A → B → Prop) (a : Vector A n)
    (b : Vector B n) : Prop :=
  ∀ p ∈ zip a b, R p.1 p.2

theorem inversion_0 {A : Type u} (v : Vector A 0) : v = #v[] := Vector.eq_empty

theorem inversion_Sn {A : Type u} {n : Nat} (v : Vector A (n + 1)) :
    ∃ a b, v = Vector.cons a b := by
  refine ⟨v[0], init v, ?_⟩
  ext i hi
  cases i with
  | zero => simp
  | succ i => simp [init, Nat.add_comm]

/-- The last element of a list. -/
def list_last {A : Type u} : List A → Option A
  | [] => none
  | [h] => some h
  | _ :: ts => list_last ts

/-- Split a nonempty list into its last element and the prefix. -/
def list_unsnoc {A : Type u} : List A → Option (A × List A)
  | [] => none
  | h :: ts =>
    match list_unsnoc ts with
    | some (h', ts') => some (h', h :: ts')
    | none => some (h, [])

/-- Coerce the `p`-th slot of `Fin m` to the `p`-th slot of `Fin (m+1)`. -/
def SL {m : Nat} (p : Fin m) : Fin (m + 1) := p.castSucc

theorem SL_sanity {m : Nat} (p : Fin m) : (SL p).val = p.val := rfl

/-- Indices of the slots of `v` satisfying `p`, labelled downward from `f` (Rocq recursion). -/
def filter_to_indices' {N M : Nat} {T : Type u} (p : T → Bool) (v : Vector T (N + 1))
    (f : Fin (M + 1)) : List (Fin (M + 1)) :=
  match N, v, f with
  | _, v, ⟨0, h⟩ => if p v[0] then [⟨0, h⟩] else []
  | 0, v, ⟨j + 1, h⟩ => if p v[0] then [⟨j + 1, h⟩] else []
  | _ + 1, v, ⟨j + 1, h⟩ =>
    let rest := filter_to_indices' p (init v) (SL (⟨j, by omega⟩ : Fin M))
    if p v[0] then ⟨j + 1, h⟩ :: rest else rest

/-- The length of a vector as the last slot of `Fin (n+1)`. -/
def length_vec {n : Nat} {T : Type u} (_ : Vector T n) : Fin (n + 1) := Fin.last n

/-- Indices of the slots of `v` satisfying `p`, in descending order. -/
def filter_to_indices {N : Nat} {T : Type u} (v : Vector T N) (p : T → Bool) : List (Fin N) :=
  match N, v with
  | 0, _ => []
  | _ + 1, v => filter_to_indices' p v.reverse (length_vec (init v))

/-- Total indexing into `h :: ts`. -/
def safe_nth {T : Type u} (h : T) : (ts : List T) → Fin (ts.length + 1) → T
  | _, ⟨0, _⟩ => h
  | x :: ts', ⟨k + 1, hk⟩ => safe_nth x ts' ⟨k, by simp at hk; omega⟩

theorem vector_to_list_length {A : Type _} {n : Nat} (v : Vector A n) : v.toList.length = n := by
  simp

theorem vector_to_list_nth_error {A : Type _} {n : Nat} (v : Vector A n) (j : Fin n) :
    v.toList[j.val]? = some v[j] := by
  simp

example : fin_all_v 1 = #v[1, 1] := by decide +kernel
example : filter_to_indices #v[1, 0, 3] (· != 0) = [2, 0] := by decide +kernel

end Tisl

-- Not ported: `vec`, `vec'`, `fin`, `fin'` abbreviations (core `Vector`/`Fin`; `fin'` is defined in
-- `Logic/CTree/Core.lean`); notations `v $ i`, `v -- i`, `v @ i do f`, `v @ i := x` (use `v[i]`,
-- `vector_remove`, `nth_map`, `v.set i x`); `inversion_aux` (helper of `inversion_0/Sn`, proved
-- directly).
