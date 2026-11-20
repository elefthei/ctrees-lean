/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.Pcm
public import Logic.Utils.Lists

/-!
# The concrete heap model

Heaps `Nat → Option Nat` with pointwise equivalence `heq` and union defined on disjoint pairs (the
`HeapPCM` instance), the update primitive `upd` and chronological writes, finite blocks,
allocation tables with managed alloc/free and their framing laws, and the stride-two node geometry
shared by queues and allocators (← `Events/HeapModel.v`). Heap equality stays pointwise.
-/

@[expose] public section
namespace Tisl.Heap
open Tisl.Pcm

/-! ## Carrier and primitive operations -/

abbrev Heap := Nat → Option Nat

def hemp : Heap := fun _ => none
def heq (h1 h2 : Heap) : Prop := ∀ a, h1 a = h2 a
def hdisj (h1 h2 : Heap) : Prop := ∀ a, h1 a = none ∨ h2 a = none
def hunion (h1 h2 : Heap) : Heap :=
  fun a => match h1 a with | some v => some v | none => h2 a

def hsingle (a v : Nat) : Heap := fun b => if a = b then some v else none
def hfree (a : Nat) (h : Heap) : Heap := fun b => if a = b then none else h b

/-- A singleton heap contains its own cell. -/
theorem hsingle_eq (i a : Nat) : hsingle i a i = some a := by simp [hsingle]

/-- A singleton heap is empty at any distinct address. -/
theorem hsingle_neq (i j a : Nat) : i ≠ j → hsingle i a j = none := fun h => by
  simp [hsingle, h]

/-- Singletons at distinct addresses are disjoint. -/
theorem hsingle_disj (a b v w : Nat) : a ≠ b → hdisj (hsingle a v) (hsingle b w) := fun Hab x =>
  if h : a = x then .inr (h ▸ hsingle_neq b a w (Ne.symm Hab)) else .inl (hsingle_neq a x v h)

/-- The single update primitive, deciding on the looked-up address. -/
def upd (h : Heap) (a v : Nat) : Heap := fun x => if x = a then some v else h x

/-- The empty heap has no allocated cell. -/
theorem hemp_dom (x : Nat) : hemp x ≠ none → False := fun h => h rfl

/-- Pointwise contents of a finite collection of heap cells. -/
def cellsat (W : List (Nat × Nat)) (h : Heap) : Prop := ∀ p ∈ W, h p.1 = some p.2

theorem cellsat_heq (W : List (Nat × Nat)) (h1 h2 : Heap) :
    heq h1 h2 → cellsat W h1 → cellsat W h2 :=
  fun he H p hp => he p.1 ▸ H p hp

theorem cellsat_agree (W : List (Nat × Nat)) (h h' : Heap) :
    (∀ p ∈ W, h' p.1 = h p.1) → cellsat W h → cellsat W h' :=
  fun hag H p hp => (hag p hp).trans (H p hp)

theorem hdisj_none (h1 h2 : Heap) (a v : Nat) : hdisj h1 h2 → h1 a = some v → h2 a = none :=
  fun hd hs => (hd a).resolve_left (by simp [hs])

/-! ## The algebra of `upd` -/

theorem upd_unfold (h : Heap) (a v x : Nat) : upd h a v x = if x = a then some v else h x := rfl

@[simp] theorem upd_eq (h : Heap) (a v : Nat) : upd h a v a = some v := by simp [upd]

theorem upd_neq (h : Heap) (a v x : Nat) : x ≠ a → upd h a v x = h x := by
  intro hx; simp [upd, hx]

theorem upd_mono (h : Heap) (a v x : Nat) : h x ≠ none → upd h a v x ≠ none := by
  intro hx; unfold upd; split <;> simp_all

theorem upd_dom (h : Heap) (a v x : Nat) : h a ≠ none → (upd h a v x ≠ none ↔ h x ≠ none) := by
  intro ha; unfold upd; split <;> simp_all

theorem upd_lookup_agree (h f : Heap) (a v x : Nat) : h x = f x → upd h a v x = upd f a v x := by
  intro hx; simp [upd, hx]

theorem upd_heq (h k : Heap) (a v : Nat) : heq h k → heq (upd h a v) (upd k a v) :=
  fun hk x => upd_lookup_agree h k a v x (hk x)

/-- Chronological writes: the pure result keeps the last value written to each key. -/
def apply_writes : List (Nat × Nat) → Heap → Heap
  | [], h => h
  | (a, v) :: rest, h => apply_writes rest (upd h a v)

@[simp] theorem apply_writes_cons (a v : Nat) (ws : List (Nat × Nat)) (h : Heap) :
    apply_writes ((a, v) :: ws) h = apply_writes ws (upd h a v) := rfl

theorem apply_writes_app (xs ys : List (Nat × Nat)) (h : Heap) :
    apply_writes (xs ++ ys) h = apply_writes ys (apply_writes xs h) := by
  induction xs generalizing h with
  | nil => rfl
  | cons p xs ih => obtain ⟨a, v⟩ := p; exact ih _

theorem apply_writes_lookup (ws : List (Nat × Nat)) (h : Heap) (a : Nat) :
    apply_writes ws h a =
      match ws.reverse.find? (fun av => a == av.1) with
      | some (_, v) => some v
      | none => h a := by
  induction ws generalizing h with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨b, v⟩ := p
    rw [apply_writes_cons, ih, List.reverse_cons, List.find?_append]
    cases ws.reverse.find? (fun av => a == av.1) with
    | some q => rfl
    | none => by_cases hab : a = b <;> simp [hab, upd]

theorem apply_writes_rev_lookup (ws : List (Nat × Nat)) (h : Heap) (a : Nat) :
    apply_writes ws.reverse h a =
      match ws.find? (fun av => a == av.1) with
      | some (_, v) => some v
      | none => h a := by
  rw [apply_writes_lookup, List.reverse_reverse]

theorem apply_writes_outside (ws : List (Nat × Nat)) (h : Heap) (a : Nat) :
    a ∉ ws.map Prod.fst → apply_writes ws h a = h a := by
  induction ws generalizing h with
  | nil => intro; rfl
  | cons p ws ih =>
    obtain ⟨b, v⟩ := p
    intro hout
    simp only [List.map_cons, List.mem_cons, not_or] at hout
    rw [apply_writes_cons, ih _ hout.2, upd_neq _ _ _ _ hout.1]

theorem apply_writes_allocated (ws : List (Nat × Nat)) (h : Heap) (a : Nat) :
    h a ≠ none → apply_writes ws h a ≠ none := by
  induction ws generalizing h with
  | nil => exact id
  | cons p ws ih => obtain ⟨b, v⟩ := p; exact fun H => ih _ (upd_mono _ _ _ _ H)

theorem apply_writes_dom_exact (ws : List (Nat × Nat)) (h : Heap) (a : Nat) :
    apply_writes ws h a ≠ none ↔ a ∈ ws.map Prod.fst ∨ h a ≠ none := by
  induction ws generalizing h with
  | nil => simp [apply_writes]
  | cons p ws ih =>
    obtain ⟨b, v⟩ := p
    rw [apply_writes_cons, ih]
    by_cases hab : a = b <;> simp [hab, upd]

theorem apply_writes_dom (ws : List (Nat × Nat)) (h : Heap) (a : Nat) :
    (∀ x v, (x, v) ∈ ws → h x ≠ none) → (apply_writes ws h a ≠ none ↔ h a ≠ none) := by
  intro hall
  rw [apply_writes_dom_exact]
  refine ⟨fun H => H.elim (fun hin => ?_) id, Or.inr⟩
  obtain ⟨⟨x, v⟩, hmem, rfl⟩ := List.mem_map.1 hin
  exact hall x v hmem

theorem apply_writes_lookup_agree (ws : List (Nat × Nat)) (h f : Heap) (a : Nat) :
    h a = f a → apply_writes ws h a = apply_writes ws f a := by
  intro H
  rw [apply_writes_lookup, apply_writes_lookup]
  split <;> simp_all

theorem apply_writes_contents (ws : List (Nat × Nat)) (h : Heap) (a v : Nat) :
    (ws.map Prod.fst).Nodup → (a, v) ∈ ws → apply_writes ws h a = some v := by
  induction ws generalizing h with
  | nil => simp
  | cons p ws ih =>
    obtain ⟨b, u⟩ := p
    intro hnd hin
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [apply_writes_cons]
    rcases List.mem_cons.1 hin with he | hin
    · cases he; rw [apply_writes_outside _ _ _ hnd.1, upd_eq]
    · exact ih _ hnd.2 hin

private theorem nodup_reverse {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup :=
  List.pairwise_reverse.2 (h.imp Ne.symm)

theorem apply_writes_rev (ws : List (Nat × Nat)) (h : Heap) :
    (ws.map Prod.fst).Nodup → heq (apply_writes ws.reverse h) (apply_writes ws h) := by
  intro hnd a
  by_cases hin : a ∈ ws.map Prod.fst
  · obtain ⟨⟨b, v⟩, hmem, rfl⟩ := List.mem_map.1 hin
    rw [apply_writes_contents ws h b v hnd hmem]
    exact apply_writes_contents _ _ _ _ (by rw [List.map_reverse]; exact nodup_reverse hnd)
      (List.mem_reverse.2 hmem)
  · rw [apply_writes_outside _ _ _ hin,
      apply_writes_outside _ _ _ (by rw [List.map_reverse, List.mem_reverse]; exact hin)]

/-! Elementary lookup consequences of `hunion`/`hdisj`. -/

theorem hunion_some (h f : Heap) (x v : Nat) : h x = some v → hunion h f x = some v := by
  intro H; simp [hunion, H]

theorem hunion_eq (h f : Heap) (x : Nat) : h x ≠ none → hunion h f x = h x := by
  intro H; cases hx : h x with
  | none => exact absurd hx H
  | some v => exact hunion_some _ _ _ _ hx

theorem hunion_none (h f : Heap) (x : Nat) : h x = none → hunion h f x = f x := by
  intro H; simp [hunion, H]

theorem hunion_dom (h f : Heap) (x : Nat) : h x ≠ none → hunion h f x ≠ none := by
  intro H; rwa [hunion_eq _ _ _ H]

theorem hunion_null (h f : Heap) : h 0 = none → f 0 = none → hunion h f 0 = none := by
  intro hh hf; rw [hunion_none _ _ _ hh, hf]

theorem hdisj_union (h1 h2 f : Heap) :
    hdisj h1 h2 → hdisj h1 f → hdisj h1 (hunion h2 f) := by
  intro h12 h1f x
  rcases h12 x with h | h
  · exact Or.inl h
  · rcases h1f x with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [hunion_none _ _ _ h, h'])

/-! The PCM laws, as standalone lemmas. -/

theorem heq_refl (a : Heap) : heq a a := fun _ => rfl

theorem heq_sym (a b : Heap) : heq a b → heq b a := fun h x => (h x).symm

theorem heq_trans (a b c : Heap) : heq a b → heq b c → heq a c := fun h h' x => (h x).trans (h' x)

theorem hdisj_resp (a a' b b' : Heap) : heq a a' → heq b b' → hdisj a b → hdisj a' b' := by
  intro ha hb hd x; rw [← ha, ← hb]; exact hd x

theorem hunion_resp (a a' b b' : Heap) : heq a a' → heq b b' → heq (hunion a b) (hunion a' b') := by
  intro ha hb x; simp only [hunion, ha x, hb x]

theorem hdisj_sym (a b : Heap) : hdisj a b → hdisj b a := fun hd x => (hd x).symm

theorem hunion_comm (a b : Heap) : hdisj a b → heq (hunion a b) (hunion b a) := by
  intro hd x; rcases hd x with h | h <;> simp only [hunion, h] <;> split <;> simp_all

theorem hdisj_hemp (a : Heap) : hdisj hemp a := fun _ => Or.inl rfl

theorem hunion_hemp (a : Heap) : heq (hunion hemp a) a := fun _ => rfl

theorem hdisj_assocL (a b c : Heap) : hdisj b c → hdisj a (hunion b c) → hdisj a b := by
  intro _ ha x; have := ha x; simp only [hunion] at this; split at this <;> simp_all

theorem hdisj_assocR (a b c : Heap) : hdisj b c → hdisj a (hunion b c) → hdisj (hunion a b) c := by
  intro hbc ha x; have h1 := ha x; have h2 := hbc x
  simp only [hunion] at *; split <;> split at h1 <;> simp_all

theorem hdisj_assocI (a b c : Heap) :
    hdisj b c → hdisj a b → hdisj (hunion a b) c → hdisj a (hunion b c) := by
  intro hbc hab habc x; have h1 := hbc x; have h2 := hab x; have h3 := habc x
  simp only [hunion] at *; split <;> split at h3 <;> simp_all

theorem hunion_assoc (a b c : Heap) :
    hdisj b c → hdisj a (hunion b c) → heq (hunion a (hunion b c)) (hunion (hunion a b) c) := by
  intro _ _ x; simp only [hunion]; cases a x <;> rfl

instance HeapPCM : PCM Heap where
  peq := heq
  pdef := hdisj
  pop := hunion
  pemp := hemp
  peq_refl := heq_refl
  peq_sym := heq_sym
  peq_trans := heq_trans
  pdef_resp := hdisj_resp
  pop_resp := hunion_resp
  pdef_comm := hdisj_sym
  pop_comm := hunion_comm
  pdef_emp := hdisj_hemp
  pop_emp := hunion_hemp
  pdef_assocL := hdisj_assocL
  pdef_assocR := hdisj_assocR
  pdef_assocI := hdisj_assocI
  pop_assoc := hunion_assoc

/-- Heaps are cancellative: the class is not weakened by leaving cancellativity out. -/
theorem HeapCancellative : Cancellative Heap := by
  intro a b c hab hac he x
  have h1 := he x; have h2 := hab x; have h3 := hac x
  change hunion a b x = hunion a c x at h1
  simp only [hunion] at h1; split at h1 <;> simp_all

/-! ## Points-to, and the separation it buys -/

/-- `pto a v` is an assertion about the *owned* resource. -/
def pto (a v : Nat) : assn Heap := fun h => heq h (hsingle a v)

theorem pto_proper (a v : Nat) : AProper (pto a v) :=
  fun _ _ he hp x => (he x).symm.trans (hp x)

theorem pto_lookup (a v : Nat) (h : Heap) : pto a v h → h a = some v := by
  intro hp; rw [hp a]; simp [hsingle]

/-- Two points-to on the same address cannot be separated. -/
theorem pto_sep_same_false (a v v' : Nat) (h : Heap) : ¬ (pto a v ⋆ pto a v') h := by
  rintro ⟨h1, h2, hd, -, H1, H2⟩
  have := pto_lookup _ _ _ H1; have := pto_lookup _ _ _ H2
  rcases hd a with h | h <;> simp_all

/-- Distinct addresses do separate. -/
theorem pto_sep_distinct (a b v v' : Nat) :
    a ≠ b → (pto a v ⋆ pto b v') (hunion (hsingle a v) (hsingle b v')) := by
  intro hab
  refine ⟨hsingle a v, hsingle b v', fun x => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  simp only [hsingle]; by_cases h : a = x <;> by_cases h' : b = x <;> simp_all

/-! ## Safe-access locality on the concrete heap -/

/-- A read inside the owned footprint returns the owned value under every compatible frame. -/
theorem read_local (h f : Heap) (a v : Nat) : hdisj h f → h a = some v → hunion h f a = some v :=
  fun _ => hunion_some h f a v

/-- A write inside the owned footprint keeps the frame disjoint ... -/
theorem write_local_disj (h f : Heap) (a v v0 : Nat) :
    hdisj h f → h a = some v0 → hdisj (upd h a v) f := by
  intro hd ha x
  by_cases hx : x = a
  · subst hx; exact Or.inr (hdisj_none _ _ _ _ hd ha)
  · rw [upd_neq _ _ _ _ hx]; exact hd x

/-- ... and commutes with framing. -/
theorem write_local_frame (h f : Heap) (a v : Nat) :
    heq (upd (hunion h f) a v) (hunion (upd h a v) f) := by
  intro x
  by_cases hx : x = a
  · subst hx; simp [hunion]
  · simp [upd, hunion, hx]

/-- A free inside the owned footprint keeps the frame disjoint ... -/
theorem free_local_disj (h f : Heap) (a : Nat) : hdisj h f → hdisj (hfree a h) f := by
  intro hd x; simp only [hfree]; split
  · exact Or.inl rfl
  · exact hd x

/-- ... and commutes with framing, provided the address is owned. -/
theorem free_local_frame (h f : Heap) (a v0 : Nat) :
    hdisj h f → h a = some v0 → heq (hfree a (hunion h f)) (hunion (hfree a h) f) := by
  intro hd ha x
  simp only [hfree, hunion]
  by_cases hx : a = x
  · subst hx; simp [hdisj_none _ _ _ _ hd ha]
  · simp [hx]

/-- Freeing an absent address leaves the heap pointwise unchanged. -/
theorem hfree_absent_noop (h : Heap) (a : Nat) : h a = none → heq (hfree a h) h := by
  intro ha x; simp only [hfree]; split <;> simp_all

/-! ## Finite blocks over the unrestricted function heap -/

def heap_bounded (bound : Nat) (h : Heap) : Prop := ∀ x, bound ≤ x → h x = none
def heap_finite (h : Heap) : Prop := ∃ bound, heap_bounded bound h
def hblock (base size : Nat) : Heap :=
  fun x => if base ≤ x ∧ x < base + size then some 0 else none
def block_free (h : Heap) (base size : Nat) : Prop :=
  ∀ offset, offset < size → h (base + offset) = none
def block_pto (base size : Nat) : Heap → Prop := fun h => heq h (hblock base size)

theorem hblock_in (base size offset : Nat) :
    offset < size → hblock base size (base + offset) = some 0 := by
  intro h; simp only [hblock]; split <;> first | rfl | omega

theorem hblock_out (base size x : Nat) :
    (x < base ∨ base + size ≤ x) → hblock base size x = none := by
  intro h; simp only [hblock]; split <;> first | rfl | omega

theorem block_free_disjoint (h : Heap) (base size : Nat) :
    block_free h base size ↔ hdisj (hblock base size) h := by
  constructor
  · intro H x
    by_cases hx : base ≤ x ∧ x < base + size
    · refine Or.inr ?_
      have := H (x - base) (by omega)
      rwa [Nat.add_sub_cancel' hx.1] at this
    · exact Or.inl (hblock_out _ _ _ (by omega))
  · intro H offset ho
    have := H (base + offset)
    rw [hblock_in _ _ _ ho] at this
    simpa using this

theorem heap_finite_hemp : heap_finite hemp := ⟨0, fun _ _ => rfl⟩

theorem heap_finite_hblock (base size : Nat) : heap_finite (hblock base size) :=
  ⟨base + size, fun _ h => hblock_out _ _ _ (Or.inr h)⟩

theorem heap_finite_hunion (h f : Heap) :
    heap_finite h → heap_finite f → heap_finite (hunion h f) := by
  rintro ⟨B, hB⟩ ⟨C, hC⟩
  refine ⟨max B C, fun x hx => ?_⟩
  rw [hunion_none _ _ _ (hB x (by omega)), hC x (by omega)]

theorem heap_finite_upd (h : Heap) (a v : Nat) : heap_finite h → heap_finite (upd h a v) := by
  rintro ⟨B, hB⟩
  refine ⟨max B (a + 1), fun x hx => ?_⟩
  rw [upd_neq _ _ _ _ (by omega), hB x (by omega)]

theorem apply_writes_finite (ws : List (Nat × Nat)) (h : Heap) :
    heap_finite h → heap_finite (apply_writes ws h) := by
  induction ws generalizing h with
  | nil => exact id
  | cons p ws ih => obtain ⟨a, v⟩ := p; exact fun H => ih _ (heap_finite_upd _ _ _ H)

theorem heap_bounded_block_free (bound : Nat) (h : Heap) (base size : Nat) :
    heap_bounded bound h → bound ≤ base → block_free h base size :=
  fun H hb offset _ => H _ (by omega)

theorem allocated_block_sep (base size : Nat) (h : Heap) (P : Heap → Prop) :
    block_free h base size → P h → asep (block_pto base size) P (hunion (hblock base size) h) :=
  fun F H => ⟨hblock base size, h, (block_free_disjoint _ _ _).1 F, heq_refl _, heq_refl _, H⟩

/-- An owned block cannot be separated from a points-to on one of its cells. -/
theorem block_pto_overlap_false (base size a v : Nat) (h : Heap) :
    base ≤ a ∧ a < base + size → ¬ asep (block_pto base size) (pto a v) h := by
  rintro ha ⟨b, p, D, -, B, P⟩
  have hb : b a = some 0 := by
    rw [B a]; have := hblock_in base size (a - base) (by omega)
    rwa [Nat.add_sub_cancel' ha.1] at this
  have := pto_lookup _ _ _ P
  rcases D a with h | h <;> simp_all

/-- The executable block-free test on an immutable snapshot. -/
def block_freeb (h : Heap) (base : Nat) : Nat → Bool
  | 0 => true
  | rest + 1 =>
    match h base with
    | none => block_freeb h (base + 1) rest
    | some _ => false

theorem block_freeb_spec (h : Heap) (base size : Nat) :
    block_freeb h base size = true ↔ block_free h base size := by
  induction size generalizing base with
  | zero => exact ⟨fun _ _ ho => absurd ho (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ size ih =>
    simp only [block_freeb]
    cases hb : h base with
    | some v =>
      refine ⟨Bool.noConfusion, fun F => ?_⟩
      have := F 0 (by omega); simp_all
    | none =>
      simp only [ih]
      constructor
      · intro F offset ho
        cases offset with
        | zero => exact hb
        | succ o => have := F o (by omega); rwa [Nat.add_right_comm, Nat.add_assoc] at this
      · intro F offset ho
        have := F (offset + 1) (by omega); rwa [← Nat.add_assoc, Nat.add_right_comm] at this

/-! ## Allocation provenance

A managed heap pairs the data heap with an allocation table recording each live block by base and
positive length; `ProductPCM` gives the pair its componentwise separation algebra. -/

abbrev AllocationTable : Type := Heap
abbrev ManagedHeap : Type := Heap × AllocationTable
def managed_empty : ManagedHeap := (hemp, hemp)

def hfree_block (base size : Nat) (h : Heap) : Heap :=
  fun x => if base ≤ x ∧ x < base + size then none else h x

def managed_alloc (memory : ManagedHeap) (base size : Nat) : ManagedHeap :=
  (hunion (hblock base size) memory.1, upd memory.2 base size)

def managed_free (memory : ManagedHeap) (base : Nat) : Option ManagedHeap :=
  if base = 0 then some memory else
  match memory.2 base with
  | some (n + 1) => some (hfree_block base (n + 1) memory.1, hfree base memory.2)
  | _ => none

def managed_wf (memory : ManagedHeap) : Prop :=
  (∀ base size, memory.2 base = some size →
    0 < base ∧ 0 < size ∧ (∀ x, base ≤ x ∧ x < base + size → memory.1 x ≠ none)) ∧
  (∀ b1 n1 b2 n2, memory.2 b1 = some n1 → memory.2 b2 = some n2 → b1 ≠ b2 →
    b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1)

def block_owned (base size : Nat) : assn ManagedHeap :=
  fun memory => 0 < base ∧ 0 < size ∧ heq memory.2 (hsingle base size) ∧
    (∀ x, memory.1 x ≠ none ↔ base ≤ x ∧ x < base + size)

theorem hfree_block_in (base size : Nat) (h : Heap) (x : Nat) :
    base ≤ x ∧ x < base + size → hfree_block base size h x = none := by
  intro hx; simp only [hfree_block]; split <;> first | rfl | omega

theorem hfree_block_out (base size : Nat) (h : Heap) (x : Nat) :
    x < base ∨ base + size ≤ x → hfree_block base size h x = h x := by
  intro hx; simp only [hfree_block]; split <;> first | rfl | omega

theorem hfree_block_finite (base size : Nat) (h : Heap) :
    heap_finite h → heap_finite (hfree_block base size h) := by
  rintro ⟨B, hB⟩
  refine ⟨B, fun x hx => ?_⟩
  simp only [hfree_block]; split
  · rfl
  · exact hB x hx

theorem managed_wf_empty : managed_wf managed_empty :=
  ⟨fun _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩

theorem managed_wf_preallocated (h : Heap) : managed_wf (h, hemp) :=
  ⟨fun _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩

theorem managed_write_preserves_wf (h : Heap) (allocs : AllocationTable) (a v : Nat) :
    managed_wf (h, allocs) → managed_wf (upd h a v, allocs) := by
  rintro ⟨W, D⟩
  refine ⟨fun base size hs => ?_, D⟩
  obtain ⟨hb, hn, C⟩ := W base size hs
  exact ⟨hb, hn, fun x hx => upd_mono _ _ _ _ (C x hx)⟩

/-- A free and an allocated nonempty interval of the same heap cannot overlap. -/
theorem block_free_allocated_disjoint (h : Heap) (base size b n : Nat) :
    0 < size → 0 < n → block_free h base size →
    (∀ x, b ≤ x ∧ x < b + n → h x ≠ none) → base + size ≤ b ∨ b + n ≤ base := by
  intro hs hn F C
  refine Classical.byContradiction fun hc => C (max base b) (by omega) ?_
  have := F (max base b - base) (by omega)
  rwa [Nat.add_sub_cancel' (Nat.le_max_left _ _)] at this

theorem managed_alloc_preserves_wf (memory : ManagedHeap) (base size : Nat) :
    managed_wf memory → 0 < base → 0 < size → block_free memory.1 base size →
    managed_wf (managed_alloc memory base size) := by
  obtain ⟨h, allocs⟩ := memory
  rintro ⟨W, D⟩ hb hs F
  simp only [managed_alloc, managed_wf] at *
  have old : ∀ b n, b ≠ base → upd allocs base size b = some n →
      allocs b = some n ∧ 0 < b ∧ 0 < n ∧ (∀ x, b ≤ x ∧ x < b + n → h x ≠ none) := by
    intro b n hne hl; rw [upd_neq _ _ _ _ hne] at hl; exact ⟨hl, W b n hl⟩
  have apart : ∀ b n, b ≠ base → upd allocs base size b = some n →
      base + size ≤ b ∨ b + n ≤ base := by
    intro b n hne hl
    obtain ⟨-, -, hn, C⟩ := old b n hne hl
    exact block_free_allocated_disjoint h base size b n hs hn F C
  constructor
  · intro b n hl
    by_cases hbe : b = base
    · subst hbe; rw [upd_eq] at hl; cases hl
      refine ⟨hb, hs, fun x hx => ?_⟩
      have := hblock_in b size (x - b) (by omega)
      rw [Nat.add_sub_cancel' hx.1] at this
      rw [hunion_some _ _ _ _ this]; simp
    · obtain ⟨-, hb', hn, C⟩ := old b n hbe hl
      exact ⟨hb', hn, fun x hx => by
        simp only [hunion]; split
        · simp
        · exact C x hx⟩
  · intro b1 n1 b2 n2 h1 h2 hne
    by_cases e1 : b1 = base <;> by_cases e2 : b2 = base
    · exact absurd (e1.trans e2.symm) hne
    · subst e1; rw [upd_eq] at h1; cases h1; have := apart b2 n2 e2 h2; omega
    · subst e2; rw [upd_eq] at h2; cases h2; have := apart b1 n1 e1 h1; omega
    · rw [upd_neq _ _ _ _ e1] at h1; rw [upd_neq _ _ _ _ e2] at h2
      exact D b1 n1 b2 n2 h1 h2 hne

private theorem managed_free_inv (m m' : ManagedHeap) (base : Nat) (hb : base ≠ 0)
    (hf : managed_free m base = some m') :
    ∃ n, m.2 base = some (n + 1) ∧ m' = (hfree_block base (n + 1) m.1, hfree base m.2) := by
  simp only [managed_free, hb, ↓reduceIte] at hf
  split at hf
  · rename_i n e; exact ⟨n, e, (Option.some.inj hf).symm⟩
  · exact nomatch hf

theorem managed_free_preserves_wf (memory memory' : ManagedHeap) (base : Nat) :
    managed_wf memory → managed_free memory base = some memory' → managed_wf memory' := by
  obtain ⟨h, allocs⟩ := memory
  rintro ⟨W, D⟩ hf
  by_cases hb0 : base = 0
  · simp only [managed_free, hb0, ↓reduceIte] at hf; cases hf; exact ⟨W, D⟩
  obtain ⟨n, eb, rfl⟩ := managed_free_inv _ _ _ hb0 hf
  have old : ∀ b s, hfree base allocs b = some s → b ≠ base ∧ allocs b = some s := by
    intro b s hl; simp only [hfree] at hl; split at hl
    · exact nomatch hl
    · exact ⟨Ne.symm ‹_›, hl⟩
  constructor
  · intro b s hl
    obtain ⟨hne, hl'⟩ := old b s hl
    obtain ⟨hb, hs, C⟩ := W b s hl'
    refine ⟨hb, hs, fun x hx => ?_⟩
    have := D b s base (n + 1) hl' eb hne
    show hfree_block base (n + 1) h x ≠ none
    rw [hfree_block_out _ _ _ _ (by omega)]; exact C x hx
  · intro b1 n1 b2 n2 h1 h2 hne
    exact D b1 n1 b2 n2 (old b1 n1 h1).2 (old b2 n2 h2).2 hne

theorem block_owned_proper (base size : Nat) : AProper (block_owned base size) := by
  rintro ⟨h, a⟩ ⟨h', a'⟩ ⟨hh, ha⟩ ⟨hb, hs, ht, hd⟩
  exact ⟨hb, hs, heq_trans _ _ _ (heq_sym _ _ ha) ht, fun x => (hh x) ▸ hd x⟩

theorem managed_alloc_sep (memory : ManagedHeap) (base size : Nat) (P : assn ManagedHeap) :
    0 < base → 0 < size → block_free memory.1 base size → memory.2 base = none → P memory →
    asep (block_owned base size) P (managed_alloc memory base size) := by
  obtain ⟨h, allocs⟩ := memory
  intro hb hs F hn hP
  refine ⟨(hblock base size, hsingle base size), (h, allocs),
    ⟨(block_free_disjoint _ _ _).1 F, fun x => ?_⟩, ⟨heq_refl _, fun x => ?_⟩,
    ⟨hb, hs, heq_refl _, fun x => ?_⟩, hP⟩
  · simp only [hsingle]; split
    · subst x; exact Or.inr hn
    · exact Or.inl rfl
  · show upd allocs base size x = hunion (hsingle base size) allocs x
    simp only [upd, hunion, hsingle]
    by_cases hx : x = base
    · subst hx; simp
    · simp [hx, Ne.symm hx]
  · show hblock base size x ≠ none ↔ _
    simp only [hblock]; split <;> simp_all

theorem managed_free_frame (owned frame : ManagedHeap) (base size : Nat) :
    pdef owned frame → block_owned base size owned →
    ∃ freed, managed_free (pop owned frame) base = some freed ∧ peq freed frame := by
  obtain ⟨ho, ao⟩ := owned
  obtain ⟨hf, af⟩ := frame
  rintro ⟨Dh, Da⟩ ⟨hb, hs, ha, hd⟩
  simp only at ha hd
  obtain ⟨n, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  have hab : ao base = some (n + 1) := by rw [ha base]; simp [hsingle]
  have ab : hunion ao af base = some (n + 1) := hunion_some _ _ _ _ hab
  refine ⟨(hfree_block base (n + 1) (hunion ho hf), hfree base (hunion ao af)), ?_, ?_⟩
  · show managed_free (hunion ho hf, hunion ao af) base = _
    simp only [managed_free, Nat.ne_of_gt hb, ↓reduceIte, ab]
  constructor
  · intro x
    show hfree_block base (n + 1) (hunion ho hf) x = hf x
    by_cases hx : base ≤ x ∧ x < base + (n + 1)
    · rw [hfree_block_in _ _ _ _ hx]
      cases hox : ho x with
      | some v => exact (hdisj_none _ _ _ _ Dh hox).symm
      | none => exact absurd hox ((hd x).2 hx)
    · rw [hfree_block_out _ _ _ _ (by omega), hunion_none]
      cases hox : ho x with
      | none => rfl
      | some v => exact absurd ((hd x).1 (by simp [hox])) hx
  · intro x
    show hfree base (hunion ao af) x = af x
    simp only [hfree]
    split
    · subst x; exact (hdisj_none _ _ _ _ Da hab).symm
    · rename_i hne; rw [hunion_none]; rw [ha x]; simp [hsingle, hne]

/-! ## Frame facts for `⊎` on managed heaps -/

/-- Reading an owned cell is unchanged by a disjoint frame. -/
theorem managed_read_pop (m fr : ManagedHeap) (a v : Nat) :
    m # fr → m.1 a = some v → (m ⊎ fr).1 a = some v :=
  fun hd => read_local m.1 fr.1 a v hd.1

/-- Writing an owned cell preserves disjointness and commutes with framing up to `≈`. -/
theorem managed_write_pop (m fr : ManagedHeap) (a v : Nat) :
    m # fr → m.1 a ≠ none →
    (upd m.1 a v, m.2) # fr ∧ (upd m.1 a v, m.2) ⊎ fr ≈ (upd (m ⊎ fr).1 a v, (m ⊎ fr).2) := by
  obtain ⟨h, allocs⟩ := m
  obtain ⟨hf, af⟩ := fr
  rintro ⟨Dh, Da⟩ ha
  cases hav : h a with
  | none => exact absurd hav ha
  | some v0 =>
    exact ⟨⟨write_local_disj _ _ _ _ _ Dh hav, Da⟩,
      heq_sym _ _ (write_local_frame _ _ _ _), heq_refl _⟩

/-- Freeing a managed allocation preserves disjointness and commutes with framing up to `≈`. -/
theorem managed_free_pop (m fr : ManagedHeap) (base : Nat) (m' : ManagedHeap) :
    m # fr → managed_wf m → managed_free m base = some m' →
    (∃ m'', managed_free (m ⊎ fr) base = some m'' ∧ m'' ≈ m' ⊎ fr) ∧ m' # fr := by
  obtain ⟨h, allocs⟩ := m
  obtain ⟨hf, af⟩ := fr
  rintro ⟨Dh, Da⟩ ⟨W, -⟩ hfr
  by_cases hb0 : base = 0
  · simp only [managed_free, hb0, ↓reduceIte] at hfr; cases hfr
    exact ⟨⟨_, by simp only [managed_free, hb0, ↓reduceIte], peq_refl _⟩, Dh, Da⟩
  obtain ⟨n, ea, rfl⟩ := managed_free_inv _ _ _ hb0 hfr
  simp only at ea
  obtain ⟨-, -, C⟩ := W base (n + 1) ea
  refine ⟨⟨(hfree_block base (n + 1) (hunion h hf), hfree base (hunion allocs af)), ?_, ?_, ?_⟩,
    ?_, free_local_disj _ _ _ Da⟩
  · show managed_free (hunion h hf, hunion allocs af) base = _
    simp only [managed_free, hb0, ↓reduceIte, hunion_some _ _ _ _ ea]
  · intro x
    show hfree_block base (n + 1) (hunion h hf) x = hunion (hfree_block base (n + 1) h) hf x
    by_cases hx : base ≤ x ∧ x < base + (n + 1)
    · rw [hfree_block_in _ _ _ _ hx, hunion_none _ _ _ (hfree_block_in _ _ _ _ hx)]
      exact ((Dh x).resolve_left (C x hx)).symm
    · rw [hfree_block_out _ _ _ _ (by omega)]
      simp only [hunion, hfree_block_out _ _ _ _ (show x < base ∨ base + (n + 1) ≤ x by omega)]
  · exact free_local_frame _ _ _ _ Da ea
  · intro x
    simp only [hfree_block]; split
    · exact Or.inl rfl
    · exact Dh x

/-- Freeing respects componentwise managed-heap equivalence. -/
theorem managed_free_peq (m m' : ManagedHeap) (base : Nat) (m1 : ManagedHeap) :
    m ≈ m' → managed_free m base = some m1 → ∃ m1', managed_free m' base = some m1' ∧ m1 ≈ m1' := by
  obtain ⟨h, allocs⟩ := m
  obtain ⟨h', allocs'⟩ := m'
  rintro ⟨hh, ha⟩ hf
  by_cases hb0 : base = 0
  · simp only [managed_free, hb0, ↓reduceIte] at hf ⊢; cases hf; exact ⟨_, rfl, hh, ha⟩
  obtain ⟨n, ea, rfl⟩ := managed_free_inv _ _ _ hb0 hf
  simp only at ea
  have ea' : allocs' base = some (n + 1) := (ha base).symm.trans ea
  simp only [managed_free, hb0, ↓reduceIte, ea']
  refine ⟨_, rfl, fun x => ?_, fun x => ?_⟩
  · simp only [hfree_block]; split
    · rfl
    · exact hh x
  · simp only [hfree]; split
    · rfl
    · exact ha x

/-! ## Stride-two node geometry

A node named `a` owns exactly two cells: the payload cell `a` and the link cell `a + 1`. -/

/-- The two cells of every node in `l`. -/
def cells (l : List Nat) : List Nat := l.flatMap fun a => [a, a + 1]

theorem in_cells (x : Nat) (l : List Nat) : x ∈ cells l ↔ ∃ a, a ∈ l ∧ (x = a ∨ x = a + 1) := by
  simp [cells, List.mem_flatMap]

theorem cells_length (ns : List Nat) : (cells ns).length = 2 * ns.length :=
  flat_map_fixed_length _ _ _ fun _ _ => rfl

theorem cells_nodup (ns : List Nat) :
    ns.Nodup → (∀ a b, a ∈ ns → b ∈ ns → a ≠ b + 1) → (cells ns).Nodup := by
  induction ns with
  | nil => intros; exact List.Pairwise.nil
  | cons a ns ih =>
    intro hnd hdisj
    rw [List.nodup_cons] at hnd
    show (a :: (a + 1) :: cells ns).Nodup
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih hnd.2 fun b c hb hc =>
      hdisj b c (List.mem_cons_of_mem _ hb) (List.mem_cons_of_mem _ hc)⟩⟩
    · intro hin
      rcases List.mem_cons.1 hin with e | hin
      · omega
      obtain ⟨b, hb, e | e⟩ := (in_cells _ _).1 hin
      · subst e; exact hnd.1 hb
      · exact hdisj a b List.mem_cons_self (List.mem_cons_of_mem _ hb) e
    · intro hin
      obtain ⟨b, hb, e | e⟩ := (in_cells _ _).1 hin
      · exact hdisj b a (List.mem_cons_of_mem _ hb) List.mem_cons_self e.symm
      · exact hnd.1 (by rw [show a = b by omega]; exact hb)

/-- Payload/link pairs in source order; both zips truncate. -/
def node_writes (ns vs : List Nat) : List (Nat × Nat) :=
  (ns.zip (vs.zip (ns.tail ++ [0]))).flatMap fun (a, v, next) => [(a, v), (a + 1, next)]

theorem node_writes_cons (a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) :
    node_writes (a :: ns) (v :: vs) = (a, v) :: (a + 1, ns.headD 0) :: node_writes ns vs := by
  cases ns <;> rfl

theorem node_writes_keys (ns vs : List Nat) :
    (node_writes ns vs).map Prod.fst = cells (ns.take vs.length) := by
  induction ns generalizing vs with
  | nil => simp [node_writes, cells]
  | cons a ns ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      rw [node_writes_cons]
      simp only [List.map_cons, List.length_cons, List.take_succ_cons, ih]; rfl

theorem node_writes_cells (ns vs : List Nat) :
    ns.length = vs.length → (node_writes ns vs).map Prod.fst = cells ns := by
  intro hlen; rw [node_writes_keys, ← hlen, List.take_length]

theorem node_writes_nodup (ns vs : List Nat) :
    ns.length = vs.length → (cells ns).Nodup → ((node_writes ns vs).map Prod.fst).Nodup := by
  intro hlen hnd; rwa [node_writes_cells _ _ hlen]

theorem node_writes_keys_subset (ns vs : List Nat) (a : Nat) :
    a ∈ (node_writes ns vs).map Prod.fst → a ∈ cells ns := by
  intro hin
  obtain ⟨⟨b, v⟩, hmem, rfl⟩ := List.mem_map.1 hin
  obtain ⟨⟨c, u, next⟩, hpair, hin⟩ := List.mem_flatMap.1 hmem
  refine (in_cells _ _).2 ⟨c, (List.of_mem_zip hpair).1, ?_⟩
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  omega

theorem node_writes_dom (ns vs : List Nat) (a : Nat) :
    ns.length = vs.length →
    (apply_writes (node_writes ns vs).reverse hemp a ≠ none ↔ a ∈ cells ns) := by
  intro hlen
  rw [apply_writes_dom_exact, List.map_reverse, node_writes_cells _ _ hlen, List.mem_reverse]
  simp [hemp]

theorem node_writes_contents (ns vs : List Nat) :
    ns.length = vs.length → (cells ns).Nodup →
    Forall2 (fun a (p : Nat × Nat) =>
      apply_writes (node_writes ns vs).reverse hemp a = some p.1 ∧
      apply_writes (node_writes ns vs).reverse hemp (a + 1) = some p.2)
      ns (vs.zip (ns.tail ++ [0])) := by
  intro hlen hnd
  have hkeys : ((node_writes ns vs).reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, node_writes_cells _ _ hlen]; exact nodup_reverse hnd
  have hpair : ∀ a v next, (a, v, next) ∈ ns.zip (vs.zip (ns.tail ++ [0])) →
      apply_writes (node_writes ns vs).reverse hemp a = some v ∧
      apply_writes (node_writes ns vs).reverse hemp (a + 1) = some next := by
    intro a v next hin
    refine ⟨apply_writes_contents _ _ _ _ hkeys (List.mem_reverse.2 ?_),
      apply_writes_contents _ _ _ _ hkeys (List.mem_reverse.2 ?_)⟩ <;>
      exact List.mem_flatMap.2 ⟨(a, v, next), hin, by simp⟩
  have hlength : ns.length = (vs.zip (ns.tail ++ [0])).length := by
    rw [List.length_zip, List.length_append]; cases ns <;> simp_all
  refine (Forall2_in_combine _ _ _).2 ⟨hlength, fun a p hin => hpair a p.1 p.2 hin⟩

def node_addrs (first : Nat) : Nat → List Nat
  | 0 => []
  | rest + 1 => first :: node_addrs (first + 2) rest

theorem node_addrs_in (first count x : Nat) :
    x ∈ node_addrs first count ↔ ∃ j, j < count ∧ x = first + 2 * j := by
  induction count generalizing first with
  | zero => simp [node_addrs]
  | succ count ih =>
    simp only [node_addrs, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, by omega, by omega⟩
      · exact ⟨j + 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | zero => exact Or.inl (by omega)
      | succ j => exact Or.inr ⟨j, by omega, by omega⟩

@[simp] theorem node_addrs_length (first count : Nat) :
    (node_addrs first count).length = count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih => simp [node_addrs, ih]

theorem node_addrs_nodup (first count : Nat) : (node_addrs first count).Nodup := by
  induction count generalizing first with
  | zero => exact List.Pairwise.nil
  | succ count ih =>
    refine List.nodup_cons.2 ⟨fun hin => ?_, ih _⟩
    obtain ⟨j, -, hj⟩ := (node_addrs_in _ _ _).1 hin
    omega

theorem node_cells_range (first count x : Nat) :
    x ∈ cells (node_addrs first count) ↔ first ≤ x ∧ x < first + 2 * count := by
  rw [in_cells]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨j, hj, rfl⟩ := (node_addrs_in _ _ _).1 ha
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨first + 2 * ((x - first) / 2), (node_addrs_in _ _ _).2 ⟨_, by omega, rfl⟩, by omega⟩

theorem node_addrs_link_payload_disjoint (first count a b : Nat) :
    a ∈ node_addrs first count → b ∈ node_addrs first count → a ≠ b + 1 := by
  intro ha hb
  obtain ⟨i, -, rfl⟩ := (node_addrs_in _ _ _).1 ha
  obtain ⟨j, -, rfl⟩ := (node_addrs_in _ _ _).1 hb
  omega

theorem node_addrs_cells_nodup (first count : Nat) : (cells (node_addrs first count)).Nodup :=
  cells_nodup _ (node_addrs_nodup _ _) fun a b => node_addrs_link_payload_disjoint first count a b

/-- Null-terminated successor updates: exactly `count` writes. -/
def link_updates (first count : Nat) : List (Nat × Nat) :=
  (node_addrs first count).zip ((node_addrs first count).tail ++ [0])

theorem combine_successors_cons (a : Nat) (ns : List Nat) :
    (a :: ns).zip ((a :: ns).tail ++ [0]) = (a, ns.headD 0) :: ns.zip (ns.tail ++ [0]) := by
  cases ns <;> rfl

theorem link_updates_cons (first count : Nat) :
    link_updates first (count + 1) =
      (first, (node_addrs (first + 2) count).headD 0) :: link_updates (first + 2) count :=
  combine_successors_cons _ _

theorem link_updates_keys (first count : Nat) :
    (link_updates first count).map Prod.fst = node_addrs first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih => rw [link_updates_cons, List.map_cons, ih]; rfl

@[simp] theorem link_updates_length (first count : Nat) :
    (link_updates first count).length = count := by
  rw [← List.length_map (f := Prod.fst), link_updates_keys, node_addrs_length]

theorem combine_successors_in (pre : List Nat) (b : Nat) (rest : List Nat) :
    (b, rest.headD 0) ∈ (pre ++ b :: rest).zip ((pre ++ b :: rest).tail ++ [0]) := by
  induction pre with
  | nil => rw [List.nil_append, combine_successors_cons]; exact List.mem_cons_self
  | cons a pre ih => rw [List.cons_append, combine_successors_cons]; exact List.mem_cons_of_mem _ ih

theorem link_updates_contents (first count : Nat) (h : Heap) (pre : List Nat) (b : Nat)
    (rest : List Nat) :
    node_addrs first count = pre ++ b :: rest →
    apply_writes (link_updates first count) h b = some (rest.headD 0) := by
  intro hnodes
  refine apply_writes_contents _ _ _ _ (by rw [link_updates_keys]; exact node_addrs_nodup _ _) ?_
  unfold link_updates; rw [hnodes]; exact combine_successors_in _ _ _

theorem link_updates_null (first count : Nat) (h : Heap) (pre : List Nat) (b : Nat) :
    node_addrs first count = pre ++ [b] → apply_writes (link_updates first count) h b = some 0 :=
  link_updates_contents first count h pre b []

theorem link_updates_index (first count j : Nat) :
    j < count →
    (first + 2 * j, if j + 1 < count then first + 2 * (j + 1) else 0) ∈
      link_updates first count := by
  induction count generalizing first j with
  | zero => intro h; omega
  | succ count ih =>
    intro hj
    rw [link_updates_cons]
    cases j with
    | zero =>
      refine List.mem_cons.2 (Or.inl ?_)
      cases count <;> simp [node_addrs]
    | succ j =>
      refine List.mem_cons_of_mem _ ?_
      have := ih (first + 2) j (by omega)
      rw [show first + 2 * (j + 1) = first + 2 + 2 * j by omega,
        show first + 2 * (j + 1 + 1) = first + 2 + 2 * (j + 1) by omega]
      simpa [show (j + 1 + 1 < count + 1) = (j + 1 < count) from propext (by omega)] using this

theorem link_updates_contents_index (first count : Nat) (h : Heap) (j : Nat) :
    j < count →
    apply_writes (link_updates first count) h (first + 2 * j) =
      some (if j + 1 < count then first + 2 * (j + 1) else 0) := fun hj =>
  apply_writes_contents _ _ _ _ (by rw [link_updates_keys]; exact node_addrs_nodup _ _)
    (link_updates_index _ _ _ hj)

/-! ## Pure link initialization over a stride-two node list

Links run low to high; the last link is the null terminator `0`. Without a checked-write premise
the pure initializer may extend the domain (see `init_links_heap_dom`). -/

def init_links_heap (first count : Nat) (h : Heap) : Heap :=
  apply_writes (link_updates first count) h

theorem init_links_heap_lookup_agree (first count : Nat) (h f : Heap) (x : Nat) :
    h x = f x → init_links_heap first count h x = init_links_heap first count f x :=
  apply_writes_lookup_agree _ _ _ _

theorem init_links_heap_frame (first count : Nat) (h : Heap) (x : Nat) :
    x ∉ node_addrs first count → init_links_heap first count h x = h x := fun hout =>
  apply_writes_outside _ _ _ (by rwa [link_updates_keys])

theorem init_links_heap_out (first count : Nat) (h : Heap) (x : Nat) :
    (x < first ∨ first + 2 * count ≤ x) → init_links_heap first count h x = h x := by
  intro hout
  refine init_links_heap_frame _ _ _ _ fun hin => ?_
  obtain ⟨j, hj, rfl⟩ := (node_addrs_in _ _ _).1 hin
  omega

theorem init_links_heap_payload (first count : Nat) (h : Heap) (b : Nat) :
    b ∈ node_addrs first count → init_links_heap first count h (b + 1) = h (b + 1) := fun hb =>
  init_links_heap_frame _ _ _ _ fun hin =>
    node_addrs_link_payload_disjoint first count (b + 1) b hin hb rfl

theorem init_links_heap_dom (first count : Nat) (h : Heap) (x : Nat) :
    init_links_heap first count h x ≠ none ↔ x ∈ node_addrs first count ∨ h x ≠ none := by
  rw [init_links_heap, apply_writes_dom_exact, link_updates_keys]

/-- A list-suffix lookup is independent of the incoming heap. -/
theorem init_links_heap_link (first count : Nat) (h : Heap) (pre : List Nat) (b : Nat)
    (rest : List Nat) :
    node_addrs first count = pre ++ b :: rest →
    init_links_heap first count h b = some (rest.headD 0) :=
  link_updates_contents first count h pre b rest

theorem init_links_heap_link_index (first count : Nat) (h : Heap) (j : Nat) :
    j < count →
    init_links_heap first count h (first + 2 * j) =
      some (if j + 1 < count then first + 2 * (j + 1) else 0) :=
  link_updates_contents_index first count h j

theorem init_links_heap_finite (first count : Nat) (h : Heap) :
    heap_finite h → heap_finite (init_links_heap first count h) :=
  apply_writes_finite _ _

end Tisl.Heap

-- Not ported: `Ltac hcase` (tactic).
