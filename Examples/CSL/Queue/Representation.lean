/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.CSL
public import Logic.Utils.Lists

/-!
# Heap-backed queue representation and pure resource theory

No temporal reasoning. The representation predicate `qrep hdr ns vs h` says that `h` holds a
null-terminated singly linked list of two-cell nodes at the distinct addresses `ns` carrying the
payloads `vs` (which may repeat), anchored at the header pair `hdr` (tail pointer) / `hdr + 1`
(head pointer). `qrep` is the intuitionistic reading ("the heap contains this queue"); `qex` is
the exactness side condition. The rotation is the pure heap surgery `rot_heap`; `rot_detach_split`
is the intermediate ownership split and `rot_heap_spec` the rotation theorem
(← `examples/CSL/Queue/Representation.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Representation
open Tisl Tisl.Heap

/-! ## Footprints and well-formedness -/

/-- The footprint of a queue: the header's two cells plus every node's two cells. -/
def qcells (hdr : Nat) (ns : List Nat) : List Nat := hdr :: (hdr + 1) :: cells ns

/-- Node names are distinct, non-null and non-overlapping (no node's payload cell is another
node's link cell). Payloads are unconstrained. -/
def qwf (hdr : Nat) (ns : List Nat) : Prop :=
  (hdr :: ns).Nodup ∧ 0 ∉ hdr :: ns ∧ ∀ a b, a ∈ hdr :: ns → b ∈ hdr :: ns → a ≠ b + 1

/-- Two-word alignment is a sufficient concrete policy for the non-overlap condition (Rocq
`Forall Nat.Even`). -/
theorem qwf_aligned (hdr : Nat) (ns : List Nat) :
    (hdr :: ns).Nodup → 0 ∉ hdr :: ns → (∀ x, x ∈ hdr :: ns → x % 2 = 0) → qwf hdr ns := by
  intro hnd h0 hev
  refine ⟨hnd, h0, fun a b ha hb e => ?_⟩
  have := hev a ha; have := hev b hb; omega

theorem qwf_perm (hdr : Nat) (ns ns' : List Nat) : ns.Perm ns' → qwf hdr ns → qwf hdr ns' := by
  rintro hp ⟨hnd, h0, hov⟩
  have hp' : (hdr :: ns).Perm (hdr :: ns') := hp.cons hdr
  exact ⟨hp'.nodup_iff.1 hnd, fun h => h0 (hp'.mem_iff.2 h),
    fun a b ha hb => hov a b (hp'.mem_iff.2 ha) (hp'.mem_iff.2 hb)⟩

theorem qwf_hdr_cells (hdr : Nat) (ns : List Nat) : qwf hdr ns → hdr ∉ cells ns := by
  rintro ⟨hnd, -, hov⟩ hin
  have hni := (List.nodup_cons.1 hnd).1
  obtain ⟨a, ha, e | e⟩ := (in_cells _ _).1 hin
  · subst e; exact hni ha
  · exact hov hdr a (.head _) (.tail _ ha) e

theorem qwf_shdr_cells (hdr : Nat) (ns : List Nat) : qwf hdr ns → hdr + 1 ∉ cells ns := by
  rintro ⟨hnd, -, hov⟩ hin
  have hni := (List.nodup_cons.1 hnd).1
  obtain ⟨a, ha, e | e⟩ := (in_cells _ _).1 hin
  · exact hov a hdr (.tail _ ha) (.head _) e.symm
  · obtain rfl : hdr = a := by omega
    exact hni ha

theorem qwf_node_cells (hdr : Nat) (ns : List Nat) (a : Nat) :
    qwf hdr (a :: ns) → a ∉ cells ns ∧ a + 1 ∉ cells ns := by
  rintro ⟨hnd, -, hov⟩
  have hni := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
  have ma : a ∈ hdr :: a :: ns := .tail _ (.head _)
  constructor <;> intro hin <;> obtain ⟨b, hb, e | e⟩ := (in_cells _ _).1 hin
  · subst e; exact hni hb
  · exact hov a b ma (.tail _ (.tail _ hb)) e
  · exact hov b a (.tail _ (.tail _ hb)) ma e.symm
  · obtain rfl : a = b := by omega
    exact hni hb

theorem qwf_zero (hdr : Nat) (ns : List Nat) : qwf hdr ns → 0 ∉ qcells hdr ns := by
  rintro ⟨-, h0, -⟩ hc
  rcases List.mem_cons.1 hc with e | hc
  · subst e; exact h0 (.head _)
  rcases List.mem_cons.1 hc with e | hc
  · omega
  obtain ⟨a, ha, e | e⟩ := (in_cells _ _).1 hc
  · subst e; exact h0 (.tail _ ha)
  · omega

/-! ## The chain of nodes -/

/-- The addresses `ns` carry the payloads `vs` and are linked in order (link at `a + 1`), the
last link holding the terminator `fin`. -/
def chain (h : Heap) (ns vs : List Nat) (fin : Nat) : Prop :=
  linked (fun a next => h (a + 1) = some next) ns fin ∧ Forall2 (fun a v => h a = some v) ns vs

theorem chain_nil (h : Heap) (fin : Nat) : chain h [] [] fin := ⟨trivial, .nil⟩

theorem chain_cons (h : Heap) (a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (fin : Nat) :
    chain h (a :: ns) (v :: vs) fin ↔
      h a = some v ∧ h (a + 1) = some (ns.headD fin) ∧ chain h ns vs fin := by
  simp only [chain, linked, Forall2_cons_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h3, h1, h2, h4⟩, fun ⟨h3, h1, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩

theorem chain_len (h : Heap) (ns vs : List Nat) (f : Nat) :
    chain h ns vs f → ns.length = vs.length := fun ⟨_, hf⟩ => Forall2_length hf

theorem chain_mono (h h' : Heap) (ns vs : List Nat) (fin : Nat) :
    chain h ns vs fin → (∀ x, x ∈ cells ns → h' x = h x) → chain h' ns vs fin := by
  rintro ⟨hl, hf⟩ hag
  refine ⟨linked_mono _ _ _ _ (fun a b ha hab => ?_) hl,
    Forall2_impl' _ _ _ _ hf fun a v ha _ hav => ?_⟩
  · show h' (a + 1) = some b
    rw [hag _ ((in_cells _ _).2 ⟨a, ha, .inr rfl⟩)]; exact hab
  · show h' a = some v
    rw [hag _ ((in_cells _ _).2 ⟨a, ha, .inl rfl⟩)]; exact hav

theorem chain_dom (h : Heap) (ns vs : List Nat) (f x : Nat) :
    chain h ns vs f → x ∈ cells ns → h x ≠ none := by
  rintro ⟨hl, hf⟩ hin
  obtain ⟨a, ha, rfl | rfl⟩ := (in_cells _ _).1 hin
  · obtain ⟨v, -, hav⟩ := Forall2_left_exists _ _ _ hf x ha
    have hav : h x = some v := hav
    simp [hav]
  · obtain ⟨pre, rest, rfl⟩ := List.append_of_mem ha
    have hl : h (a + 1) = some _ := (linked_split _ _ _ _ hl).2.1
    simp [hl]

/-- `h'` agrees with `h` outside the footprint `m`. -/
def agree_out (m : List Nat) (h h' : Heap) : Prop := ∀ x, x ∉ m → h' x = h x

theorem chain_frame (h h' : Heap) (m ns vs : List Nat) (f : Nat) :
    chain h ns vs f → agree_out m h h' → (∀ x, x ∈ m → x ∉ cells ns) → chain h' ns vs f :=
  fun hc hag hm => chain_mono _ _ _ _ _ hc fun x hx => hag x fun hin => hm x hin hx

theorem chain_app (h : Heap) (ns1 vs1 ns2 vs2 : List Nat) (f : Nat) :
    chain h ns1 vs1 (ns2.headD f) → chain h ns2 vs2 f → chain h (ns1 ++ ns2) (vs1 ++ vs2) f := by
  rintro ⟨h1l, h1f⟩ ⟨h2l, h2f⟩
  refine ⟨linked_app _ _ _ _ h1l h2l, ?_⟩
  clear h1l h2l
  induction h1f with
  | nil => exact h2f
  | cons hxy _ ih => exact .cons hxy ih

theorem chain_split (h : Heap) (ns1 vs1 ns2 vs2 : List Nat) (f : Nat) :
    ns1.length = vs1.length → chain h (ns1 ++ ns2) (vs1 ++ vs2) f →
      chain h ns1 vs1 (ns2.headD f) ∧ chain h ns2 vs2 f := by
  rintro hl ⟨hlk, hf⟩
  obtain ⟨h1l, h2l⟩ := linked_split _ _ _ _ hlk
  obtain ⟨h1f, h2f⟩ := Forall2_app_inv_len _ _ _ _ _ hl hf
  exact ⟨⟨h1l, h1f⟩, h2l, h2f⟩

/-! ## The representation predicate -/

/-- The tail pointer is constrained only when the queue is non-empty. -/
def tailok (hdr : Nat) (ns : List Nat) (h : Heap) : Prop :=
  match ns with
  | [] => h hdr ≠ none
  | _ => h hdr = some (ns.getLastD 0)

/-- The intuitionistic representation predicate: the heap contains this queue. Its last clause
says only that null is unallocated and the footprint is allocated, so a framed heap still
satisfies it; the exact reading adds `qex`. -/
def qrep (hdr : Nat) (ns vs : List Nat) (h : Heap) : Prop :=
  qwf hdr ns ∧ h (hdr + 1) = some (ns.headD 0) ∧ tailok hdr ns h ∧ chain h ns vs 0 ∧
    (h 0 = none ∧ ∀ x, x ∈ qcells hdr ns → h x ≠ none)

theorem qrep_len (hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ns.length = vs.length := fun ⟨_, _, _, hc, _⟩ => chain_len _ _ _ _ hc

/-- The null address is never allocated. -/
theorem qrep_null (hdr : Nat) (ns vs : List Nat) (h : Heap) : qrep hdr ns vs h → h 0 = none :=
  fun ⟨_, _, _, _, hd⟩ => hd.1

theorem qrep_fp (hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ∀ x, x ∈ qcells hdr ns → h x ≠ none :=
  fun ⟨_, _, _, _, hd⟩ => hd.2

/-- Exactness: every allocated cell is in the queue's footprint. -/
def qex (hdr : Nat) (ns : List Nat) (h : Heap) : Prop :=
  ∀ x, h x ≠ none → x ∈ qcells hdr ns

theorem qrep_head_null_iff (hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → (ns.headD 0 = 0 ↔ ns = []) := by
  rintro ⟨⟨-, h0, -⟩, -⟩
  cases ns with
  | nil => simp
  | cons a ns =>
    simp only [List.headD_cons, reduceCtorEq, iff_false]
    rintro rfl; exact h0 (.tail _ (.head _))

/-! ## Rotation on the abstract lists -/

theorem qcells_rot (hdr a : Nat) (ns : List Nat) (x : Nat) :
    x ∈ qcells hdr (ns ++ [a]) ↔ x ∈ qcells hdr (a :: ns) :=
  (((List.perm_append_singleton a ns).flatMap_right _).cons _ |>.cons _).mem_iff

/-! ## The rotation, as heap surgery

`rot_heap hdr a n z h` performs, in program order: detach (`hdr + 1 := n`), append
(`z + 1 := a`), terminate (`a + 1 := 0`), retarget the tail (`hdr := a`). -/

def rot_heap (hdr a n z : Nat) (h : Heap) : Heap :=
  upd (upd (upd (upd h (hdr + 1) n) (z + 1) a) (a + 1) 0) hdr a

/-- The node the append phase links to: the old last node, or the header itself when detaching
emptied the queue. -/
def zof (hdr : Nat) (ns : List Nat) : Nat :=
  match ns with
  | [] => hdr
  | _ => ns.getLastD 0

theorem zof_snoc (hdr : Nat) (l : List Nat) (a : Nat) : zof hdr (l ++ [a]) = a := by
  unfold zof; split
  · simp_all
  · exact List.getLastD_concat

theorem rot_heap_hdr (hdr a n z : Nat) (h : Heap) : rot_heap hdr a n z h hdr = some a :=
  upd_eq _ _ _

theorem rot_heap_sa (hdr a n z : Nat) (h : Heap) :
    a + 1 ≠ hdr → rot_heap hdr a n z h (a + 1) = some 0 := by
  intro h1; unfold rot_heap; rw [upd_neq _ _ _ _ h1, upd_eq]

theorem rot_heap_sz (hdr a n z : Nat) (h : Heap) :
    z + 1 ≠ hdr → z ≠ a → rot_heap hdr a n z h (z + 1) = some a := by
  intro h1 h2; unfold rot_heap; rw [upd_neq _ _ _ _ h1, upd_neq _ _ _ _ (by omega), upd_eq]

theorem rot_heap_shdr (hdr a n z : Nat) (h : Heap) :
    hdr ≠ a → hdr ≠ z → rot_heap hdr a n z h (hdr + 1) = some n := by
  intro h1 h2; unfold rot_heap
  rw [upd_neq _ _ _ _ (by omega), upd_neq _ _ _ _ (by omega), upd_neq _ _ _ _ (by omega), upd_eq]

theorem rot_heap_other (hdr a n z : Nat) (h : Heap) (x : Nat) :
    x ≠ hdr → x ≠ a + 1 → x ≠ z + 1 → x ≠ hdr + 1 → rot_heap hdr a n z h x = h x := by
  intro h1 h2 h3 h4; unfold rot_heap
  rw [upd_neq _ _ _ _ h1, upd_neq _ _ _ _ h2, upd_neq _ _ _ _ h3, upd_neq _ _ _ _ h4]

/-- The rotation touches no cell outside the queue's footprint and creates none. -/
theorem rot_heap_dom (hdr a n z : Nat) (h : Heap) :
    h (hdr + 1) ≠ none → h (z + 1) ≠ none → h (a + 1) ≠ none → h hdr ≠ none →
      ∀ x, rot_heap hdr a n z h x ≠ none ↔ h x ≠ none := by
  intro h1 h2 h3 h4 x; unfold rot_heap upd
  by_cases e1 : x = hdr <;> by_cases e2 : x = a + 1 <;> by_cases e3 : x = z + 1 <;>
    by_cases e4 : x = hdr + 1 <;> simp_all

/-! ### The intermediate ownership split

Between the detach and the append the heap splits into a well-formed queue holding the remaining
nodes and the two cells of the detached node `a`. -/

/-- `h` owns exactly the node `a` with payload `v` and link `nx`. -/
def nodeat (a v nx : Nat) (h : Heap) : Prop :=
  h a = some v ∧ h (a + 1) = some nx ∧ ∀ x, h x ≠ none ↔ (x = a ∨ x = a + 1)

/-- Membership test for the two cells of node `a`. -/
def nodeb (a x : Nat) : Bool := x == a || x == a + 1

theorem nodeb_true (a x : Nat) : nodeb a x = true ↔ (x = a ∨ x = a + 1) := by simp [nodeb]

theorem nodeb_false (a x : Nat) : nodeb a x = false ↔ (x ≠ a ∧ x ≠ a + 1) := by simp [nodeb]

/-- The address inequalities the rotation needs, derived once from `qwf`. -/
theorem qwf_neqs (hdr a : Nat) (ns : List Nat) :
    qwf hdr (a :: ns) →
      hdr ≠ a ∧ hdr + 1 ≠ a ∧ hdr ≠ a + 1 ∧ hdr + 1 ≠ a + 1 ∧ hdr ≠ hdr + 1 := by
  rintro ⟨hnd, -, hov⟩
  have hni := (List.nodup_cons.1 hnd).1
  have hha : hdr ≠ a := by rintro rfl; exact hni (.head _)
  have := hov a hdr (.tail _ (.head _)) (.head _)
  have := hov hdr a (.head _) (.tail _ (.head _))
  refine ⟨hha, ?_, ?_, ?_, ?_⟩ <;> omega

theorem qwf_neqs_mem (hdr a : Nat) (ns : List Nat) (z : Nat) :
    qwf hdr (a :: ns) → z ∈ ns →
      z ≠ hdr ∧ z ≠ a ∧ z ≠ hdr + 1 ∧ z ≠ a + 1 ∧
      z + 1 ≠ hdr ∧ z + 1 ≠ a ∧ z + 1 ≠ hdr + 1 ∧ z + 1 ≠ a + 1 := by
  rintro ⟨hnd, -, hov⟩ hz
  have hni := (List.nodup_cons.1 hnd).1
  have hnia := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
  have mz : z ∈ hdr :: a :: ns := .tail _ (.tail _ hz)
  have mh : hdr ∈ hdr :: a :: ns := .head _
  have ma : a ∈ hdr :: a :: ns := .tail _ (.head _)
  have hzh : z ≠ hdr := by rintro rfl; exact hni (.tail _ hz)
  have hza : z ≠ a := by rintro rfl; exact hnia hz
  have := hov z hdr mz mh; have := hov z a mz ma; have := hov hdr z mh mz; have := hov a z ma mz
  refine ⟨hzh, hza, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem qwf_tail (hdr a : Nat) (ns : List Nat) : qwf hdr (a :: ns) → qwf hdr ns := by
  rintro ⟨hnd, h0, hov⟩
  obtain ⟨hni, hnd'⟩ := List.nodup_cons.1 hnd
  have sub : ∀ x, x ∈ hdr :: ns → x ∈ hdr :: a :: ns := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact .head _
    · exact .tail _ (.tail _ hx)
  exact ⟨List.nodup_cons.2 ⟨fun h => hni (.tail _ h), (List.nodup_cons.1 hnd').2⟩,
    fun h => h0 (sub _ h), fun x y hx hy => hov x y (sub _ hx) (sub _ hy)⟩

/-- The queue that remains after the head node is detached. -/
def qres (hdr a n : Nat) (h : Heap) : Heap :=
  fun x => if nodeb a x then none else upd h (hdr + 1) n x

/-- The detached node itself. -/
def qnode (a : Nat) (h : Heap) : Heap := fun x => if nodeb a x then h x else none

/-- The intermediate ownership split (needs the exact reading `qex`). -/
theorem rot_detach_split (hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (h : Heap) :
    qrep hdr (a :: ns) (v :: vs) h → qex hdr (a :: ns) h →
      hdisj (qres hdr a (ns.headD 0) h) (qnode a h) ∧
      heq (upd h (hdr + 1) (ns.headD 0)) (hunion (qres hdr a (ns.headD 0) h) (qnode a h)) ∧
      (qrep hdr ns vs (qres hdr a (ns.headD 0) h) ∧ qex hdr ns (qres hdr a (ns.headD 0) h)) ∧
      nodeat a v (ns.headD 0) (qnode a h) := by
  rintro ⟨hwf, hhd, htl, hch, hnull, hfp⟩ hex
  obtain ⟨ha, hsa, hch⟩ := (chain_cons _ _ _ _ _ _).1 hch
  obtain ⟨hha, hsha, hhsa, hshsa, hhshdr⟩ := qwf_neqs _ _ _ hwf
  obtain ⟨hanc, hsanc⟩ := qwf_node_cells _ _ _ hwf
  have hwfns := qwf_tail _ _ _ hwf
  have hhnc := qwf_hdr_cells _ _ hwfns
  have hshnc := qwf_shdr_cells _ _ hwfns
  have hhdrdom : h hdr ≠ none := hfp _ (.head _)
  have hqhdr : qres hdr a (ns.headD 0) h hdr = h hdr := by
    simp only [qres, (nodeb_false a hdr).2 ⟨hha, by omega⟩]
    exact upd_neq _ _ _ _ (by omega)
  have hres : ∀ x, qres hdr a (ns.headD 0) h x ≠ none ↔ x ∈ qcells hdr ns := by
    intro x
    have hmem : x ∈ qcells hdr (a :: ns) ↔
        x = hdr ∨ x = hdr + 1 ∨ x = a ∨ x = a + 1 ∨ x ∈ cells ns := by
      simp [qcells, cells]
    simp only [qcells, List.mem_cons, qres]
    cases hb : nodeb a x
    · obtain ⟨hxa, hxsa⟩ := (nodeb_false a x).1 hb
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hx : x = hdr + 1
      · subst hx; simp
      · rw [upd_neq _ _ _ _ hx]
        constructor
        · intro hx'
          rcases hmem.1 (hex x hx') with e | e | e | e | e <;> simp_all
        · intro hx'
          exact hfp x (hmem.2 (by rcases hx' with e | e | e <;> simp_all))
    · simp only [↓reduceIte, ne_eq, not_true_eq_false, false_iff, not_or]
      rcases (nodeb_true a x).1 hb with rfl | rfl
      · exact ⟨hha.symm, by omega, hanc⟩
      · exact ⟨by omega, by omega, hsanc⟩
  refine ⟨fun x => ?_, fun x => ?_, ⟨⟨hwfns, ?_, ?_, ?_, ?_, fun x hx => (hres x).2 hx⟩,
    fun x hx => (hres x).1 hx⟩, ?_, ?_, fun x => ?_⟩
  · simp only [qres, qnode]; split <;> simp
  · simp only [qres, qnode, hunion]
    cases hb : nodeb a x
    · simp only [Bool.false_eq_true, ↓reduceIte]; cases upd h (hdr + 1) (ns.headD 0) x <;> rfl
    · simp only [↓reduceIte]
      rcases (nodeb_true a x).1 hb with rfl | rfl <;> exact upd_neq _ _ _ _ (by omega)
  · simp only [qres, (nodeb_false a (hdr + 1)).2 ⟨hsha, by omega⟩]; exact upd_eq _ _ _
  · cases ns with
    | nil => show qres hdr a _ h hdr ≠ none; rw [hqhdr]; exact hhdrdom
    | cons b ns' =>
      show qres hdr a _ h hdr = some _; rw [hqhdr, htl]; simp
  · refine chain_frame h _ [a, a + 1, hdr + 1] _ _ _ hch (fun x hx => ?_) (fun x hx => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [qres, (nodeb_false a x).2 ⟨hx.1, hx.2.1⟩, Bool.false_eq_true, ↓reduceIte]
      exact upd_neq _ _ _ _ hx.2.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
  · rcases h0 : qres hdr a (ns.headD 0) h 0 with _ | w
    · rfl
    · exact absurd ((hres 0).1 (by rw [h0]; simp)) (qwf_zero _ _ hwfns)
  · simp only [qnode, (nodeb_true a a).2 (.inl rfl), ↓reduceIte]; exact ha
  · simp only [qnode, (nodeb_true a (a + 1)).2 (.inr rfl), ↓reduceIte]; exact hsa
  · simp only [qnode]
    cases hb : nodeb a x
    · simp [(nodeb_false a x).1 hb]
    · simp only [↓reduceIte, (nodeb_true a x).1 hb, iff_true]
      rcases (nodeb_true a x).1 hb with rfl | rfl <;> simp [ha, hsa]

/-- The separating-conjunction reading of the intermediate split. -/
theorem rot_detach_sep (hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (h : Heap) :
    qrep hdr (a :: ns) (v :: vs) h → qex hdr (a :: ns) h →
      ∃ hq hn, hdisj hq hn ∧ heq (upd h (hdr + 1) (ns.headD 0)) (hunion hq hn) ∧
        qrep hdr ns vs hq ∧ nodeat a v (ns.headD 0) hn := fun hq hex =>
  let ⟨h1, h2, ⟨h3, _⟩, h4⟩ := rot_detach_split hdr a ns v vs h hq hex
  ⟨_, _, h1, h2, h3, h4⟩

theorem cells_mono_app (x : Nat) (l1 l2 : List Nat) : x ∈ cells l1 → x ∈ cells (l1 ++ l2) := by
  intro h; simp only [cells, List.flatMap_append, List.mem_append]; exact .inl h

theorem cells_mono_cons (x b : Nat) (l : List Nat) : x ∈ cells l → x ∈ cells (b :: l) :=
  fun h => .tail _ (.tail _ h)

/-! ## The rotation theorem

One completed rotation turns the queue `a :: ns` / `v :: vs` into `ns ++ [a]` / `vs ++ [v]` and
touches no cell outside the queue's footprint. -/

theorem rot_heap_spec (hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (h : Heap) :
    qrep hdr (a :: ns) (v :: vs) h →
      qrep hdr (ns ++ [a]) (vs ++ [v]) (rot_heap hdr a (ns.headD 0) (zof hdr ns) h) ∧
      ∀ x, rot_heap hdr a (ns.headD 0) (zof hdr ns) h x ≠ none ↔ h x ≠ none := by
  rintro ⟨hwf, hhd, htl, hch, hnull, hfp⟩
  obtain ⟨ha, hsa, hch⟩ := (chain_cons _ _ _ _ _ _).1 hch
  obtain ⟨hha, hsha, hhsa, hshsa, hhshdr⟩ := qwf_neqs _ _ _ hwf
  obtain ⟨hanc, hsanc⟩ := qwf_node_cells _ _ _ hwf
  have hhnc := qwf_hdr_cells _ _ hwf
  have hshnc := qwf_shdr_cells _ _ hwf
  have hhdrdom : h hdr ≠ none := hfp _ (.head _)
  have hshdrdom : h (hdr + 1) ≠ none := by rw [hhd]; simp
  have hsadom : h (a + 1) ≠ none := by rw [hsa]; simp
  -- the null cell and the footprint transfer through any domain-preserving rewrite
  have hfinish : ∀ h' : Heap, (∀ x, h' x ≠ none ↔ h x ≠ none) →
      h' 0 = none ∧ ∀ x, x ∈ qcells hdr (ns ++ [a]) → h' x ≠ none := fun h' hd' =>
    ⟨by rcases h0 : h' 0 with _ | w
        · rfl
        · exact absurd hnull ((hd' 0).1 (by rw [h0]; simp)),
      fun x hx => (hd' x).2 (hfp x ((qcells_rot _ _ _ _).1 hx))⟩
  rcases List.eq_nil_or_concat ns with rfl | ⟨ns0, zz, rfl⟩
  · -- one element: detaching empties the queue and the append re-links the header itself
    cases vs with
    | cons _ _ => exact absurd (chain_len _ _ _ _ hch) (by simp)
    | nil =>
    show qrep hdr [a] [v] (rot_heap hdr a 0 hdr h) ∧ ∀ x, rot_heap hdr a 0 hdr h x ≠ none ↔ _
    have hdom' := rot_heap_dom hdr a 0 hdr h hshdrdom hshdrdom hsadom hhdrdom
    have hra : rot_heap hdr a 0 hdr h a = some v := by
      rw [rot_heap_other _ _ _ _ _ _ hha.symm (by omega) (by omega) (by omega)]; exact ha
    exact ⟨⟨hwf, rot_heap_sz _ _ _ _ _ (by omega) hha, rot_heap_hdr _ _ _ _ _,
      (chain_cons _ _ _ _ _ _).2 ⟨hra, rot_heap_sa _ _ _ _ _ (by omega), chain_nil _ _⟩,
      hfinish _ hdom'⟩, hdom'⟩
  · -- the general case: the append re-links the old last node `zz`
    rw [List.concat_eq_append] at *
    have hzz : zz ∈ ns0 ++ [zz] := List.mem_append_right _ (.head _)
    obtain ⟨hzh, hza, hzsh, hzsa, hszh, hsza, hszsh, hszsa⟩ := qwf_neqs_mem _ _ _ _ hwf hzz
    rw [zof_snoc]
    obtain ⟨vs0, vz, rfl⟩ : ∃ vs0 vz, vs = vs0 ++ [vz] := by
      rcases List.eq_nil_or_concat vs with rfl | ⟨vs0, vz, rfl⟩
      · exact absurd (chain_len _ _ _ _ hch) (by simp)
      · exact ⟨vs0, vz, List.concat_eq_append ..⟩
    have hlen : ns0.length = vs0.length := by have := chain_len _ _ _ _ hch; simp at this; omega
    obtain ⟨hch0, hchz⟩ := chain_split _ _ _ _ _ _ hlen hch
    obtain ⟨hzv, hszv, -⟩ := (chain_cons _ _ _ _ _ _).1 hchz
    have hszdom : h (zz + 1) ≠ none := by rw [hszv]; simp
    have hdom' := rot_heap_dom hdr a ((ns0 ++ [zz]).headD 0) zz h hshdrdom hszdom hsadom hhdrdom
    refine ⟨⟨qwf_perm _ _ _ (rotl_perm (a :: (ns0 ++ [zz]))) hwf, ?_, ?_, ?_, hfinish _ hdom'⟩,
      hdom'⟩
    · rw [rot_heap_shdr _ _ _ _ _ hha (Ne.symm hzh)]; cases ns0 <;> rfl
    · unfold tailok; split
      · simp at *
      · rw [rot_heap_hdr]; simp
    · refine chain_app _ _ _ [a] [v] _ (chain_app _ _ _ [zz] [vz] _ ?_ ?_) ?_
      · -- the nodes that stay in place are untouched
        refine chain_frame h _ [hdr, hdr + 1, a + 1, zz + 1] _ _ _ hch0 (fun x hx => ?_)
          (fun x hx hin => ?_)
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          exact rot_heap_other _ _ _ _ _ _ hx.1 hx.2.2.1 hx.2.2.2 hx.2.1
        · have hin' : x ∈ cells (ns0 ++ [zz]) := cells_mono_app _ _ _ hin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hhnc (cells_mono_cons _ _ _ hin')
          · exact hshnc (cells_mono_cons _ _ _ hin')
          · exact hsanc hin'
          · -- `zz + 1` is the link the append rewrites; no staying node owns it
            obtain ⟨c, hc, e | e⟩ := (in_cells _ _).1 hin
            · exact hwf.2.2 c zz (.tail _ (.tail _ (List.mem_append_left _ hc))) (.tail _ (.tail _
                hzz)) e.symm
            · obtain rfl : c = zz := by omega
              have hnd := (List.nodup_cons.1 (List.nodup_cons.1 hwf.1).2).2
              exact (List.nodup_append.1 hnd).2.2 c hc c (.head _) rfl
      · have hrz : rot_heap hdr a ((ns0 ++ [zz]).headD 0) zz h zz = some vz := by
          rw [rot_heap_other _ _ _ _ _ _ hzh (by omega) (by omega) hzsh]; exact hzv
        exact (chain_cons _ _ _ _ _ _).2 ⟨hrz, rot_heap_sz _ _ _ _ _ hszh hza, chain_nil _ _⟩
      · have hra : rot_heap hdr a ((ns0 ++ [zz]).headD 0) zz h a = some v := by
          rw [rot_heap_other _ _ _ _ _ _ hha.symm (by omega) (by omega) (by omega)]; exact ha
        exact (chain_cons _ _ _ _ _ _).2 ⟨hra, rot_heap_sa _ _ _ _ _ (by omega), chain_nil _ _⟩

/-! ## Two facts the language layer needs about the rotation's footprint -/

/-- The cell the append phase writes is always already allocated. -/
theorem qrep_zof_dom (hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (h : Heap) :
    qrep hdr (a :: ns) (v :: vs) h → h (zof hdr ns + 1) ≠ none := by
  rintro ⟨-, hhd, -, -, -, hfp⟩
  cases ns with
  | nil => show h (hdr + 1) ≠ none; rw [hhd]; simp
  | cons b ns1 =>
    refine hfp _ (.tail _ (.tail _ ((in_cells _ _).2 ⟨(b :: ns1).getLastD 0, ?_, .inr rfl⟩)))
    exact .tail _ (last_in _ _ (by simp))

/-- The address the program computes for the append is exactly `zof`. -/
theorem zof_compute (hdr a : Nat) (ns : List Nat) :
    qwf hdr (a :: ns) →
      (if ns.headD 0 == 0 then hdr else (a :: ns).getLastD 0) = zof hdr ns := by
  rintro ⟨-, h0, -⟩
  cases ns with
  | nil => rfl
  | cons b ns1 =>
    have hb : b ≠ 0 := by rintro rfl; exact h0 (.tail _ (.tail _ (.head _)))
    simp [hb, zof]

end Examples.CSL.Queue.Representation
