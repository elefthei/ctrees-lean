/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.AsepCore
public import Lang.CoCSL.Owned
public import Examples.CSL.Frame.Shared

/-!
# Active separation: operational next regression

After an admitted fork of two writers on disjoint cells, the parent's write is one visible
action of a single owner: the global step advances exactly one lineage's local world and leaves
the other lineage untouched (← `examples/CSL/Frame/Active.v`, module
`OperationalNextRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.OperationalNextRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm CoCSL
open Examples.CSL.Frame.Shared

def cfg : OwnedCfg := init_owned (.write 1 4) (.write 2 6) (region 1 3) (region 2 5) [] 0

def initial : AsepState := { cfg := cfg, global := .pure, loc := fun _ => .pure }

theorem admitted : admissible (.write 1 4) (.write 2 6) (region 1 3) (region 2 5) [] 0 :=
  admissible_regions _ _ _ _ _ _ _ _ (by decide) trivial trivial
    (by simp [addr_ok, region, hsingle]) (by simp [addr_ok, region, hsingle])

theorem initial_ok : asep_state_ok initial :=
  ⟨admissible_active_erasable _ _ _ _ _ _ admitted, .pure, fun _ => .pure⟩

def post : OwnedCfg :=
  set_pool (set_heap cfg .parent (upd (region 2 5).1 2 6, (region 2 5).2))
    (mk_pool 2 #v[denote (.write 1 4), pure ⟨⟩] #v[.child, .parent] (some 1))

theorem write_step : owned_step cfg (act .parent .write) post := by
  show focus_step cfg 1 #v[denote (.write 1 4), denote (.write 2 6)] #v[.child, .parent] 1
    (act .parent .write) post
  refine .inr (.inr (.inr (.inr ⟨.inl (.write 2 6), fun _ => pure ⟨⟩, .write, ⟨⟩,
    set_heap cfg .parent (upd (region 2 5).1 2 6, (region 2 5).2),
    ⟨0, ?_⟩, ?_, rfl, ?_⟩)))
  · exact source_raw_write_head _ _ _
  · simp [prim_step, heap_prim, cfg, init_owned, init_owned_threads, region, hsingle]
  · rfl

theorem one_write_has_single_owner :
    ∃ t' s' u i,
      ktrans (owned_interp cfg) .pure t'
        (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (joined_heap post)) ⟨⟩) ∧
      asep_frontier initial s' ∧ t' ~ owned_interp s'.cfg ∧
      ktrans (owned_interp (project i cfg)) .pure u (s'.loc i) ∧
      u ~ owned_interp (project i s'.cfg) ∧
      owned_interp (project (other i) s'.cfg) ~ owned_interp (project (other i) cfg) ∧
      s'.loc (other i) = .pure := by
  obtain ⟨t', HT, -⟩ := owned_interp_visible cfg cfg (act .parent .write) post
    (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (joined_heap post)) ⟨⟩)
    initial_ok.1.1 .refl write_step rfl
  have HK : ktrans (owned_interp cfg) .pure t'
      (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (joined_heap post)) ⟨⟩) :=
    owned_label_ktrans (act .parent .write) (joined_heap post) _ _ _ .pure rfl HT .pure
  obtain ⟨s', u, i, Hfront, Et, -, HC⟩ :=
    asep_visible_forward_owner initial t' _ initial_ok HK (.obs _ _)
  exact ⟨t', s', u, i, HK, Hfront, Et, HC⟩

end Examples.CSL.Frame.Active.OperationalNextRegression
