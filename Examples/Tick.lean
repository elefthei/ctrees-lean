/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Iter
public import Logic.CTree.Bind

/-!
# Tick-tock

A loop that repeatedly makes a visible binary choice between `tick` and `tock`; some infinite path
observes `tock` forever (← `examples/Tick.v`).
-/

@[expose] public section
namespace Examples.Tick
open CTree Tisl Tisl.Notation
open ITree (Effect)

/-- The two clock events (Rocq `Tick`, `Tock : tickE unit`). -/
inductive TickOp
  | tick
  | tock

/-- The clock effect: both events answer `⟨⟩`. -/
@[implicit_reducible] def tickE : Effect.{0} := ⟨TickOp, fun _ => PUnit⟩
unif_hint (x : tickE.I) where |- tickE.O x ≟ PUnit

def tick : CTree tickE B2 PUnit := CTree.trigger (E := tickE) TickOp.tick
def tock : CTree tickE B2 PUnit := CTree.trigger (E := tickE) TickOp.tock

/-! ## Example 1: non-deterministic loop calling `tick`

The choices are observable scheduling choices, hence visible (`brS2`). -/

def tocker : CTree tickE B2 PUnit :=
  CTree.iter (fun _ : PUnit => Sum.inl <$> CTree.brS2 (CTree.brS2 tick tock) tick) ⟨⟩

/-- Specification: there exists an infinite path that always `tock`s. -/
theorem eg_tock :
    entails (EG visₜ (fun e _ => e = TickOp.tock)) tocker (.obs (E := tickE) TickOp.tock ⟨⟩) := by
  refine eg_iter (fun _ w => w = .obs (E := tickE) TickOp.tock ⟨⟩) rfl ?_
  rintro ⟨⟩ w rfl
  have hφ {Y : Type} (t : CTree tickE B2 Y) :
      entails (visₜ (fun (e : tickE.I) _ => e = TickOp.tock)) t (.obs TickOp.tock ⟨⟩) :=
    ⟨.obs _ _ rfl, .obs _ _⟩
  have hbr (t u : CTree tickE B2 PUnit) :
      CTree.brS2 t u = .brS (B := B2) ⟨⟩ fun b => if b.down then t else u := rfl
  refine ⟨hφ _, ?_⟩
  simp only [hbr, map_brS]
  apply en_brS.2
  refine ⟨⟨trivial, .obs _ _⟩, ⟨true⟩, ?_⟩
  simp only [ite_true, map_brS]
  apply eu_brS.1
  right; refine ⟨hφ _, ⟨false⟩, ?_⟩
  simp only [Bool.false_eq_true, ite_false, tock, CTree.trigger, map_vis]
  apply eu_vis.1
  right; refine ⟨hφ _, ⟨⟩, ?_⟩
  rw [map_pure]
  apply eu_ret.1
  exact Or.inl (ret_ret (.obs _ _) ⟨⟨⟩, rfl, rfl⟩)

end Examples.Tick
