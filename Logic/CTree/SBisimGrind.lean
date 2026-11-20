/- SPDX-License-Identifier: MIT -/
module
-- Lean-only module, no Rocq counterpart.

public import CTree

/-!
# `grind` up to strong bisimulation

`grind` closes goals up to `=` only. Its preprocessor rewrites every `t ~ u` (`sbisim Eq`) to the
equality `sbq t = sbq u` of strong-bisimilarity classes, so `~` hypotheses, goals and instances
of `~` lemmas enter the congruence closure: reflexivity, symmetry and transitivity of `~` are free,
and `=` rewrites of the trees inside compose with them. `sbisim` is never a pattern symbol, so
`@[grind .]` on a `~` lemma triggers on `sbq` of its left-hand tree (plain `@[grind]` also prints
its pattern choice). `>>=` is a congruence in its first argument (`sbq_bind_eq`), and
guards vanish (`sb_guard`).

`grind` never rewrites under a binder: in `(t >>= fun _ => pure r) >>= k`, reassociation strands
`pure r >>= k` under `fun _`. Equations that answer `r` after a prefix `t` therefore state it as
`Functor.mapConst r t`, and `mapConst_bind` puts `k r` where the congruence closure sees it.
-/

@[expose] public section
namespace Tisl
open CTree Coinduction
open ITree (Effect)

variable {E C : Effect.{u}} {X Y : Type u}

/-- Strong bisimilarity `~` as a setoid. -/
def sbisimSetoid (E C : Effect.{u}) (X : Type u) : Setoid (CTree E C X) :=
  ⟨sbisim Eq, sbisim_equivalence ⟨fun _ => rfl, .symm, .trans⟩⟩

/-- The strong-bisimilarity class of a tree. -/
def sbq (t : CTree E C X) : Quotient (sbisimSetoid E C X) := Quotient.mk _ t

@[grind norm] theorem sbisim_iff_sbq {t u : CTree E C X} : t ~ u ↔ sbq t = sbq u :=
  ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

attribute [grind symbol 0] sbisim

/-- `>>=` on classes, through its first argument. -/
def sbq_bind (q : Quotient (sbisimSetoid E C X)) (k : X → CTree E C Y) :
    Quotient (sbisimSetoid E C Y) :=
  Quotient.lift (fun t => sbq (t >>= k))
    (fun _ _ h => sbisim_iff_sbq.1 (sbisim_clo_bind_eq h fun _ => sbisim_refl _)) q

@[grind =] theorem sbq_bind_eq (t : CTree E C X) (k : X → CTree E C Y) :
    sbq (t >>= k) = sbq_bind (sbq t) k := rfl

attribute [grind .] sb_guard
attribute [grind =] stuck_bind translate_ret translate_stuck

@[grind =] theorem mapConst_bind {Z : Type u} (x : X) (t : CTree E C Y) (k : X → CTree E C Z) :
    (Functor.mapConst x t >>= k) = (t >>= fun _ => k x) := by
  show ((t >>= fun _ => pure x) >>= k) = _
  rw [bind_assoc]; simp only [pure_bind]

end Tisl
