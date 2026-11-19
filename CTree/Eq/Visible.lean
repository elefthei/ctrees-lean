/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.Equ

/-!
# Visible nodes

`visible t u` holds when `u` is the first observable node of `t` (a `step`, `vis` or `ret` node),
reached by crossing `br` and `guard` nodes (← `Eq/Visible.v`). Structural equality is `=`, so the
Rocq `Proper` instances w.r.t. `equ` are not needed.
-/

@[expose] public section
namespace CTree
open ITree (Effect)

variable {E C : Effect.{u}} {R : Type u}

/-- `visible` on unfolded trees. -/
inductive Visible_ : CTreeF E C R (CTree E C R) → CTreeF E C R (CTree E C R) → Prop
  | br {c : C.I} (x : C.O c) {k : C.O c → CTree E C R} {t} :
      Visible_ (k x).unfold t → Visible_ (.br c k) t
  | guard {t : CTree E C R} {t'} : Visible_ t.unfold t' → Visible_ (.guard t) t'
  | step {t t' : CTree E C R} : t = t' → Visible_ (.step t) (.step t')
  | vis {e : E.I} {k₁ k₂ : E.O e → CTree E C R} :
      (∀ x, k₁ x = k₂ x) → Visible_ (.vis e k₁) (.vis e k₂)
  | ret (r : R) : Visible_ (.ret r) (.ret r)

def visible (t u : CTree E C R) : Prop := Visible_ t.unfold u.unfold

end CTree
