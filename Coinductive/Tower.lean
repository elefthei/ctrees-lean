/- SPDX-License-Identifier: MIT -/
module

public meta import Lean.Elab.Tactic.ElabTerm

/-!
# Coinduction via the final chain (tower induction)

A Lean port of Damien Pous's `coinduction` library (`tower.v`, `rel.v`): the greatest fixpoint of a
monotone function `b` on a complete lattice is the least element of the *final chain* `Chain b`,
the closure of the top element under `b` and arbitrary infima. Reasoning about chain elements
(`tower`) gives coinduction up-to for free.

## Usage pattern

The tactics `coinduction R hR CIH` and `step` are the ones of the Rocq library:
```
theorem foo : ∀ a, sbisim L (f a) (g a) := by
  coinduction R hR CIH
  -- hR : Chain (sb L) R, CIH : ∀ a, R (f a) (g a) ⊢ ∀ a, sb L R (f a) (g a)
  intro a
  …  -- use `step` on goals `R x y`, `gfp_le_chain hR`, chain-closure lemmas with `hR`
```
Hypotheses of the coinductive statement are binders of the goal: `∀ a, P a → gfp b (f a) (g a)`.
On a hypothesis, `gfp_pfp _ _ h` unfolds `gfp` once.
-/

@[expose] public section
namespace Coinduction

/-- The complete-lattice fragment the tower needs (arbitrary infima). -/
class Lattice (X : Type u) where
  le : X → X → Prop
  inf : (X → Prop) → X
  le_refl (x : X) : le x x
  le_trans {x y z : X} : le x y → le y z → le x z
  le_antisymm {x y : X} : le x y → le y x → x = y
  inf_le {T : X → Prop} {x : X} : T x → le (inf T) x
  le_inf {T : X → Prop} {y : X} : (∀ x, T x → le y x) → le y (inf T)

instance (priority := low) {X : Type u} [Lattice X] : LE X := ⟨Lattice.le⟩
export Lattice (inf)

section Lattice
variable {X : Type u} [Lattice X]

theorem le_refl (x : X) : x ≤ x := Lattice.le_refl x
theorem le_trans {x y z : X} : x ≤ y → y ≤ z → x ≤ z := Lattice.le_trans
theorem le_antisymm {x y : X} : x ≤ y → y ≤ x → x = y := Lattice.le_antisymm
theorem inf_le {T : X → Prop} {x : X} : T x → inf T ≤ x := Lattice.inf_le
theorem le_inf {T : X → Prop} {y : X} : (∀ x, T x → y ≤ x) → y ≤ inf T := Lattice.le_inf

/-- Binary meet. -/
def cap (x y : X) : X := inf fun z => z = x ∨ z = y

theorem cap_le_left (x y : X) : cap x y ≤ x := inf_le (.inl rfl)
theorem cap_le_right (x y : X) : cap x y ≤ y := inf_le (.inr rfl)
theorem le_cap {x y z : X} (h₁ : z ≤ x) (h₂ : z ≤ y) : z ≤ cap x y :=
  le_inf fun _ h => h.elim (· ▸ h₁) (· ▸ h₂)

end Lattice

instance : Lattice Prop where
  le p q := p → q
  inf T := ∀ p, T p → p
  le_refl _ := id
  le_trans h₁ h₂ := h₂ ∘ h₁
  le_antisymm h₁ h₂ := propext ⟨h₁, h₂⟩
  inf_le h₁ h₂ := h₂ _ h₁
  le_inf h hy p hp := h p hp hy

instance {α : Type v} {Y : Type w} [Lattice Y] : Lattice (α → Y) where
  le f g := ∀ a, f a ≤ g a
  inf T a := inf fun y => ∃ f, T f ∧ f a = y
  le_refl f a := le_refl (f a)
  le_trans h₁ h₂ a := le_trans (h₁ a) (h₂ a)
  le_antisymm h₁ h₂ := funext fun a => le_antisymm (h₁ a) (h₂ a)
  inf_le h _ := inf_le ⟨_, h, rfl⟩
  le_inf h a := le_inf fun _ ⟨f, hf, e⟩ => e ▸ h f hf a

/-- Binary relations. -/
abbrev Rel (α : Type u) (β : Type v) := α → β → Prop
/-- Predicates. -/
abbrev Pred (α : Type u) := α → Prop

@[simp] theorem Prop.le_def {p q : Prop} : p ≤ q ↔ (p → q) := Iff.rfl
@[simp] theorem Prop.inf_def {T : Prop → Prop} : inf T ↔ ∀ p, T p → p := Iff.rfl

theorem Fun.le_def {α : Type v} {Y : Type w} [Lattice Y] {f g : α → Y} :
    f ≤ g ↔ ∀ a, f a ≤ g a := Iff.rfl
theorem Fun.inf_apply {α : Type v} {Y : Type w} [Lattice Y] {T : (α → Y) → Prop} {a : α} :
    inf T a = inf fun y => ∃ f, T f ∧ f a = y := rfl

@[simp] theorem Pred.le_def {α : Type u} {P Q : Pred α} : P ≤ Q ↔ ∀ x, P x → Q x := Iff.rfl
@[simp] theorem Pred.inf_apply {α : Type u} {T : Pred α → Prop} {x : α} :
    inf T x ↔ ∀ P, T P → P x :=
  ⟨fun h P hP => h _ ⟨P, hP, rfl⟩, fun h _ ⟨P, hP, e⟩ => e ▸ h P hP⟩

@[simp] theorem Rel.le_def {α : Type u} {β : Type v} {R S : Rel α β} :
    R ≤ S ↔ ∀ x y, R x y → S x y := Iff.rfl
@[simp] theorem Rel.inf_apply {α : Type u} {β : Type v} {T : Rel α β → Prop} {x : α} {y : β} :
    inf T x y ↔ ∀ R, T R → R x y :=
  ⟨fun h R hR => h _ ⟨_, ⟨R, hR, rfl⟩, rfl⟩, fun h _ ⟨_, ⟨R, hR, e₁⟩, e₂⟩ => e₂ ▸ e₁ ▸ h R hR⟩

/-- Ternary relations (e.g. `Bool`-indexed families of relations). -/
abbrev Rel3 (γ : Type w) (α : Type u) (β : Type v) := γ → α → β → Prop

@[simp] theorem Rel3.le_def {γ : Type w} {α : Type u} {β : Type v} {R S : Rel3 γ α β} :
    R ≤ S ↔ ∀ c x y, R c x y → S c x y := Iff.rfl
@[simp] theorem Rel3.inf_apply {γ : Type w} {α : Type u} {β : Type v} {T : Rel3 γ α β → Prop}
    {c : γ} {x : α} {y : β} : inf T c x y ↔ ∀ R, T R → R c x y :=
  ⟨fun h R hR => h _ ⟨_, ⟨_, ⟨R, hR, rfl⟩, rfl⟩, rfl⟩,
   fun h _ ⟨_, ⟨_, ⟨R, hR, e₁⟩, e₂⟩, e₃⟩ => e₃ ▸ e₂ ▸ e₁ ▸ h R hR⟩

@[simp] theorem Pred.cap_apply {α : Type u} {P Q : Pred α} {x : α} : cap P Q x ↔ P x ∧ Q x := by
  simp only [cap, Pred.inf_apply]
  exact ⟨fun h => ⟨h _ (.inl rfl), h _ (.inr rfl)⟩, fun h _ e => e.elim (· ▸ h.1) (· ▸ h.2)⟩

@[simp] theorem Rel.cap_apply {α : Type u} {β : Type v} {R S : Rel α β} {x : α} {y : β} :
    cap R S x y ↔ R x y ∧ S x y := by
  simp only [cap, Rel.inf_apply]
  exact ⟨fun h => ⟨h _ (.inl rfl), h _ (.inr rfl)⟩, fun h _ e => e.elim (· ▸ h.1) (· ▸ h.2)⟩

@[simp] theorem Rel3.cap_apply {γ : Type w} {α : Type u} {β : Type v} {R S : Rel3 γ α β} {c : γ}
    {x : α} {y : β} : cap R S c x y ↔ R c x y ∧ S c x y := by
  simp only [cap, Rel3.inf_apply]
  exact ⟨fun h => ⟨h _ (.inl rfl), h _ (.inr rfl)⟩, fun h _ e => e.elim (· ▸ h.1) (· ▸ h.2)⟩

/-- Monotone endofunctions. -/
structure Mon (X : Type u) [Lattice X] where
  body : X → X
  mono {x y : X} : x ≤ y → body x ≤ body y

instance {X : Type u} [Lattice X] : CoeFun (Mon X) fun _ => X → X := ⟨Mon.body⟩

section Tower
variable {X : Type u} [Lattice X] (b : Mon X)

/-- The final chain: all (transfinite) iterations of `b` from the top element. -/
inductive Chain : X → Prop
  | step {x} : Chain x → Chain (b x)
  | inf {T : X → Prop} : (∀ x, T x → Chain x) → Chain (inf T)

/-- The greatest fixpoint of `b`, the least element of the final chain. -/
def gfp : X := inf (Chain b)

/-- Predicates closed under arbitrary infima. -/
def InfClosed (P : X → Prop) : Prop := ∀ T, (∀ x, T x → P x) → P (inf T)

variable {b}

/-- Tower induction: an inf-closed predicate preserved by `b` holds on the whole chain. -/
theorem tower {P : X → Prop} (hinf : InfClosed P) (hb : ∀ x, Chain b x → P x → P (b x)) :
    ∀ x, Chain b x → P x := by
  intro x hx
  induction hx with
  | step hx ih => exact hb _ hx ih
  | inf _ ih => exact hinf _ ih

variable (b) in
theorem gfp_chain : Chain b (gfp b) := .inf fun _ h => h

theorem gfp_prop {P : X → Prop} (h : ∀ x, Chain b x → P x) : P (gfp b) := h _ (gfp_chain b)

theorem gfp_le_chain {x : X} (hx : Chain b x) : gfp b ≤ x := inf_le hx

theorem infClosed_le (f : Mon X) : InfClosed fun x => f x ≤ x :=
  fun _ hT => le_inf fun x hx => le_trans (f.mono (inf_le hx)) (hT x hx)

theorem infClosed_forall {ι : Sort w} {P : ι → X → Prop} (h : ∀ i, InfClosed (P i)) :
    InfClosed fun x => ∀ i, P i x :=
  fun T hT i => h i T fun x hx => hT x hx i

theorem infClosed_imp {Q P : X → Prop} (hQ : ∀ {x y}, x ≤ y → Q x → Q y) (hP : InfClosed P) :
    InfClosed fun x => Q x → P x :=
  fun T hT hq => hP T fun x hx => hT x hx (hQ (inf_le hx) hq)

theorem infClosed_and {Q P : X → Prop} (hQ : InfClosed Q) (hP : InfClosed P) :
    InfClosed fun x => Q x ∧ P x :=
  fun T hT => ⟨hQ T fun x hx => (hT x hx).1, hP T fun x hx => (hT x hx).2⟩

/-- Elements of the chain are pre-fixpoints of `b`: `b x ≤ x`. -/
theorem b_chain {x : X} (hx : Chain b x) : b x ≤ x :=
  tower (infClosed_le b) (fun _ _ h => b.mono h) x hx

theorem gfp_pfp : gfp b ≤ b (gfp b) := inf_le (.step (gfp_chain b))

theorem gfp_fp : b (gfp b) = gfp b := le_antisymm (b_chain (gfp_chain b)) gfp_pfp

/-- `gfp b` is the greatest post-fixpoint. -/
theorem le_gfp {x : X} (h : x ≤ b x) : x ≤ gfp b :=
  le_inf <| tower (P := (x ≤ ·)) (fun _ hT => le_inf hT) fun _ _ hy => le_trans h (b.mono hy)

theorem gfp_mono {b c : Mon X} (h : ∀ x, b x ≤ c x) : gfp b ≤ gfp c :=
  le_gfp (le_trans gfp_pfp (h _))

variable (b) in
/-- `f` is compatible with `b`. -/
def Compat (f : X → X) : Prop := ∀ x, f (b x) ≤ b (f x)

theorem compat_chain (f : Mon X) (hf : Compat b f) : ∀ x, Chain b x → f x ≤ x :=
  tower (infClosed_le f) fun x _ h => le_trans (hf x) (b.mono h)

end Tower

theorem Rel.infClosed_apply {α : Type u} {β : Type v} (a : α) (c : β) :
    InfClosed fun R : Rel α β => R a c :=
  fun _ hT => Rel.inf_apply.2 hT

theorem Rel3.infClosed_apply {γ : Type w} {α : Type u} {β : Type v} (i : γ) (a : α) (c : β) :
    InfClosed fun R : Rel3 γ α β => R i a c :=
  fun _ hT => Rel3.inf_apply.2 hT

/-! ## Relations (`rel.v`) -/

section Rel
variable {α : Type u} {b : Mon (Rel α α)}

theorem refl_chain (h : ∀ R, Chain b R → (∀ x, R x x) → ∀ x, b R x x) :
    ∀ R, Chain b R → ∀ x, R x x :=
  tower (infClosed_forall fun x => Rel.infClosed_apply x x) h

theorem symm_chain (h : ∀ R, Chain b R → (∀ x y, R x y → R y x) → ∀ x y, b R x y → b R y x) :
    ∀ R, Chain b R → ∀ x y, R x y → R y x :=
  tower (fun _ hT x y hxy => Rel.inf_apply.2 fun R hR => hT R hR x y (Rel.inf_apply.1 hxy R hR)) h

theorem trans_chain
    (h : ∀ R, Chain b R → (∀ x y z, R x y → R y z → R x z) →
      ∀ x y z, b R x y → b R y z → b R x z) :
    ∀ R, Chain b R → ∀ x y z, R x y → R y z → R x z :=
  tower (fun _ hT x y z hxy hyz => Rel.inf_apply.2 fun R hR =>
    hT R hR x y z (Rel.inf_apply.1 hxy R hR) (Rel.inf_apply.1 hyz R hR)) h

variable (α) in
/-- The converse of a relation, as a monotone function. -/
def converse : Mon (Rel α α) := ⟨fun R x y => R y x, fun h _ _ => h _ _⟩

@[simp] theorem converse_apply {R : Rel α α} {x y : α} : converse α R x y ↔ R y x := Iff.rfl

end Rel

/-! ## Symmetry arguments -/

/-- `b x = s x ⊓ i (s (i x))` for an involution `i` (`Symmetrical` in tower.v). -/
structure Symmetrical {X : Type u} [Lattice X] (i b s : Mon X) : Prop where
  invol : ∀ x, i (i x) = x
  eq : ∀ x, b x = cap (s x) (i (s (i x)))

namespace Symmetrical
variable {X : Type u} [Lattice X] {i b s : Mon X}

theorem invol_compat (h : Symmetrical i b s) : Compat b i := by
  intro x
  rw [h.eq, h.eq, h.invol]
  exact le_cap (le_trans (i.mono (cap_le_right _ _)) (by rw [h.invol]; exact le_refl _))
    (i.mono (cap_le_left _ _))

theorem invol_chain (h : Symmetrical i b s) {x : X} (hx : Chain b x) : i x = x := by
  have h₁ := compat_chain i h.invol_compat x hx
  exact le_antisymm h₁ (by have := i.mono h₁; rwa [h.invol] at this)

theorem chain_eq (h : Symmetrical i b s) {x : X} (hx : Chain b x) :
    b x = cap (s x) (i (s x)) := by
  rw [h.eq, h.invol_chain hx]

theorem pfp (h : Symmetrical i b s) {x : X} (hi : i x ≤ x) (hs : x ≤ s x) : x ≤ b x := by
  have hx : i x = x :=
    le_antisymm hi (by have := i.mono hi; rwa [h.invol] at this)
  rw [h.eq, hx]
  exact le_cap hs (le_trans (by rw [hx]; exact le_refl _) (i.mono hs))

end Symmetrical

section SymRel
variable {α : Type u} {b s : Mon (Rel α α)}

theorem symm_symchain (h : Symmetrical (converse α) b s) :
    ∀ R, Chain b R → ∀ x y, R x y → R y x := by
  intro R hR x y hxy
  rw [← h.invol_chain hR] at hxy
  exact hxy

theorem symchain_iff (h : Symmetrical (converse α) b s) {R : Rel α α} (hR : Chain b R) {x y : α} :
    b R x y ↔ s R x y ∧ s R y x := by
  rw [h.chain_eq hR]; exact Rel.cap_apply

theorem refl_symchain (h : Symmetrical (converse α) b s)
    (hs : ∀ R, Chain b R → (∀ x, R x x) → ∀ x, s R x x) : ∀ R, Chain b R → ∀ x, R x x :=
  refl_chain fun R hR hrefl x => (symchain_iff h hR).2 ⟨hs R hR hrefl x, hs R hR hrefl x⟩

theorem trans_symchain (h : Symmetrical (converse α) b s)
    (hs : ∀ R, Chain b R → (∀ x y z, R x y → R y z → R x z) →
      ∀ x y z, s R x y → s R y z → s R x z) :
    ∀ R, Chain b R → ∀ x y z, R x y → R y z → R x z :=
  trans_chain fun R hR htrans x y z hxy hyz => by
    rw [symchain_iff h hR] at hxy hyz ⊢
    exact ⟨hs R hR htrans _ _ _ hxy.1 hyz.1, hs R hR htrans _ _ _ hyz.2 hxy.2⟩

end SymRel

/-! ## Tactics (Rocq `coinduction`, `step`) -/

section Tactics
open Lean Meta Elab Tactic

/-- Unfold the head of `e` until it is an application `gfp b args`; returns `gfp b` and `args`. -/
private meta partial def gfpApp? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let e ← whnfCore e
  if e.isAppOf ``gfp && e.getAppNumArgs > 3 then
    let args := e.getAppArgs
    return some (mkAppN e.getAppFn (args.extract 0 3), args.extract 3 args.size)
  match ← unfoldDefinition? e with
  | some e => gfpApp? e
  | none => return none

/-- `inf T args ↔ ∀ R, T R → R args` at the given arity. -/
private meta def infApply : Nat → MetaM Name
  | 1 => pure ``Pred.inf_apply
  | 2 => pure ``Rel.inf_apply
  | 3 => pure ``Rel3.inf_apply
  | k => throwError "coinduction: relations of arity {k} are not supported"

/-- `coinduction R hR CIH` on a goal `∀ xs, gfp b args` (the head may be a definition unfolding
to `gfp b`) introduces a chain element `R` with `hR : Chain b R` and the coinduction hypothesis
`CIH : ∀ xs, R args`, and leaves `∀ xs, b R args`. Proved by `tower` with the predicate
`fun R => ∀ xs, R args`, so `CIH` may be used under any `b`-step taken with chain lemmas. -/
syntax (name := coinductionTac) &"coinduction" ppSpace binderIdent ppSpace binderIdent ppSpace
  binderIdent : tactic

elab_rules : tactic
  | `(tactic| coinduction $R $hR $cih) => do
    let g ← getMainGoal
    g.withContext do
    -- `have`/`let` leave an mdata annotation that `forallTelescope` does not see through
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let (P, hinf, hTy, gb) ← forallTelescope ty fun xs body => do
      let some (gb, as) ← gfpApp? body
        | throwError "coinduction: the goal is not of the form `∀ xs, gfp b args`"
      let #[X, inst, b] := gb.getAppArgs | throwError "coinduction: unexpected `gfp` term"
      if xs.any (gb.containsFVar ·.fvarId!) then
        throwError "coinduction: `{gb}` depends on a quantified variable; introduce it first"
      let lem ← infApply as.size
      -- `P R := ∀ xs, R args`
      let P ← withLocalDeclD `R X fun R => do
        mkLambdaFVars #[R] (← mkForallFVars xs (mkAppN R as))
      -- `InfClosed P`: `fun T hT xs => (inf_apply).2 fun R hR => hT R hR xs`
      let hinf ← withLocalDeclD `T (← mkArrow X (mkSort .zero)) fun T => do
        let hTTy ← withLocalDeclD `x X fun x => do
          mkForallFVars #[x] (← mkArrow (mkApp T x) (P.beta #[x]))
        withLocalDeclD `hT hTTy fun hT => do
          let pick ← withLocalDeclD `R X fun R => withLocalDeclD `hR (mkApp T R) fun hR =>
            mkLambdaFVars #[R, hR] (mkAppN (mkApp2 hT R hR) xs)
          let iff ← mkAppOptM lem
            ((Array.replicate as.size none).push (some T) ++ as.map some)
          mkLambdaFVars #[T, hT] (← mkLambdaFVars xs (← mkAppM ``Iff.mpr #[iff, pick]))
      -- `∀ R, Chain b R → P R → P (b R)`
      let hTy ← withLocalDeclD `R X fun R => do
        let chain ← mkAppOptM ``Chain #[X, inst, b, R]
        let bR ← mkAppOptM ``Mon.body #[X, inst, b, R]
        mkForallFVars #[R] (← mkArrow chain (← mkArrow (P.beta #[R])
          (← mkForallFVars xs (mkAppN bR as))))
      return (P, hinf, hTy, gb)
    let #[X, inst, b] := gb.getAppArgs | throwError "coinduction: unexpected `gfp` term"
    let h ← mkFreshExprSyntheticOpaqueMVar hTy (← g.getTag)
    let pf ← mkAppOptM ``gfp_prop #[X, inst, b, P,
      ← mkAppOptM ``tower #[X, inst, b, P, hinf, h]]
    unless ← isDefEq (← inferType pf) ty do
      throwError "coinduction: could not match the goal with `{P} ({gb})`"
    g.assign pf
    replaceMainGoal [h.mvarId!]
    let names ← #[R, hR, cih].mapM fun
      | `(binderIdent| $i:ident) => pure (⟨i.raw⟩ : Term)
      | _ => `(_)
    evalTactic (← `(tactic| intro $names*))

/-- `step` unfolds the goal one step: `gfp b args` becomes `b (gfp b) args`, and `R args` becomes
`b R args` when a hypothesis `Chain b R` is in context (the head may be a definition unfolding to
either form). -/
syntax (name := stepTac) &"step" : tactic

elab_rules : tactic
  | `(tactic| step) => do
    let g ← getMainGoal
    g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let (X, inst, b, x, hx, as) ← match ← gfpApp? ty with
      | some (gb, as) =>
        let #[X, inst, b] := gb.getAppArgs | throwError "step: unexpected `gfp` term"
        pure (X, inst, b, gb, ← mkAppOptM ``gfp_chain #[X, inst, b], as)
      | none =>
        let e ← whnfR ty
        let R := e.getAppFn
        unless R.isFVar do throwError "step: the goal is neither `gfp b args` nor `R args`"
        let some (X, inst, b, hx) ← (← getLCtx).findDeclRevM? fun d => do
            if d.isImplementationDetail then return none
            let t ← whnfR (← instantiateMVars d.type)
            unless t.isAppOfArity ``Chain 4 && t.appArg! == R do return none
            let #[X, inst, b, _] := t.getAppArgs | return none
            return some (X, inst, b, d.toExpr)
          | throwError "step: no hypothesis `Chain _ {R}` in context"
        pure (X, inst, b, R, hx, e.getAppArgs)
    let next ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (← mkAppOptM ``Mon.body #[X, inst, b, x]) as) (← g.getTag)
    let pf := mkAppN (← mkAppOptM ``b_chain #[X, inst, b, x, hx]) (as.push next)
    unless ← isDefEq (← inferType pf) ty do throwError "step: could not unfold the goal"
    g.assign pf
    replaceMainGoal [next.mvarId!]

end Tactics

end Coinduction
