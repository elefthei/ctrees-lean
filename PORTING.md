# Porting notes

How the Rocq sources map to Lean, the conventions that changed, and what was left out. The first
part covers [vellvm/ctrees](https://github.com/vellvm/ctrees) (`theories/`), the second
[vellvm/ticl](https://github.com/vellvm/ticl) (see [TISL](#tisl)).

`Coinductive/CoInd.lean` and `ITree/{Effect,Definition,InterpM}.lean` are vendored verbatim from
[coinductive-lean](https://github.com/ISTA-PLV/coinductive) @ `e9b076be`. The ctrees test
`tests/UniverseCheck` is not portable (`PF` forces one universe).

## Layout

| Rocq | Lean |
|---|---|
| `Core/{Utils,Index,CTreeDefinitions}.v` | `CTree/Core/{Utils,Index,Definitions}.lean` |
| `coinduction` library (`tower.v`, `rel.v`) | `Coinductive/Tower.lean` (namespace `Coinduction`) |
| `Eq/{Equ,Shallow}.v` | `CTree/Eq/Equ.lean` |
| `Eq/{Trans,SSim,CSSim,SBisim,Visible,Epsilon,SSimAlt,SBisimAlt,WBisim,Trace,IterFacts}.v` | `CTree/Eq/*.lean` (same names) |
| `Misc/{Pure,Head}.v` | `CTree/Misc/{Pure,Head}.lean` |
| `Interp/*.v` | `CTree/Interp/*.lean` (same names) |

## Conventions

- `CTree` is extensional, so Rocq's structural equality `equ eq` (`≅`) is `=`. Equality coinduction
  is `eq_coind`/`eq_coind_upto`.
- `~` is `sbisim Eq` and `≈` is `wbisim`, both scoped to `namespace CTree`. Pous's `coinduction R H`
  and `step` tactics are `coinduction R hR CIH` and `step`; the goal of `coinduction` must quantify
  over every argument and hypothesis of the coinductive statement (`∀ t u, P t u → t ~ u`).
- Effects are `ITree.Effect` (`I`, `O`), and handlers `E ~> M` are `(e : E.I) → M (E.O e)`. Rocq's
  `-<` is `Subeffect`. Lemmas that need every branch of an injected `br'` to be reachable also take
  `[LawfulSubeffect B₁ B]`; Rocq gets this for free.
- Rocq `_id` rules over a shared answer type take `hO : F.O f = E.O e` plus `cast`.
- Lean's `StateT` returns `(value, state)` and Rocq's `stateT` returns `(state, value)`. The
  `Interp/FoldStateT` and `Interp/Refine` statements are flipped to match.
- Renamed declarations:
  - Predicates use Lean case: `isStuck`, `isPure`, `PureFinite`, `isSimple`, `Productive`,
    `Epsilon`, `EpsilonDet`, `wfVal`, `updateValRel`, `HAction`, `runHAction`, `converseNeg`.
  - Rocq `fold` is `foldM`, because `CTree.fold` is the coinductive constructor. `trans_ABr` is
    `trans_AStep`.
  - Generic names that clash take a relation prefix: `bind_chain_gen` becomes `sb_`/`ss'_`/`sb'_`/
    `wb_chain_bind_gen`; `spinS_gen_nonempty` becomes `ssim_`/`cssim_`/`sbisim_spinS_gen_nonempty`;
    RecursionFacts' `interp_trigger` becomes `interp_trigger_sbisim`.
- Rocq typeclass instances that only package lemmas (`Equivalence_*`, `PreOrder_*`, `Transitive_*`,
  `Reflexive_*`, `Proper` instances over `eq`) are theorems.

## Not ported

- **Everything about `equ`**: the `Proper (equ …)`, `weq` and `Lequiv` instances, the
  up-to-`equ` closures (`equ_clos*`), and `*_equ` lemmas. All are trivial for `=`.
- **Rocq-only tooling**: Ltac and tactic notations (`play`, `inv_trans`, `upto_bind`, `break`, …),
  printing-only notations, and `Arguments`/`Opaque`/`Typeclasses Opaque` directives.
- **Chain-specialised duplicates of `_gen` rules** (`step_ss_*`, `step_css_*`, `step_sb_*` without
  `_gen`, `sbisim_ssim_subrelation`, …). Dropping the `Proper` hypotheses makes the `_gen`
  versions apply directly.
- **By file**:
  - `Core/Utils.v`: the `Injective`/`Deterministic` classes, which only Ltac uses.
  - `Core/CTreeDefinitions.v`: `subst`, `cat`, `map` (use `>>=`, `>=>`, `<$>`). `Vis_eq1/2` and
    `Br_eq1/2` are `vis_eq_vis_iff'` and `br_eq_br_iff'`.
  - `Eq/Equ.v`, `Eq/Shallow.v`: `equ`, `observing`, `going` and their theory.
  - `Eq/Trans.v`: the `Coproduct` section (`srtrans`/`sltrans`/`ltrans`/`rtrans`). It is unused
    upstream, and `srtrans_`/`sltrans_` have no base constructor, so they are empty relations.
  - `Eq/SBisim.v`: the `sbisim_clos` monotone function (the closure lemmas take its hypotheses
    directly) and `bind_sbisim_cong(_gen)` (covered by `sbisim_clo_bind(_eq)`).
  - `Eq/SBisimAlt.v`: `lift_rel3`, which only the `equ` closure uses.
  - `Eq/WBisim.v`:
    - `wbisimT`: RelationAlgebra packaging.
    - `cnv_gfp`, `cnv_wbisim`: covered by `cnv_wt` and `wbisim_symm`.
    - `wbisim_trans_back'`, `wbisim_wtrans_front_`: duplicates.
    - `wb_step_inv`: `Abort`ed upstream.
    - `spinS_nary_0`, `brS2_not_assoc`: commented out upstream.
  - `Misc/Head.v`: `eq_haction`, `head_equ`.
  - `Interp/Recursion.v`, `Interp/RecursionFacts.v`:
    - `Proper_interp_mrec`, `rec_as_interp`: `Admitted` upstream.
    - `mrec_fix`, `rec_fix`, `unfold_interp_mrec_h`, `euttge_interp_mrec(')`: commented out
      upstream.
  - `Interp/ITree.v`: `embed_eq`, `eq_itree_productive`. Lean's `ITree` equality is `=`. The
    vendored ITree has no `eutt`, so `Interp/ITree.lean` defines it locally with the tower
    (`EuttF`, `eutt`) to state and prove `embed_eutt`.

## TISL

Three more libraries port [vellvm/ticl](https://github.com/vellvm/ticl) (branch `lang/yield` @
`3235488`; `theories/` minus the old languages, and `examples/`):

- `Logic` (namespace `Tisl`; `Tisl.Yield` for schedulers, `Tisl.CSL`/`Tisl.Pcm`/`Tisl.Heap` for
  separation): the logic, its ctree model and structural rules, interpreters, the cooperative
  Yield/Fork scheduler stack, the CSL handler, the owned two-lineage machine and active separation.
- `Lang` (namespace `CoCSL`): the cooperative separation-logic language CoCSL.
- `Examples` (namespace `Examples.<path>`): every example under `examples/CSL/` plus `Tick`,
  `HiddenBr`, `IndexedSyntax` and `Scheduling`.

`Examples/CSL/Evidence.lean` is the port of `Evidence.v`: `#check` and `#print axioms` for each of
its 238 roots. Every root depends only on `propext`, `Classical.choice` and `Quot.sound`:
`lake env lean Examples/CSL/Evidence.lean`.

### Layout

Paths are under `theories/` unless they start with `examples/`.

| Rocq | Lean |
|---|---|
| `Utils/{Utils,Relations,Lists,Maps,Vectors,Execution}.v` | `Logic/Utils/*.lean` (same names) |
| `Events/XE.v` + `CTree/Events/X.v` (Writer, Heap, Yield) | `Logic/Events/{Writer,Heap,Yield}.lean` |
| `Logic/{World,Kripke,Syntax,Semantics,Setoid,Congruence,Simulation}.v` | `Logic/*.lean` (same names) |
| `Utils/Pcm.v`, `Events/HeapModel.v` | `Logic/Sep/{Pcm,HeapModel}.lean` |
| `CTree/{Core,Events/State}.v`, `CTree/Trace.v` | `Logic/CTree/{Core,Trace}.lean` |
| `CTree/Logic/*.v` | `Logic/CTree/*.lean` (same names; `Trace.v` is `TraceRules.lean`) |
| `CTree/Interp/{State/Mod,Heap,Refine}.v` | `Logic/Interp/{State,Heap,Refine}.lean` |
| `CTree/Interp/Yield/*.v` | `Logic/Yield/*.lean` (same names) |
| `CTree/Interp/Yield/Mod.v` | `Logic/Yield/{Scheduler,Mod}.lean` |
| `CTree/Interp/Yield/SBisim.v` | `Logic/Yield/{SBisim,SBisimSchedule,SBisimAlign}.lean` |
| `CTree/Interp/CSL/{Mod,Frame}.v` | `Logic/Sep/{CSL,Frame}.lean` |
| `CTree/Interp/CSL/Owned.v` | `Logic/Sep/{Owned,OwnedProject,OwnedInterp}.lean` |
| `CTree/Interp/CSL/Asep.v` | `Logic/Sep/{AsepCore,Asep}.lean` |
| `Lang/CoCSL/Mod.v` | `Lang/CoCSL/{Syntax,Runners,RunnersFair,Early,Loops,KernelsNd,KernelsFair,Surface,Pools}.lean`, re-exported by `Lang/CoCSL/Mod.lean` |
| `Lang/CoCSL/{Sequential,Frame,Owned}.v` | `Lang/CoCSL/*.lean` (same names) |
| `Lang/CoCSL/Asep.v` | `Lang/CoCSL/{AsepModal,AsepSplit,Asep}.lean` |
| `examples/{Tick,HiddenBr,IndexedSyntax,Scheduling}.v` | `Examples/*.lean` (same names) |
| `examples/CSL/**/*.v` | `Examples/CSL/**/*.lean` (same names) |
| `examples/CSL/Allocator/Liveness.v` | `Examples/CSL/Allocator/{LivenessRanks,Liveness}.lean` |
| `examples/CSL/Frame/{Separation,Active}.v` | one file per Rocq `Module` under `Examples/CSL/Frame/{Separation,Active}/` |
| `examples/CSL/Frame/HeapObservations.v` | `Examples/CSL/Frame/HeapObservations/{Loops,Framed,Allocator}.lean` |

Rocq files that were too long for one Lean file are split by line range. Each piece imports the
previous one or is re-exported by a facade named after the Rocq file, and the pieces keep the Rocq
namespace, so Rocq paths such as `examples.CSL.Allocator.Liveness.allocator_agaf_fair` are unchanged.

### Conventions

These extend the ctrees conventions above.

- State pairs follow Lean's `StateT`: Rocq `(σ, x)` is `(x, σ)`, and formulas over `Σ * X` are over
  `X × Σ`.
- Formulas are `Ticl E i` with `i : Option (Type u)` (`TiclL E` for prefix formulas, `TiclR E X` for
  postconditions), and `entails φ t w` is defined for every index. Notations are scoped in
  `Tisl.Notation`: `AX`, `AF`, `AG`, `AN`, `AU`, their `E` duals, `∧ₜ`, `∨ₜ`, `visWₜ`.
- The until modalities are the inductives `Auc`/`Euc`, inlined because Lean rejects the nested
  occurrence through `anc`; `auc_unfold` recovers the Rocq shape. `agc`/`egc` are `gfp`s.
- `Proper (sbisim eq ==> …)` hypotheses are `SbProper P`; `Proper` instances over `=` are dropped.
- `grind` works up to `~`: `Logic/CTree/SBisimGrind.lean` (Lean-only) rewrites `t ~ u` to the
  quotient equality `sbq t = sbq u`. The scheduler, thread and `sh` handler step laws carry
  `@[grind]` attributes, so the focused runner equations of `Logic/Sep/CSL.lean` and
  `Lang/CoCSL/Runners{,Fair}.lean` are `by grind`. `grind` cannot rewrite under binders: a
  continuation that must reduce inside `fun _ => …` still needs `simp`.
- Vectors are core `Vector` (`v[i]`, `v.set i x`, `Vector.cons`); `Fin.F1`/`Fin.FS i` are `0`/`i.succ`.
- `CoFixpoint`s producing ctrees (`schedule_policy`, `refine_rr`, example workers) are
  `partial_fixpoint`s.
- Prop-valued inductives are UpperCamel (`NotDone`, `ReclaimCredit`); theorem names are verbatim.
- Rocq `Let`s and section helpers that public statements mention are public `def`s.

### Not ported

- The older languages `Lang/{StImp,MeQ,MeS,HeapImp}.v` and their examples `Toy`, `Sec`, `Queue`,
  `Election` (and the `StoreExtension`/`HeapExtension` modules of `IndexedSyntax.v`).
- The 688-name ND×RR modality matrix of `Lang/CoCSL/Mod.v`: it is ported as two kernels polymorphic
  in the quantifier (ND runner and policy-generic runner, `KernelsNd`/`KernelsFair`), plus named
  ND/RR corollaries only for the 45 names other files use. Each kernel file's closing comment lists
  the names it covers.
- Ltac, tactic notations, hints and `vm_compute`; proofs use `decide`/`rfl`/`simp` and local
  macros instead. Per-file omissions are in a `-- Not ported:` comment at the end of each file.
