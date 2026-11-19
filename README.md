# ctrees-lean

A Lean 4 port of [Choice Trees](https://github.com/vellvm/ctrees) (`theories/`): the coinductive
`CTree E B R` with `ret/stuck/step/guard/vis/br` nodes, its labelled transition system, strong and
weak (bi)simulations built on a Lean port of Damien Pous's coinduction tower, and interpreters
(`foldM`, `interp`, `refine`, state, `mrec`, ITree embedding).

`Coinductive/CoInd.lean` and `ITree/{Effect,Definition,InterpM}.lean` are vendored verbatim from
[coinductive-lean](https://github.com/ISTA-PLV/coinductive) @ `e9b076be`.

Build: `lake build`. No Mathlib. `tests/UniverseCheck` is not portable (`PF` forces one universe).

Use from another Lake package (released on [Reservoir](https://reservoir.lean-lang.org) as
`elefthei/ctrees`):

```toml
[[require]]
name = "ctrees"
scope = "elefthei"
rev = "v0.1.0"
```

The vendored libraries keep their module names (`Coinductive.CoInd`, `ITree.*`), so this package
cannot be required alongside coinductive-lean itself.

## Layout

| Rocq | Lean |
|---|---|
| `Core/{Utils,Index,CTreeDefinitions}.v` | `CTree/Core/{Utils,Index,Definitions}.lean` |
| `coinduction` library (`tower.v`, `rel.v`) | `CTree/Coinduction.lean` |
| `Eq/{Equ,Shallow}.v` | `CTree/Eq/Equ.lean` |
| `Eq/{Trans,SSim,CSSim,SBisim,Visible,Epsilon,SSimAlt,SBisimAlt,WBisim,Trace,IterFacts}.v` | `CTree/Eq/*.lean` (same names) |
| `Misc/{Pure,Head}.v` | `CTree/Misc/{Pure,Head}.lean` |
| `Interp/*.v` | `CTree/Interp/*.lean` (same names) |

## Conventions

- `CTree` is extensional, so Rocq's structural equality `equ eq` (`≅`) is `=`. Equality coinduction
  is `eq_coind`/`eq_coind_upto`.
- `~` is `sbisim Eq` and `≈` is `wbisim`, both scoped to `namespace CTree`. Rocq's `step`
  tactic is `*_unfold.1`/`.2`, and `coinduction` is `Coinduction.coinduction (b := …)`.
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
- **Rocq-only tooling**: Ltac and tactic notations (`step`, `coinduction`, `play`, `inv_trans`,
  `upto_bind`, `break`, …), printing-only notations, and `Arguments`/`Opaque`/`Typeclasses Opaque`
  directives.
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

## License

MIT ([LICENSE](LICENSE)), as is the Rocq original. The vendored files under `Coinductive/` and
`ITree/` keep their Apache-2.0 headers; their license text is in [LICENSE-APACHE](LICENSE-APACHE).
