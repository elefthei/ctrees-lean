# ctrees-lean

Choice trees and the TICL temporal logic in Lean 4, ported from three Rocq developments:

- [damien-pous/coinduction](https://github.com/damien-pous/coinduction): the companion and
  coinduction tower of Pous, "Coinduction All the Way Up" (LICS 2016), with its `coinduction` and
  `step` tactics, in `Coinductive/Tower.lean`. Every simulation and bisimulation below is a greatest
  fixpoint proved with it, up to enhancements.
- [vellvm/ctrees](https://github.com/vellvm/ctrees): choice trees (Chappe et al., POPL 2023), a
  coinductive model of nondeterministic, recursive and impure programs, in `CTree/`.
- [vellvm/ticl](https://github.com/vellvm/ticl) (branch `lang/yield`): TICL, a temporal logic over
  ctrees with structural proof rules, together with cooperative schedulers, a separation layer and
  the CoCSL language, in `Logic/`, `Lang/` and `Examples/`.

The coinductive types come from [coinductive-lean](https://github.com/ISTA-PLV/coinductive),
vendored as `Coinductive/CoInd.lean` and `ITree/`. There is no Mathlib dependency, and `lake build`
checks everything. [PORTING.md](PORTING.md) maps Rocq files to Lean files and lists what was not
ported.

## Install

The package is released on [Reservoir](https://reservoir.lean-lang.org) as `elefthei/ctrees`:

```toml
[[require]]
name = "ctrees"
scope = "elefthei"
rev = "v0.1.1"
```

The vendored libraries keep their module names (`Coinductive.CoInd`, `ITree.*`), so this package
cannot be required alongside coinductive-lean itself.

## Equivalences

A `CTree E B X` returns values in `X`, performs events from `E`, and branches on choices from `B`.
A `br` node is a hidden choice; a `brS` node is a visible one that takes a step.

You can prove strong bisimulation `t ~ u` (`sbisim`), weak bisimulation `t ≈ u` (`wbisim`), strong
and complete simulations (`ssim`, `cssim`), and trace equivalence. The heterogeneous versions relate
trees with different events and return types through a label relation. `~` is a congruence for
`>>=` (`sbisim_clo_bind`), for `iter` (`sbisim_iter`) and for interpretation with simple handlers
(`interp_sbisim_eq`). Refining choices into pure trees gives a tree that the original simulates
(`refine_ctree_ssim`).

Nondeterministic choice satisfies the expected laws up to `~`:

```lean
import CTree
open CTree

variable {E : ITree.Effect.{0}} {X : Type} (t u v : CTree E B2 X)

-- Hidden choice is associative, commutative and idempotent.
example : CTree.br2 (.br2 t u) v ~ .br2 t (.br2 u v) := br2_assoc t u v
example : CTree.br2 t u ~ .br2 u t := br2_commut t u
example : CTree.br2 t t ~ t := br2_idem t
-- Visible choice commutes, but merging two equal branches leaves a visible step,
example : CTree.brS2 t t ~ .step t := brS2_idem t
-- which weak bisimulation ignores.
example : CTree.step t ≈ t := step_wb t
```

Simulation in both directions does not imply bisimulation (`ssim_sbisim_nequiv`).

## Liveness

`entails φ t w` says that the ctree `t` in world `w` satisfies the TICL formula `φ`. Formulas
include `AX`/`EX`, `AF`/`EF`, `AG`/`EG`, `AU`/`EU`, and `ret` postconditions on returned values.
Proofs are structural. Each ctree node has its own rule (`au_ret`, `au_br`, `au_brS`, `au_vis`, …),
sequencing has bind rules (`u_bind_r`, `ag_bind_r`), loops have variant and invariant rules
(`u_iter_nat`, `ag_iter`, `eg_iter`), and every formula is invariant under `~`
(`proper_entails_meq`).

A loop that subtracts 1 or 2 at each round, chosen nondeterministically, terminates on every path.
The variant `n` decreases in both branches:

```lean
import Logic
open CTree Tisl Tisl.Notation

def countdown (n : Nat) : CTree void1 B2 (Nat ⊕ PUnit) :=
  if n = 0 then pure (.inr ⟨⟩) else .brS2 (pure (.inl (n - 1))) (pure (.inl (n - 2)))

theorem countdown_af (n : Nat) :
    entails (AF ret= PUnit.unit .pure) (CTree.iter countdown n) (.pure : World void1) := by
  refine u_iter_nat (fun _ w => w = .pure) (fun n _ => n) rfl fun s w hw => ?_
  subst hw; unfold countdown; split
  · exact au_ret.1 (.inl (ret_ret .pure (ret_ret .pure ⟨rfl, rfl⟩)))
  · refine (au_brS (ULift.up true)).1 (.inr ⟨⟨trivial, .pure⟩, fun ⟨b⟩ => ?_⟩)
    cases b <;> exact au_ret.1 (.inl (ret_ret .pure ⟨rfl, by omega⟩))
```

The same rules scale to concurrent programs. Under any fair scheduler, a cooperative thread pool
satisfies `AG (AF …)` of its observations, given a ranking certificate (`agaf_pool_fair`). Round
robin is fair and nondeterministic selection is not. CoCSL adds frame and separation rules on top.
`Examples/CSL/Allocator/Liveness.lean` proves that allocation, retirement and reclamation in a
CAS-based allocator each recur under every fair scheduler (`allocator_agaf_fair`).
`lake env lean Examples/CSL/Evidence.lean` prints the axioms of 238 headline results.

## License

MIT ([LICENSE](LICENSE)), as is the Rocq original. The vendored files `Coinductive/CoInd.lean` and
`ITree/` keep their Apache-2.0 headers; their license text is in [LICENSE-APACHE](LICENSE-APACHE).
