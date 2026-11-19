# ctrees-lean

A Lean 4 port of [Choice Trees](https://github.com/vellvm/ctrees) (`theories/`): the coinductive
`CTree E B R` with `ret/stuck/step/guard/vis/br` nodes, its labelled transition system, strong and
weak (bi)simulations built on a Lean port of Damien Pous's coinduction tower, and interpreters
(`fold`, `interp`, `refine`, state, `mrec`, ITree embedding).

`Coinductive/CoInd.lean` and `ITree/{Effect,Definition,InterpM}.lean` are vendored verbatim from
[coinductive-lean](https://github.com/ISTA-PLV/coinductive) @ `e9b076be`.

Build: `lake build`. No Mathlib. `tests/UniverseCheck` is not portable (`PF` forces one universe).

## Not ported
