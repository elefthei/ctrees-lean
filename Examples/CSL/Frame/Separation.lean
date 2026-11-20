/- SPDX-License-Identifier: MIT -/
module

-- Separation regressions (<- `examples/CSL/Frame/Separation.v`), one file per Rocq module;
-- `Shared` holds the heap-view assertions they share.
public import Examples.CSL.Frame.Separation.Shared
public import Examples.CSL.Frame.Separation.NextRegression
public import Examples.CSL.Frame.Separation.HeapRegression
public import Examples.CSL.Frame.Separation.AlwaysRegression
public import Examples.CSL.Frame.Separation.FiniteRegression
public import Examples.CSL.Frame.Separation.FiniteTiclRegression
public import Examples.CSL.Frame.Separation.AlwaysTiclRegression
public import Examples.CSL.Frame.Separation.SilentReadTiclRegression
