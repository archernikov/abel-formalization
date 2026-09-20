# Source-only audit: proper regular fibers on compact target sets

The companion unimported draft is `Scratch/LionProperRegularCompactUpperBound.lean`. No Lean, Lake, or umbrella build was run for it. Its three public statements are:

1. `exists_open_fullFiber_bound_of_proper_regular_center`: for a proper `C¹` square Euclidean map and a regular center with finite full fiber, one open neighborhood of that center has **all** full fibers bounded by one natural number.
2. `hasUpperNumberOfPreimagesAt_of_proper_regular_center`: the previous result implies the project's `HasUpperNumberOfPreimagesAt` at that regular center.
3. `exists_uniform_preimage_bound_on_compact_regular_targets`: if `K` is compact, consists of regular target values, and its fibers are pointwise finite, one number bounds all full fibers over `K`.

The proof deliberately retains `hfinite : (F ⁻¹' {u}).Finite`. It can subsequently be discharged from `hproper.isCompact_preimage isCompact_singleton`, local inverse-function charts, and `IsCompact.finite` applied to the discrete regular fiber. Keeping it explicit minimizes the present source-only elaboration burden and shows where finite fibers enter.

The local bound uses these exact existing APIs:

- `ContDiffAt.toOpenPartialHomeomorph` and `ContDiffAt.mem_toOpenPartialHomeomorph_source` from `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`; the maintained `LionUpperNumbersCenterControl` already constructs these charts for nondegenerate square-map preimages.
- `OpenPartialHomeomorph.open_source` and `OpenPartialHomeomorph.injOn` from `Mathlib.Topology.OpenPartialHomeomorph.Defs`.
- `IsProperMap.isClosedMap` from `Mathlib.Topology.Maps.Proper.Basic`: the image of the closed complement of the finite union of charts is closed. Its complement is the target neighborhood on which every preimage belongs to one chart.
- `ENat.card_le_card_of_injective` and `ENat.card_eq_coe_natCard` to bound the nearby fiber by the finite chart-index type.
- `IsCompact.elim_finite_subcover` from `Mathlib.Topology.Compactness.Compact` and `Finset.le_sup` to combine the local bounds over `K`.

Expected compiler repair sites in the uncompiled draft are the dependent `choose` declarations, the definitional identification of the inverse-function chart with `F` in its `injOn` proof, and membership coercions between `F ⁻¹' {u}` and its underlying Euclidean space. They are elaboration risks, not mathematical assumptions.

This result does **not** establish `HasGabrielovUniformUpperNumberProperty F`. The maintained `hasGabrielovUniformUpperNumberProperty_iff` identifies that missing assertion with a single bound on full fibers over **every regular target value**. A compact regular subset does not include target values approaching singular centers or escaping to infinity. There is also no current project theorem making every square family tuple proper. The Lion interface in `LionUniformFiberNarrowing` still needs Gabrielov uniform upper numbers and a rank-varying rectangular encoding.

The source distinction is real. [Ambroży's statement of Lion's Theorem 1.5](https://www.impan.pl/shop/en/publication/transaction/download/product/85569) takes geometric regularity and `0`-regularity as hypotheses and gives UFF; it does not derive that quantifier change from ordinary proper-map topology. [Khovanskii's analytic finiteness paper](https://www.math.utoronto.ca/askold/1984-Faa-2-english.pdf) states parameter-uniform bounds for analytic families on cubes and, later, for proper Pfaffian maps, using analytic/Pfaffian finiteness machinery absent from local mathlib. [Fornasiero and Servi's complement theorem](https://arxiv.org/pdf/0803.3560) assumes uniform connected-component bounds before deriving o-minimality, so it does not discharge the Lion upper-number step either.

Even `proper C∞ + finite regular fibers at each target` is insufficient near a singular center. On the positive half-line, the flat oscillatory germ `exp (-1 / x²) * (2 + sin (1 / x⁴))` tends to zero, has finitely many points over each fixed nonzero level near zero, and admits levels with arbitrarily many transverse preimages as the level tends to zero. This observation is only a mathematical obstruction audit; no global interpolation of that germ or Lean counterexample is asserted in the draft.
