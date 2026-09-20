# Proper regular fiber finiteness: source-only audit

Staged theorem: `finite_fullFiber_of_proper_regular_target` in
`Scratch/LionProperRegularFiberFinite.lean`. No Lean or Lake command has been
run on this module. It is unimported by the maintained project.

The proof uses these exact local mathlib interfaces:

| Interface | Type or purpose |
| --- | --- |
| `IsProperMap.isCompact_preimage` | `(h : IsProperMap f) → IsCompact K → IsCompact (f ⁻¹' K)` |
| `isCompact_singleton` | `IsCompact ({u} : Set Y)` |
| `isDiscrete_iff_forall_mem_exists_isOpen` | `IsDiscrete s ↔ ∀ x ∈ s, ∃ U, IsOpen U ∧ U ∩ s = {x}` |
| `IsCompact.finite` | `IsCompact s → IsDiscrete s → s.Finite` |
| `ContDiffAt.toOpenPartialHomeomorph` | Invertible derivative of a `C¹` map gives an open inverse-function chart. |
| `OpenPartialHomeomorph.injOn` | The chart is injective on its open source. |

The derivative-to-chart construction is copied from the compiled
`LionUpperNumbersCenterControl.exists_open_target_preimages_in_of_contDiff_of_surjective_fderiv`
and `RegularZeroBasics.exists_isOpen_inter_regularZeroSet_eq_singleton`. It
turns surjectivity of the square derivative into a continuous linear
equivalence using
`continuousLinearMap_injective_of_surjective_of_finrank_eq` and
`ContinuousLinearEquiv.ofBijective`.

For each `x ∈ F ⁻¹' {u}`, the maintained definition
`IsRegularTargetValue F u` supplies surjectivity of `fderiv ℝ F x`.
An open injective chart around `x` intersects the fiber only at `x`, proving
discreteness. Properness makes the fiber compact, hence finite. The empty
fiber case is covered automatically.

If this scratch theorem compiles, it discharges the explicit `hfinite`
premise in
`LionProperRegularCompactUpperBound.exists_uniform_preimage_bound_on_compact_regular_targets`
by `fun u hu ↦ finite_fullFiber_of_proper_regular_target hF hproper
  (hregular u hu)`. It also discharges the local theorem's `hfinite` at
any regular center. The resulting bound remains local or compact-target;
it does not establish one uniform bound over all regular targets.

The only plausible elaboration risk is rewriting the chart coercion to `F`
in `exists_open_injective_patch_of_surjective_fderiv`; the maintained
inverse-chart proofs use the same definition and `chart.injOn` pattern.
