import AbelFormalization.AnalyticGermGenerators
import AbelFormalization.AnalyticGermDimensionLower
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Consequences of the remaining analytic Noetherian theorem

The actual coordinate generators and prime chain determine regularity and
dimension once Noetherianity is available. This module does not assert
Noetherianity in arbitrary dimension: it makes that remaining hypothesis
explicit and proves the further algebraic conclusions from it.
-/

noncomputable section

namespace AbelFormalization

/-- The analytic maximal ideal needs at most one generator per coordinate. -/
theorem analyticGerm_maximalIdeal_spanFinrank_le (p : ℕ) :
    (IsLocalRing.maximalIdeal (RealAnalyticGerm p)).spanFinrank ≤ p := by
  rw [analyticGerm_maximalIdeal_eq_span_coordinates]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
  have h := Set.ncard_image_le (f := analyticGermCoordinate p)
    (s := Set.univ) Set.finite_univ
  simpa using h

/-- Given the analytic Noetherian theorem, the coordinate prime chain and
Krull's height theorem determine the dimension exactly. -/
theorem realAnalyticGerm_dimension_of_isNoetherian (p : ℕ)
    [IsNoetherianRing (RealAnalyticGerm p)] :
    ringKrullDim (RealAnalyticGerm p) = p := by
  apply le_antisymm _ (realAnalyticGerm_dimension_lower p)
  apply (ringKrullDim_le_spanFinrank_maximalIdeal (RealAnalyticGerm p)).trans
  exact_mod_cast analyticGerm_maximalIdeal_spanFinrank_le p

/-- Noetherianity is the remaining input for regularity in general dimension;
neither this theorem nor the dimension theorem assumes regularity itself. -/
theorem realAnalyticGerm_regular_of_isNoetherian (p : ℕ)
    [IsNoetherianRing (RealAnalyticGerm p)] : IsRegularLocalRing (RealAnalyticGerm p) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [realAnalyticGerm_dimension_of_isNoetherian]
  exact_mod_cast analyticGerm_maximalIdeal_spanFinrank_le p

end AbelFormalization
