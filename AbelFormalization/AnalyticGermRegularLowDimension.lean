import AbelFormalization.AnalyticGermOneVariable
import AbelFormalization.AnalyticGermDimensionZero
import AbelFormalization.AnalyticGermComposition
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Regularity in zero and one analytic variable

The convergent analytic arguments and the scalar/tuple germ equivalence
establish the full regular Noetherian local-ring assertions in dimensions
zero and one. The corresponding assertions in higher dimensions are not
assumed by these results.
-/

noncomputable section

namespace AbelFormalization

/-- The zero-variable analytic local ring is regular. -/
instance realAnalyticGermZeroIsRegularLocalRing : IsRegularLocalRing (RealAnalyticGerm 0) :=
  IsRegularLocalRing.of_ringEquiv realAnalyticGermZeroEquivReal.symm

/-- The one-variable result applies to the exact finite-tuple convention used
in the manuscript. -/
instance realAnalyticGermOneIsDiscreteValuationRing :
    IsDiscreteValuationRing (RealAnalyticGerm 1) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing analyticGermOneEquiv

theorem realAnalyticGerm_one_isNoetherian : IsNoetherianRing (RealAnalyticGerm 1) :=
  inferInstance

theorem realAnalyticGerm_one_isRegularLocalRing : IsRegularLocalRing (RealAnalyticGerm 1) :=
  inferInstance

theorem realAnalyticGerm_one_ringKrullDim : ringKrullDim (RealAnalyticGerm 1) = 1 := by
  rw [← analyticGermOneEquiv.toRingEquiv.ringKrullDim]
  exact analyticGerm_one_variable_ringKrullDim 0

end AbelFormalization
