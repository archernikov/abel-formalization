import AbelFormalization.CharbonnelPositiveZeroTraceCategory
import AbelFormalization.CharbonnelSardianProjectionMorseSardReduction
import AbelFormalization.CharbonnelSourceStageIntegerAffineTrace

/-!
# The Sardian projection constructor from the direct Charbonnel theorems

The category proofs of Charbonnel Theorems 2.1 and 2.2, together with the
proved smooth rectangular Morse--Sard theorem, discharge Wilkie's Sardian
projection constructor for every Abel family with uniform fibre finiteness.
The numeric description-rank induction then has no remaining analytic
premise.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Direct Abel endpoint for the positive-hidden-arity Sardian projection
constructor. -/
theorem IsAbel.charbonnelSardianProjectionConstructorInput_of_category
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily A) := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact hA.charbonnelSardianProjectionConstructorInput_of_smoothCriticalValues
    hUFF
    (literalZeroSet_charbonnelClosure_theorem21 hG hsmooth hUFF)
    (literalZeroSet_charbonnelClosure_theorem22 hG hsmooth hUFF)

/-- Hence the full numeric Sardian approximation rank step is automatic for
an Abel family with uniform fibre finiteness. -/
theorem IsAbel.charbonnelSardianApproximationRankStep_of_category
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    CharbonnelSardianApproximationRankStep (abelGeometricFamily A) := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact charbonnelSardianApproximationRankStep_of_projection hG hsmooth
    (hA.charbonnelSardianProjectionConstructorInput_of_category hUFF)

/-- The closed empty-interior boundary carrier property consumed by
Wilkie's Section 4 cell argument is therefore automatic as well. -/
theorem IsAbel.charbonnelClosedBoundaryCarrierProperty_of_category
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    CharbonnelClosedBoundaryCarrierProperty (abelGeometricFamily A) := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty
    hG
    (literalZeroSet_charbonnelClosure_approximationTraceTameness
      hG hsmooth hUFF)
    (hA.charbonnelSardianApproximationRankStep_of_category hUFF)

end AbelFormalization
