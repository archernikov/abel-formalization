import AbelFormalization.WilkieSection4DeepEndpointAssembly
import AbelFormalization.WilkieDirectTraceExactResidualPipeline

/-!
# Main-theorem endpoint for the retained Section 4 induction
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Pointwise Abel endpoint: a bounded retained simultaneous Section 4
induction, allowed to use the closed-boundary carrier datum, discharges the
last tower premise. -/
theorem IsAbel.oMinimal_of_boundedDeepSection4Induction
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hinduction :
      CharbonnelClosedBoundaryCarrierProperty (abelGeometricFamily A) →
        ∀ n : ℕ,
          CharbonnelBoundedDeepSection4InductionAt
            (literalZeroSetFamily (abelGeometricFamily A)) n) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact hA.oMinimal_of_towers
    (charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_boundedDeepSection4Induction
      hG hsmooth hinduction)

/-- Family-wide endpoint: constructing the bounded retained simultaneous
Section 4 induction for every Abel family proves the literal main theorem. -/
theorem mainTheorem_of_boundedDeepSection4Induction
    (hinduction : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelClosedBoundaryCarrierProperty (abelGeometricFamily A) →
        ∀ n : ℕ,
          CharbonnelBoundedDeepSection4InductionAt
            (literalZeroSetFamily (abelGeometricFamily A)) n) :
    MainTheorem := by
  apply mainTheorem_of_towers
  intro A hA
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_boundedDeepSection4Induction
      hG hsmooth (hinduction A hA)

end AbelFormalization
