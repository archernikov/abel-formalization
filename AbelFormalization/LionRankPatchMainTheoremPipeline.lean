import AbelFormalization.LionRankPatchFixedSquareEncoding
import AbelFormalization.CharbonnelSourceComplementPipeline
import AbelFormalization.WilkieBoundedComplementAssembly

/-!
# Main-theorem endpoint from finite rank/minor patches

This module feeds the finite rank/minor fixed-square atlas into the strongest
source-shaped main-theorem pipeline.  The rank/minor atlas and a uniform bound
for regular fibers of fixed square family maps replace the former uniform
fiber-finiteness premise.  On the complement side, the bounded-coordinate
closed-lift cover property replaces the older global cell-cover assembly.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- For one Abel function, finite rank/minor patch encodings turn uniform
fixed-square regular-fiber bounds into the uniform fiber bound consumed by the
source complement pipeline.  Projection is automatic, and only the bounded
closed-lift cell-cover assembly is retained from the cell argument. -/
theorem IsAbel.oMinimal_of_rankMinorPatchEncodings_and_charbonnelSourceSteps
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hregular : HasUniformSquareRegularFiberBound
      (abelGeometricFamily A))
    (hpatch : HasRankMinorPatchFixedSquareEncodingsForFamily
      (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hUFF : HasUniformFiberFiniteness (abelGeometricFamily A) :=
    hasUniformFiberFiniteness_of_rankMinorPatchEncodings
      hsmooth hregular hpatch
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection
    hUFF hselection hanalytic
    (charbonnelClosedBoundaryComplementAssembly_of_boundedCellCovers
      hG hsmooth hUFF hcells)

/-- Family-wide main-theorem endpoint with the uniform-fiber premise split
into its exact finite-patch inputs: a uniform fixed-square regular-fiber bound
and canonical rank/minor patch encodings.  The remaining source hypotheses are
Maxwell meagre selection, the Section 5 analytic step, and bounded closed-lift
cell covers. -/
theorem mainTheorem_of_rankMinorPatchEncodings_and_charbonnelSourceSteps
    (hregular : ∀ (A : ℝ → ℝ), IsAbel A →
      HasUniformSquareRegularFiberBound (abelGeometricFamily A))
    (hpatch : ∀ (A : ℝ → ℝ), IsAbel A →
      HasRankMinorPatchFixedSquareEncodingsForFamily
        (abelGeometricFamily A))
    (hselection : ∀ (A : ℝ → ℝ), IsAbel A →
      HasMaxwellMeagreClosureComponentSelection
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSection5AnalyticStep
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedClosedBoundaryCellCoverAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_rankMinorPatchEncodings_and_charbonnelSourceSteps
    (hregular A hA) (hpatch A hA) (hselection A hA)
      (hanalytic A hA) (hcells A hA)

/-- Gabrielov upper numbers discharge the fixed-square regular-fiber premise
in the finite rank/minor patch main-theorem endpoint.  Thus the exact Lion
input left here is the construction of the canonical patch encoders. -/
theorem
    mainTheorem_of_gabrielovUpperNumbers_rankMinorPatchEncodings_and_charbonnelSourceSteps
    (hupper : ∀ (A : ℝ → ℝ), IsAbel A →
      ∀ n (F : RealEuclidean n → RealEuclidean n),
        FunctionTupleInFamily (abelGeometricFamily A) F →
          HasGabrielovUniformUpperNumberProperty F)
    (hpatch : ∀ (A : ℝ → ℝ), IsAbel A →
      HasRankMinorPatchFixedSquareEncodingsForFamily
        (abelGeometricFamily A))
    (hselection : ∀ (A : ℝ → ℝ), IsAbel A →
      HasMaxwellMeagreClosureComponentSelection
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSection5AnalyticStep
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedClosedBoundaryCellCoverAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  apply mainTheorem_of_rankMinorPatchEncodings_and_charbonnelSourceSteps
  · intro A hA
    obtain ⟨_hG, hsmooth, _hderiv⟩ :=
      hA.geometric_smooth_derivativeClosed_abelGeometricFamily
    exact hasUniformSquareRegularFiberBound_of_gabrielovUpperNumbers
      hsmooth (hupper A hA)
  · exact hpatch
  · exact hselection
  · exact hanalytic
  · exact hcells

end AbelFormalization
