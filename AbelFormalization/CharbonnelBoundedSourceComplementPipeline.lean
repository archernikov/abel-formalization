import AbelFormalization.CharbonnelSourceComplementPipeline
import AbelFormalization.WilkieBoundedComplementAssembly

/-!
# Source complement pipeline through Wilkie's bounded coordinates

This module replaces the older global closed-lift cell-cover premise by the
smaller relative decomposition requested after transporting the visible
projection to the open cube.  The semialgebraic bounded-coordinate map,
relative finite-union argument, and pullback to the original coordinates are
all proved in the imported assembly module.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The source steps produce the projected-zero complement envelope from
cube-relative compatible covers of bounded projected closed lifts. -/
noncomputable def
    projectedZeroComplementEnvelope_of_charbonnelSourceSteps_and_boundedCellCovers
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly G) :
    ProjectedZeroComplementEnvelope G :=
  projectedZeroComplementEnvelope_of_charbonnelSourceSteps
    hG hsmooth hUFF hselection hanalytic hprojection
      (charbonnelClosedBoundaryComplementAssembly_of_boundedCellCovers
        hG hsmooth hUFF hcells)

/-- Pointwise Abel o-minimality from the three analytic source inputs and the
cube-relative bounded cell-cover assembly; the projection step is internal. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
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
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection
    hUFF hselection hanalytic
      (charbonnelClosedBoundaryComplementAssembly_of_boundedCellCovers
        hG hsmooth hUFF hcells)

/-- All four conclusions of the proposed theorem for one Abel function, with
the cell input stated exactly in Wilkie's bounded relative form. -/
theorem IsAbel.mainTheoremConclusion_of_charbonnelSourceSteps_and_boundedCellCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A ∧ ExponentialDefinable A ∧
      PositiveInverseDefinable A (inverse A) ∧
        IsTransexponential (inverse A) :=
  ⟨hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
      hUFF hselection hanalytic hcells,
    hA.exponentialDefinable, hA.positiveInverseDefinable,
    hA.isTransexponential⟩

/-- Family-wide source endpoint with the Section 4 obligation reduced to
cube-relative compatible covers of bounded projected closed lifts. -/
theorem
    mainTheorem_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
    (hUFF : ∀ (A : ℝ → ℝ), IsAbel A →
      HasUniformFiberFiniteness (abelGeometricFamily A))
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
  exact hA.mainTheoremConclusion_of_charbonnelSourceSteps_and_boundedCellCovers
    (hUFF A hA) (hselection A hA) (hanalytic A hA) (hcells A hA)

end AbelFormalization
