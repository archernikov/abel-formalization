import AbelFormalization.MaxwellMeagreClosureSelection
import AbelFormalization.CharbonnelSection56InfiniteFiberLocalClosedness
import AbelFormalization.CharbonnelSection57InfiniteFiberBridge
import AbelFormalization.WilkieProjectionCoherentCellCoverTower
import AbelFormalization.LionUniformFiberFinitenessTheorem

/-!
# Main theorem from the source-faithful Lion residual

Lion's theorem supplies uniform finiteness of fibers directly from
zero-regularity of the geometric family.  This file connects that conclusion
to the already formalized Charbonnel--Wilkie pipeline without passing through
the invalid canonical Lagrange-cover route.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Lion's uniform fiber theorem makes Maxwell selection automatic.  Given the
stable closure-fiber bound, the only other complement input is the bounded
projection-coherent Section 4 tower. -/
theorem IsAbel.oMinimal_of_stableGraphs_and_projectionTowers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hstable : CharbonnelSection57StableClosureFiberBoundReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hUFF : HasUniformFiberFiniteness (abelGeometricFamily A) :=
    hA.hasUniformFiberFiniteness
  have hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_hasMaxwellMeagreClosureComponentSelection
      hG hsmooth hUFF
  have hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    charbonnelSection57BoundedGraphReduction_of_stableClosureFiberBoundReduction
      hstable
  have hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_section5AnalyticStep_of_maxwellMeagreSelection_and_graphReduction
      hG hsmooth hUFF hselection hbounded
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedProjectionCoherentTowers
      hUFF hselection hanalytic htowers

/-- Source-shaped pointwise endpoint.  Lion supplies uniform fiber finiteness,
and the infinite-fiber bridge derives the Section 5.7 fiber bound from open
localization. -/
theorem IsAbel.oMinimal_of_openLocalization_and_projectionTowers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hlocalize : CharbonnelSection57StableClosureOpenLocalization
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hUFF : HasUniformFiberFiniteness (abelGeometricFamily A) :=
    hA.hasUniformFiberFiniteness
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hstable : CharbonnelSection57StableClosureFiberBoundReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    charbonnelSection57StableClosureFiberBoundReduction_of_openLocalization
      hC (charbonnelClosure_closureInteriorRegularity hC) hlocalize
  exact
    hA.oMinimal_of_stableGraphs_and_projectionTowers hstable htowers

/-- Family-wide conditional endpoint with exactly the two remaining complement
inputs after Lion's theorem: Section 5.7 open localization and the bounded
projection-coherent Section 4 tower. -/
theorem mainTheorem_of_openLocalization_and_projectionTowers
    (hlocalize : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSection57StableClosureOpenLocalization
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_openLocalization_and_projectionTowers
    (hlocalize A hA) (htowers A hA)

end AbelFormalization
