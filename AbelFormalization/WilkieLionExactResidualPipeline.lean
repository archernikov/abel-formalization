import AbelFormalization.LionRankPatchCanonicalLagrangeReduction
import AbelFormalization.MaxwellMeagreClosureSelection
import AbelFormalization.CharbonnelSection56InfiniteFiberLocalClosedness
import AbelFormalization.CharbonnelSection57InfiniteFiberBridge
import AbelFormalization.WilkieProjectionCoherentCellCoverTower

/-!
# Main theorem from the current exact source residuals

This module composes the strongest Lion and Wilkie reductions currently
available.  In particular, Charbonnel 5.4--5.6 is no longer an independent
input: Maxwell closure-interior regularity supplies the closed exceptional
base obtained from the closure of the infinite-fibre locus.  Section 5.7 is
represented by its stable closure-fibre cardinality witness, and Section 4 by
an actual projection-coherent enriched cell-cover tower.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Pointwise Abel endpoint exposing the current independent residuals.

The Lion side consists of Gabrielov uniform upper numbers and finite regular
Lagrange covers of the canonical rank/minor fibres.  On the complement side,
Maxwell meagre selection is now automatic from the weak structure, so only
the stable graph witness and projection-coherent enriched towers remain as
the separate Section 5.7 and Section 4 inputs. -/
theorem IsAbel.oMinimal_of_canonicalLagrange_stableGraphs_and_projectionTowers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hupper : ∀ n (F : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily (abelGeometricFamily A) F →
        HasGabrielovUniformUpperNumberProperty F)
    (hcovers : HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
      (abelGeometricFamily A))
    (hstable : CharbonnelSection57StableClosureFiberBoundReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hregular : HasUniformSquareRegularFiberBound
      (abelGeometricFamily A) :=
    hasUniformSquareRegularFiberBound_of_gabrielovUpperNumbers
      hsmooth hupper
  have hUFF : HasUniformFiberFiniteness (abelGeometricFamily A) :=
    hA.hasUniformFiberFiniteness_of_canonicalFiniteLagrangeCovers
      hregular hcovers
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

/-- Stronger pointwise endpoint using the infinite-fibre bridge.  The fibre
cardinality bound in the preceding theorem is now derived from compactness
and localization of stable intervals away from the closed infinite-fibre
locus. -/
theorem IsAbel.oMinimal_of_canonicalLagrange_openLocalization_and_projectionTowers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hupper : ∀ n (F : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily (abelGeometricFamily A) F →
        HasGabrielovUniformUpperNumberProperty F)
    (hcovers : HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
      (abelGeometricFamily A))
    (hlocalize : CharbonnelSection57StableClosureOpenLocalization
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hregular : HasUniformSquareRegularFiberBound
      (abelGeometricFamily A) :=
    hasUniformSquareRegularFiberBound_of_gabrielovUpperNumbers
      hsmooth hupper
  have hUFF : HasUniformFiberFiniteness (abelGeometricFamily A) :=
    hA.hasUniformFiberFiniteness_of_canonicalFiniteLagrangeCovers
      hregular hcovers
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
  exact hA.oMinimal_of_canonicalLagrange_stableGraphs_and_projectionTowers
    hupper hcovers hstable htowers

/-- Family-wide form of the exact-residual endpoint. -/
theorem mainTheorem_of_canonicalLagrange_stableGraphs_and_projectionTowers
    (hupper : ∀ (A : ℝ → ℝ), IsAbel A →
      ∀ n (F : RealEuclidean n → RealEuclidean n),
        FunctionTupleInFamily (abelGeometricFamily A) F →
          HasGabrielovUniformUpperNumberProperty F)
    (hcovers : ∀ (A : ℝ → ℝ), IsAbel A →
      HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
        (abelGeometricFamily A))
    (hstable : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSection57StableClosureFiberBoundReduction
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_canonicalLagrange_stableGraphs_and_projectionTowers
    (hupper A hA) (hcovers A hA) (hstable A hA) (htowers A hA)

/-- Family-wide exact-residual endpoint after eliminating the independent
closure-fibre cardinality premise from section 5.7. -/
theorem mainTheorem_of_canonicalLagrange_openLocalization_and_projectionTowers
    (hupper : ∀ (A : ℝ → ℝ), IsAbel A →
      ∀ n (F : RealEuclidean n → RealEuclidean n),
        FunctionTupleInFamily (abelGeometricFamily A) F →
          HasGabrielovUniformUpperNumberProperty F)
    (hcovers : ∀ (A : ℝ → ℝ), IsAbel A →
      HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
        (abelGeometricFamily A))
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
  exact hA.oMinimal_of_canonicalLagrange_openLocalization_and_projectionTowers
    (hupper A hA) (hcovers A hA) (hlocalize A hA) (htowers A hA)

end AbelFormalization
