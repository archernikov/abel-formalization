import AbelFormalization.CharbonnelPositiveZeroTraceCategory
import AbelFormalization.CharbonnelSardianProjectionCategory
import AbelFormalization.CharbonnelSardianRankConstructorReduction
import AbelFormalization.WilkieProjectionCoherentCellCoverTower
import AbelFormalization.LionUniformFiberFinitenessTheorem
import AbelFormalization.ProjectedZeroComplementCriterion
import AbelFormalization.Consequences
import AbelFormalization.Definability

/-!
# Main theorem after direct trace smallness

The category proof of positive-zero-trace smallness removes the Charbonnel
section 5 analytic and localization premises from the complement pipeline.
Lion supplies uniform fiber finiteness.  The exact remaining inputs are the
Sardian projection constructor and the bounded projection-coherent Section 4
tower.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Direct trace tameness, a Sardian projection constructor, and the bounded
Section 4 tower construct the projected-zero complement envelope. -/
noncomputable def
    projectedZeroComplementEnvelope_of_directTrace_projection_and_towers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G) :
    ProjectedZeroComplementEnvelope G := by
  have htrace : CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_approximationTraceTameness
      hG hsmooth hUFF
  have hsardian : CharbonnelSardianApproximationRankStep G :=
    charbonnelSardianApproximationRankStep_of_projection
      hG hsmooth hprojection
  have hcell : CharbonnelClosedBoundaryComplementAssembly G :=
    charbonnelClosedBoundaryComplementAssembly_of_boundedProjectionCoherentTowers
      hG hsmooth hUFF htowers
  apply
    projectedZeroComplementEnvelope_of_literalZeroSet_charbonnelClosure_compl
      hG hsmooth hUFF
  exact hcell
    (literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty
      hG htrace hsardian)

/-- Pointwise o-minimality with all Lion and trace-smallness inputs discharged
internally. -/
theorem IsAbel.oMinimal_of_projection_and_towers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hprojection : CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily A))
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    (projectedZeroComplementEnvelope_of_directTrace_projection_and_towers
      hG hsmooth hA.hasUniformFiberFiniteness hprojection htowers).oMinimal

/-- Family-wide exact residual after Lion uniform finiteness and direct trace
smallness: Sardian projection and the bounded Section 4 tower. -/
theorem mainTheorem_of_projection_and_towers
    (hprojection : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSardianProjectionConstructorInput
        (abelGeometricFamily A))
    (htowers : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_projection_and_towers
    (hprojection A hA) (htowers A hA)

/-- Lion uniform finiteness and the category construction discharge the
Sardian projection input.  The bounded projection-coherent Section 4 tower
is the sole remaining pointwise premise. -/
theorem IsAbel.oMinimal_of_towers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  have hUFF : HasUniformFiberFiniteness (abelGeometricFamily A) :=
    hA.hasUniformFiberFiniteness
  exact hA.oMinimal_of_projection_and_towers
    (hA.charbonnelSardianProjectionConstructorInput_of_category hUFF)
    htowers

/-- Exact family-wide residual: proving the bounded projection-coherent
Section 4 tower for each Abel family proves the literal main theorem. -/
theorem mainTheorem_of_towers
    (htowers : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨hA.oMinimal_of_towers (htowers A hA),
    hA.exponentialDefinable, hA.positiveInverseDefinable,
    hA.isTransexponential⟩

end AbelFormalization
