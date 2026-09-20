import AbelFormalization.CharbonnelClosedBoundaryCellAssembly
import AbelFormalization.CharbonnelSourceStageIntegerAffineTrace
import AbelFormalization.CharbonnelSardianProjectionMorseSardReduction
import AbelFormalization.Wilkie27CriticalValues
import AbelFormalization.MaxwellSection5Smoothness
import AbelFormalization.ProjectedZeroComplementCriterion
import AbelFormalization.Consequences
import AbelFormalization.Definability

/-!
# Source-shaped endpoint for the complement theorem

This module assembles the strongest source-shaped reduction currently proved.
The finite locally closed decomposition used by the older pipeline is replaced
by Maxwell's family-level meagre-selection step.  Wilkie's critical-value
selection argument now constructs the positive-projection Sardian step from
the same Theorems 2.1 and 2.2 produced by the source pipeline.  The strongest
endpoint therefore has four genuine source obligations: uniform fiber
finiteness, meagre selection, the section 5 analytic step, and the remaining
higher-dimensional compatible-cell-cover induction.  The unary cell base and
the finite-cover/WS6 assembly are theorems, as are both Sardian branches.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Maxwell selection and the analytic section 5 successor give exactly the
trace-tameness package consumed by Sardian boundary descent. -/
theorem
    literalZeroSet_charbonnelClosure_approximationTraceTameness_of_meagreSelection_and_analyticStep
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)) := by
  have hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  obtain ⟨h21, h22⟩ :=
    literalZeroSet_charbonnelTheorems21And22_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  exact literalZeroSet_charbonnelClosure_traceTameness hG hsmooth
    (charbonnelApproximationTraceSmallness_of_theorems21_22
      hmem h21 h22)

/-- The exact five remaining source obligations construct the concrete all-arity
projected-zero complement envelope; no external complement principle or
Maxwell smoothness package is assumed. -/
noncomputable def projectedZeroComplementEnvelope_of_charbonnelSourceSteps
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (hcell : CharbonnelClosedBoundaryComplementAssembly G) :
    ProjectedZeroComplementEnvelope G := by
  have htrace : CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_approximationTraceTameness_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  have hsardian : CharbonnelSardianApproximationRankStep G :=
    charbonnelSardianApproximationRankStep_of_projection
      hG hsmooth hprojection
  apply
    projectedZeroComplementEnvelope_of_literalZeroSet_charbonnelClosure_compl
      hG hsmooth hUFF
  exact hcell
    (literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty
      hG htrace hsardian)

/-- Source endpoint with the former abstract cell-assembly premise replaced by
the exact remaining higher-dimensional compatible-cell-cover construction.
The unary base, finite-cover union, and WS6 closed-lift passage are discharged
by `CharbonnelClosedBoundaryCellAssembly`. -/
noncomputable def
    projectedZeroComplementEnvelope_of_charbonnelSourceSteps_and_cellCovers
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (hcells : CharbonnelClosedBoundaryCellCoverAssembly G) :
    ProjectedZeroComplementEnvelope G :=
  projectedZeroComplementEnvelope_of_charbonnelSourceSteps
    hG hsmooth hUFF hselection hanalytic hprojection
      (charbonnelClosedBoundaryComplementAssembly_of_cellCovers
        hG hsmooth hUFF hcells)

/-- Pointwise main o-minimality conclusion from the exact remaining source
steps, specialized to the Abel geometric family. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hprojection : CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily A))
    (hcell : CharbonnelClosedBoundaryComplementAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    (projectedZeroComplementEnvelope_of_charbonnelSourceSteps
      hG hsmooth hUFF hselection hanalytic hprojection hcell).oMinimal

/-- Rectangular Morse--Sard discharges the positive-projection premise in
the source pipeline. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps_and_rectangularMorseSard
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hMS : RectangularMorseSardInput)
    (hcell : CharbonnelClosedBoundaryComplementAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  obtain ⟨h21, h22⟩ :=
    literalZeroSet_charbonnelTheorems21And22_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  exact hA.oMinimal_of_charbonnelSourceSteps hUFF hselection hanalytic
    (hA.charbonnelSardianProjectionConstructorInput_of_rectangularMorseSard
      hUFF h21 h22 hMS)
    hcell

/-- Wilkie's family-theoretic critical-value theorem discharges the
positive-projection premise internally.  This is the strongest pointwise
source endpoint: it assumes no independent Morse--Sard or projection input. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcell : CharbonnelClosedBoundaryComplementAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  obtain ⟨h21, h22⟩ :=
    literalZeroSet_charbonnelTheorems21And22_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  exact hA.oMinimal_of_charbonnelSourceSteps hUFF hselection hanalytic
    (hA.charbonnelSardianProjectionConstructorInput_of_theorems21_22
      hUFF h21 h22)
    hcell

/-- Pointwise o-minimality endpoint with Wilkie's former closed-boundary
assembly premise narrowed to the higher-dimensional closed-lift cell-cover
construction.  Projection is discharged internally. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_cellCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection
    hUFF hselection hanalytic
    (charbonnelClosedBoundaryComplementAssembly_of_cellCovers
      hG hsmooth hUFF hcells)

/-- Under the same five source obligations, all four clauses of the proposed
main theorem hold for the fixed Abel function. -/
theorem IsAbel.mainTheoremConclusion_of_charbonnelSourceSteps
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hprojection : CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily A))
    (hcell : CharbonnelClosedBoundaryComplementAssembly
      (abelGeometricFamily A)) :
    OMinimal A ∧ ExponentialDefinable A ∧
      PositiveInverseDefinable A (inverse A) ∧
        IsTransexponential (inverse A) :=
  ⟨hA.oMinimal_of_charbonnelSourceSteps hUFF hselection hanalytic
      hprojection hcell,
    hA.exponentialDefinable, hA.positiveInverseDefinable,
    hA.isTransexponential⟩

/-- Family-wide form of the exact source reduction.  This theorem does not
assert any of its five hypotheses; it records that proving them for every Abel
function is sufficient for the literal `MainTheorem` declaration. -/
theorem mainTheorem_of_charbonnelSourceSteps
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
    (hprojection : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSardianProjectionConstructorInput
        (abelGeometricFamily A))
    (hcell : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelClosedBoundaryComplementAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  exact hA.mainTheoremConclusion_of_charbonnelSourceSteps
    (hUFF A hA) (hselection A hA) (hanalytic A hA)
      (hprojection A hA) (hcell A hA)

/-- Source endpoint with the projection constructor replaced by the precise
rectangular Morse--Sard theorem proved sufficient above. -/
theorem mainTheorem_of_charbonnelSourceSteps_and_rectangularMorseSard
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
    (hMS : RectangularMorseSardInput)
    (hcell : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelClosedBoundaryComplementAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_charbonnelSourceSteps_and_rectangularMorseSard
    (hUFF A hA) (hselection A hA) (hanalytic A hA) hMS (hcell A hA)

/-- Strongest source endpoint.  Projection regularity is proved internally by
Wilkie's weak-selection/differentiable-section contradiction, so only the
four still-unproved source obligations remain. -/
theorem mainTheorem_of_charbonnelSourceSteps_automaticProjection
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
    (hcell : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelClosedBoundaryComplementAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection
    (hUFF A hA) (hselection A hA) (hanalytic A hA) (hcell A hA)

/-- Strongest family-wide endpoint.  Both Sardian branches, the unary cell
base, and the finite-cover/closed-lift complement assembly are internal; the
remaining cell premise is precisely Wilkie's higher-dimensional compatible
cell-cover induction. -/
theorem mainTheorem_of_charbonnelSourceSteps_automaticProjection_and_cellCovers
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
      CharbonnelClosedBoundaryCellCoverAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_cellCovers
    (hUFF A hA) (hselection A hA) (hanalytic A hA) (hcells A hA)

end AbelFormalization
