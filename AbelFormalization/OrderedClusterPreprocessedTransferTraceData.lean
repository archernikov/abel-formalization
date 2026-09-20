import AbelFormalization.OrderedClusterPreprocessedAlgebraicDescent
import AbelFormalization.OrderedClusterIndividualTraceData
import AbelFormalization.OrderedClusterCentralRealJetIdentities

/-!
# Complete finite transfer data at a preprocessed ordered-cluster stage

An ordered-cluster stage has two chronological parts.  First, its fixed list
of individual logarithmic decrements acts in the literal prefix ring.  Then
the resulting ideal is curried and relabeled before the simultaneous central
operations stored by the cluster reduction certificate.

This module chooses all quantitative certificates, finite displayed
generators, and exact change-of-generators identities for both parts at once.
It is purely algebraic; sequence evaluations and scale estimates are added by
the analytic trace modules.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

namespace OrderedClusterPreprocessedAlgebraicStage

/-- Every finite quantitative-transfer choice belonging to one preprocessed
ordered-cluster stage, including displayed generators on both sides of every
operation. -/
structure FullTransferTraceData
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj) where
  individual : data.OrderedClusterIndividualIdealTraceData R higher
    ⟨j, hj⟩ (fixedSteps ⟨j, hj⟩) stage.preprocessingInput
  individualDisplayed :
    data.OrderedClusterIndividualDisplayedTraceData R higher ⟨j, hj⟩
      (fixedSteps ⟨j, hj⟩) stage.preprocessingInput individual
  simultaneous : stage.certificate.FullCentralTransferData
  simultaneousDisplayed :
    (r : Fin (stage.certificate.terminalized.extraSteps + 1)) →
      ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
        simultaneous r

/-- Noetherianity supplies all finite transfer and displayed-generator data
for a preprocessed stage simultaneously. -/
theorem nonempty_fullTransferTraceData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj)
    [IsNoetherianRing (data.OrderedClusterPrefixRing R higher j)] :
    Nonempty stage.FullTransferTraceData := by
  classical
  let individual := Classical.choice
    (data.nonempty_orderedClusterIndividualIdealTraceData R higher ⟨j, hj⟩
      (fixedSteps ⟨j, hj⟩) stage.preprocessingInput)
  let individualDisplayed := Classical.choice
    (data.nonempty_orderedClusterIndividualDisplayedTraceData R higher
      ⟨j, hj⟩ (fixedSteps ⟨j, hj⟩) stage.preprocessingInput
      individual)
  let simultaneous := Classical.choice
    stage.certificate.nonempty_fullCentralTransferData
  let simultaneousDisplayed :=
    fun r : Fin (stage.certificate.terminalized.extraSteps + 1) ↦
      Classical.choice
        (ClusterAlgebraicReductionCertificate.nonempty_fullCentralStepDisplayedData
          simultaneous r)
  exact ⟨{
    individual := individual
    individualDisplayed := individualDisplayed
    simultaneous := simultaneous
    simultaneousDisplayed := simultaneousDisplayed
  }⟩

namespace FullTransferTraceData

/-- The individual part begins at the literal incoming stage ideal. -/
@[simp]
theorem individual_initial_boundary
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    {stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj}
    (trace : stage.FullTransferTraceData) :
    data.orderedClusterIndividualIdealBoundary R higher ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩) stage.preprocessingInput 0 =
      stage.preprocessingInput := by
  exact data.orderedClusterIndividualIdealBoundary_zero R higher ⟨j, hj⟩
    (fixedSteps ⟨j, hj⟩) stage.preprocessingInput

/-- The last individual boundary is exactly the preprocessing output used to
form the simultaneous reduction input. -/
@[simp]
theorem individual_terminal_boundary
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    {stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj}
    (trace : stage.FullTransferTraceData) :
    data.orderedClusterIndividualIdealBoundary R higher ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩) stage.preprocessingInput
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length) =
      stage.preprocessingOutput := by
  exact data.orderedClusterIndividualIdealBoundary_last R higher ⟨j, hj⟩
    (fixedSteps ⟨j, hj⟩) stage.preprocessingInput

/-- The first simultaneous transfer input is the curried and final-order
relabeled preprocessing output stored in the stage certificate. -/
@[simp]
theorem simultaneous_first_input
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    {stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj}
    (trace : stage.FullTransferTraceData) :
    stage.certificate.centralTransferInput
        stage.certificate.firstCentralStepIndex = stage.reductionInput := by
  rfl

/-- The first displayed simultaneous source family spans the translated
actual reduction input. -/
theorem simultaneous_first_source_span
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    {stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj}
    (trace : stage.FullTransferTraceData) :
    Ideal.span (Set.range
      (trace.simultaneousDisplayed
        stage.certificate.firstCentralStepIndex).source.generator) =
      stage.reductionInput.map
        (polynomialCoordinateTranslation
          (Sum.elim
            (fun _ : Fin (data.orderedCluster ⟨j, hj⟩).card ↦
              (-1 : data.OrderedClusterPrefixRing R higher j))
            (fun _ : CentralPolynomialIndex
                (Fin (data.orderedCluster ⟨j, hj⟩).card)
                (terminalTotalDerivativeCount (fun _ ↦ higher))
                (Fin (data.orderedCluster ⟨j, hj⟩).card) ↦ 0))).toRingHom := by
  exact
    (trace.simultaneousDisplayed
      stage.certificate.firstCentralStepIndex).first_source_span

end FullTransferTraceData
end OrderedClusterPreprocessedAlgebraicStage

end RepresentativeClusterSubsequence
end AbelFormalization
