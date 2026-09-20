import AbelFormalization.FullCentralNumericQuantitativeTransfer

/-!
# Numeric quantitative transfer through ordered-cluster simultaneous steps

The simultaneous transfer developed earlier evaluates the complete smaller-prefix
coefficient ring in real sequences.  A fixed displayed step only uses the
finitely many coefficients in its canonical source polynomials and two finite
numeric change-of-generators matrices.  This module exposes exactly those
values, then propagates a lower bound backwards through the whole simultaneous
segment using one numeric change-of-family identity at each retained boundary.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

namespace RepresentativeClusterSubsequence
namespace OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData

variable {R : Type u} [CommRing R]
variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable {data : RepresentativeClusterSubsequence time}
variable {higher : ℕ}
variable {fixedSteps : data.OrderedClusterIndividualStepPlan}
variable {fixedOrder : data.OrderedClusterFinalOrderPlan}
variable {initialIdeal : Ideal
  (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
variable {j : ℕ} {hj : j < data.orderedClusterCount}
variable {stage : OrderedClusterPreprocessedAlgebraicStage R data higher
  fixedSteps fixedOrder initialIdeal j hj}

/-- One actual simultaneous operation, evaluated from only finite numeric
coefficient data.  The hierarchy and domination records come from the fixed
balancing plan; the central and source identities are the two evaluation
seams left to the concrete coefficient realization. -/
theorem simultaneousBeforeValue_lower_of_afterValue_lower_numeric
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    {A : ℝ → ℝ} (hA : IsAbel A)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (baseTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (baseTime n))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps ⟨j, hj⟩)
    (hfixedOrder : ∀ n, (plans n).finalOrder = fixedOrder ⟨j, hj⟩)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : ((r.val + 6 : ℕ) : ℝ) ≤ N)
    (hbaseTop : Tendsto baseTime atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ a b : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        a ≠ b →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n a - rawTime n b))
    (coefficientValue :
      Fin (trace.simultaneous.transferCertificate r).count →
        (ClusterOperationSymbol
          (Fin (data.orderedCluster ⟨j, hj⟩).card)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) →₀ ℕ) →
          ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (afterValue : Fin ((trace.simultaneousDisplayed r).central.count + 1) →
      ℕ → ℝ)
    (centralCoefficient :
      Fin ((trace.simultaneousDisplayed r).central.count + 1) →
        Fin (trace.simultaneous.transferCertificate r).count → ℕ → ℝ)
    (beforeValue : Fin ((trace.simultaneousDisplayed r).source.count + 1) →
      ℕ → ℝ)
    (sourceCoefficient :
      Fin (trace.simultaneous.transferCertificate r).count →
        Fin ((trace.simultaneousDisplayed r).source.count + 1) → ℕ → ℝ)
    (hcoefficient : ∀ a e,
      e ∈ ((trace.simultaneous.transferCertificate r).source a).support →
        HasPolynomialUpperBound atTop
          (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
          (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
        (finiteRealJetMainAssignment A
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) x))
    (hjetError : ∀ i
      (q : Fin (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)),
      Asymptotics.SuperpolynomialDecay atTop
        (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
        (fun n ↦ (jets n i).error q))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      afterValue b n =
        ∑ a, centralCoefficient b a n *
          ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation A
              (terminalTotalDerivativeCount (fun _ :
                Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher))
              (coefficientValue a)
              (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
                (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
              ((trace.simultaneous.transferCertificate r).source a) n)
    (hcentralCoefficient : ∀ b a,
      HasPolynomialUpperBound atTop
        (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
        (centralCoefficient b a))
    (hafterLower : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      afterValue)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
            (terminalTotalDerivativeCount (fun _ :
              Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher))
            (coefficientValue a)
            (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
              (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
            jets ((trace.simultaneous.transferCertificate r).source a) n =
        ∑ k, sourceCoefficient a k n * beforeValue k n)
    (hsourceCoefficient : ∀ a k,
      HasPolynomialUpperBound atTop
        (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        (sourceCoefficient a k)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      beforeValue := by
  let u := data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
    (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val
  let Rscale := data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
    (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1)
  let Xscale := data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
    (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val
  have hierarchies := hA.orderedClusterSimultaneousStep_transferHierarchies
    data ⟨j, hj⟩ rawTime baseTime plans (fixedSteps ⟨j, hj⟩)
      (fixedOrder ⟨j, hj⟩) hfixedSteps hfixedOrder r.val
      hseparationConstant hN hbaseTop hseparated
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchies.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hXone : ∀ᶠ n in atTop, 1 ≤ Xscale n := by
    rcases hierarchies with ⟨_, _, _, domination⟩
    exact domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  haveI : Nonempty (Fin (trace.simultaneous.transferCertificate r).count) :=
    trace.simultaneous.source_nonempty r
  have hcentralUniform : HasUniformPolynomialUpperBound atTop Rscale
      centralCoefficient :=
    hasUniformPolynomialUpperBound_of_finite centralCoefficient hRone
      hcentralCoefficient
  have hsourceUniform : HasUniformPolynomialUpperBound atTop Xscale
      sourceCoefficient :=
    hasUniformPolynomialUpperBound_of_finite sourceCoefficient hXone
      hsourceCoefficient
  exact (trace.simultaneousDisplayed r).realJet_source_lower_of_central_lower_numeric
    hA coefficientValue u jets
      Rscale Xscale hierarchies afterValue centralCoefficient beforeValue
      sourceCoefficient hcoefficient hmainBound hjetError hcentralIdentity
      hcentralUniform hafterLower hsourceIdentity hsourceUniform

/-- All finite numeric inputs for one simultaneous operation.  Matrix bounds
are stated pointwise; finiteness upgrades them to the uniform bounds used by
the quantitative transfer theorem. -/
structure SimultaneousNumericQuantitativeData
    (trace : stage.FullTransferTraceData)
    (A : ℝ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1)) where
  coefficientValue :
    Fin (trace.simultaneous.transferCertificate r).count →
      (ClusterOperationSymbol
        (Fin (data.orderedCluster ⟨j, hj⟩).card)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) →₀ ℕ) →
        ℕ → ℝ
  jets : ∀ n i, RealCentralJetSubstitutionData A
    (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val i n)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)
  afterValue : Fin ((trace.simultaneousDisplayed r).central.count + 1) →
    ℕ → ℝ
  centralCoefficient :
    Fin ((trace.simultaneousDisplayed r).central.count + 1) →
      Fin (trace.simultaneous.transferCertificate r).count → ℕ → ℝ
  beforeValue : Fin ((trace.simultaneousDisplayed r).source.count + 1) →
    ℕ → ℝ
  sourceCoefficient :
    Fin (trace.simultaneous.transferCertificate r).count →
      Fin ((trace.simultaneousDisplayed r).source.count + 1) → ℕ → ℝ
  coefficient_bound : ∀ a e,
    e ∈ ((trace.simultaneous.transferCertificate r).source a).support →
      HasPolynomialUpperBound atTop
        (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
        (coefficientValue a e)
  main_bound : ∀ x,
    HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (finiteRealJetMainAssignment A
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) x)
  jet_error : ∀ i
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)),
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (fun n ↦ (jets n i).error q)
  central_identity : ∀ᶠ n in atTop, ∀ b,
    afterValue b n =
      ∑ a, centralCoefficient b a n *
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation A
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher))
          (coefficientValue a)
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
          ((trace.simultaneous.transferCertificate r).source a) n
  central_coefficient_bound : ∀ b a,
    HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (centralCoefficient b a)
  source_identity : ∀ᶠ n in atTop, ∀ a,
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher))
        (coefficientValue a)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        jets ((trace.simultaneous.transferCertificate r).source a) n =
      ∑ k, sourceCoefficient a k n * beforeValue k n
  source_coefficient_bound : ∀ a k,
    HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      (sourceCoefficient a k)

/-- Bundled form of the numeric one-step theorem. -/
theorem simultaneousBeforeValue_lower_of_afterValue_lower_numeric_of_data
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    {A : ℝ → ℝ} (hA : IsAbel A)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (baseTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (baseTime n))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps ⟨j, hj⟩)
    (hfixedOrder : ∀ n, (plans n).finalOrder = fixedOrder ⟨j, hj⟩)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : ((r.val + 6 : ℕ) : ℝ) ≤ N)
    (hbaseTop : Tendsto baseTime atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ a b : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        a ≠ b →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n a - rawTime n b))
    (step : SimultaneousNumericQuantitativeData trace A rawTime r)
    (hafterLower : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      step.afterValue) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      step.beforeValue := by
  exact trace.simultaneousBeforeValue_lower_of_afterValue_lower_numeric r hA
    rawTime baseTime plans hfixedSteps hfixedOrder hseparationConstant hN
    hbaseTop hseparated step.coefficientValue step.jets step.afterValue
    step.centralCoefficient step.beforeValue step.sourceCoefficient
    step.coefficient_bound step.main_bound step.jet_error
    step.central_identity step.central_coefficient_bound hafterLower
    step.source_identity step.source_coefficient_bound

/-- Numeric data for the complete simultaneous segment.  At an internal
retained boundary, only the representation of the next source family as
linear combinations of the preceding central family is needed.  The reverse
representation is deliberately absent. -/
structure SimultaneousNumericSegmentQuantitativeData
    (trace : stage.FullTransferTraceData)
    (A : ℝ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ) where
  step : (r : Fin (stage.certificate.terminalized.extraSteps + 1)) →
    SimultaneousNumericQuantitativeData trace A rawTime r
  adjacentCoefficient :
    (i : Fin stage.certificate.terminalized.extraSteps) →
      Fin ((trace.simultaneousDisplayed i.succ).source.count + 1) →
      Fin ((trace.simultaneousDisplayed i.castSucc).central.count + 1) →
        ℕ → ℝ
  adjacent_coefficient_bound : ∀ i k b,
    HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
      (adjacentCoefficient i k b)
  adjacent_identity : ∀ i, ∀ᶠ n in atTop, ∀ k,
    (step i.succ).beforeValue k n =
      ∑ b, adjacentCoefficient i k b n *
        (step i.castSucc).afterValue b n

/-- Propagate a terminal central-family lower bound backwards through every
extra retained operation and the distinguished first simultaneous operation.
For `extraSteps = 0`, the decreasing induction has no internal boundary and
the theorem is exactly the first one-step transfer. -/
theorem firstBeforeValue_lower_of_terminalAfterValue_lower_numeric
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (baseTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (baseTime n))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps ⟨j, hj⟩)
    (hfixedOrder : ∀ n, (plans n).finalOrder = fixedOrder ⟨j, hj⟩)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : (((stage.certificate.terminalized.extraSteps + 6 : ℕ) : ℝ)) ≤ N)
    (hbaseTop : Tendsto baseTime atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ a b : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        a ≠ b →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n a - rawTime n b))
    (segment : SimultaneousNumericSegmentQuantitativeData trace A rawTime)
    (hterminal : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩)
        (stage.certificate.terminalized.extraSteps + 1))
      (segment.step (Fin.last
        stage.certificate.terminalized.extraSteps)).afterValue) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
      (segment.step stage.certificate.firstCentralStepIndex).beforeValue := by
  let extra := stage.certificate.terminalized.extraSteps
  let scale := data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
    (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩)
  let StepLower := fun r : Fin (extra + 1) ↦
    HasInversePowerLowerBound atTop (scale r.val)
      (segment.step r).beforeValue
  have margin (r : Fin (extra + 1)) : (((r.val + 6 : ℕ) : ℝ)) ≤ N := by
    calc
      (((r.val + 6 : ℕ) : ℝ)) ≤ (((extra + 6 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ r.isLt) 6
      _ ≤ N := hN
  have top : StepLower (Fin.last extra) := by
    exact trace.simultaneousBeforeValue_lower_of_afterValue_lower_numeric_of_data
      (Fin.last extra) hA rawTime baseTime plans hfixedSteps hfixedOrder
      hseparationConstant (margin (Fin.last extra)) hbaseTop hseparated
      (segment.step (Fin.last extra)) hterminal
  have descent : StepLower stage.certificate.firstCentralStepIndex := by
    change StepLower (⟨0, Nat.succ_pos extra⟩ : Fin (extra + 1))
    refine Nat.decreasingInduction (n := extra)
        (motive := fun k hk ↦ StepLower
          ⟨k, Nat.lt_succ_iff.mpr hk⟩) ?_ ?_ (Nat.zero_le extra)
    · intro k hk ih
      let i : Fin extra := ⟨k, hk⟩
      let previous : Fin (extra + 1) := i.castSucc
      let next : Fin (extra + 1) := i.succ
      have ihNext : StepLower next := by
        have hindex : next =
            (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (extra + 1)) := Fin.ext rfl
        rw [hindex]
        exact ih
      have hierarchies := hA.orderedClusterSimultaneousStep_transferHierarchies
        data ⟨j, hj⟩ rawTime baseTime plans (fixedSteps ⟨j, hj⟩)
          (fixedOrder ⟨j, hj⟩) hfixedSteps hfixedOrder previous.val
          hseparationConstant (margin previous) hbaseTop hseparated
      have hscale : ∀ᶠ n in atTop, 1 ≤ scale next.val n := by
        simpa only [scale, next, previous, Fin.val_succ, Fin.val_castSucc]
          using hierarchies.scale_ge_two.mono
            (fun _ hn ↦ one_le_two.trans hn)
      have hafter : HasInversePowerLowerBound atTop (scale next.val)
          (segment.step previous).afterValue := by
        apply hasInversePowerLowerBound_of_linearCombinations
          (segment.step previous).afterValue
          (segment.step next).beforeValue
          (segment.adjacentCoefficient i) hscale
        · simpa only [i, previous, next] using segment.adjacent_identity i
        · exact hasUniformPolynomialUpperBound_of_finite
            (segment.adjacentCoefficient i) hscale
            (segment.adjacent_coefficient_bound i)
        · exact ihNext
      have hprevious :=
        trace.simultaneousBeforeValue_lower_of_afterValue_lower_numeric_of_data
          previous hA rawTime baseTime plans hfixedSteps hfixedOrder
          hseparationConstant (margin previous) hbaseTop hseparated
          (segment.step previous) (by
            simpa only [scale, next, previous, Fin.val_succ,
              Fin.val_castSucc] using hafter)
      have hindex : previous =
          (⟨k, Nat.lt_succ_of_lt hk⟩ : Fin (extra + 1)) := Fin.ext rfl
      rw [← hindex]
      exact hprevious
    · have hindex : (Fin.last extra : Fin (extra + 1)) =
          ⟨extra, Nat.lt_succ_self extra⟩ := Fin.ext rfl
      rw [← hindex]
      exact top
  simpa only [StepLower, scale,
    ClusterAlgebraicReductionCertificate.firstCentralStepIndex] using descent

end OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData
end RepresentativeClusterSubsequence
end AbelFormalization
