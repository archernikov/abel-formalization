import AbelFormalization.HermiteRankPreprocessedIndividualMixedBoundary
import AbelFormalization.HermiteRankPreprocessedSimultaneousNumericData

/-!
# Quantitative propagation through the mixed individual Hermite trace

The recursively mixed boundary supplies the correct source jet at every
individual decrement: the paper Hermite jet at a first occurrence and the
exact derivative jet at every repeated occurrence.  This module connects
that boundary to the coefficientwise numeric transfer API.

All hierarchy, growth, and jet-error estimates are proved from the paper
data.  The residual input is finite and analytic: at each displayed step the
caller supplies the two evaluated change-of-generators identities and their
polynomial coefficient bounds.  No evaluation homomorphism on the full ring
of analytic germs is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

noncomputable local instance individualMixedQuantitativeBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- The actual algebraic transfer datum selected by one fixed individual
balancing step. -/
abbrev individualMixedTransferData
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  (boundary.preprocessed.transferTrace.stage c).individual.transferData
    (data.orderedClusterIndividualStepIndexEquiv c
      (boundary.preprocessed.fixedSteps c) j)

/-- Supported outer coefficients of the canonical source family at one
individual step. -/
abbrev IndividualMixedSourceCoefficientIndex
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  Sigma fun q : Fin ((boundary.individualMixedTransferData D representative
    offset radius Fsys x w₀ hw₀ data c j).certificate.count) ↦
    {e // e ∈ ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.source q).support}

/-- The remaining-block coefficient polynomial named by one supported outer
monomial of a canonical individual source. -/
def individualMixedSourceCoefficientPolynomial
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (qe : boundary.IndividualMixedSourceCoefficientIndex D representative
      offset radius Fsys x w₀ hw₀ data c j) :
    IndividualCentralCoefficientRing (RealAnalyticGerm p)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
      (data.orderedClusterIndividualSelectedBlock c
        (boundary.preprocessed.fixedSteps c) j) :=
  ((boundary.individualMixedTransferData D representative offset radius Fsys x
    w₀ hw₀ data c j).certificate.source qe.1).coeff qe.2

/-- One common finite family of moving analytic representatives for every
supported remaining-block coefficient polynomial occurring in an individual
step. -/
abbrev IndividualMixedSourceCoefficientData
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  FiniteMovingCoefficientData
    (boundary.individualMixedSourceCoefficientPolynomial D representative
      offset radius Fsys x w₀ hw₀ data c j)

/-- The finite moving coefficient family exists for every individual step. -/
theorem nonempty_individualMixedSourceCoefficientData
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    Nonempty (boundary.IndividualMixedSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c j) := by
  exact nonempty_finiteMovingCoefficientData
    (boundary.individualMixedSourceCoefficientPolynomial D representative
      offset radius Fsys x w₀ hw₀ data c j)

/-- The remaining-block assignment used to evaluate the coefficient ring.
It is read at the post-boundary, where the canonical scale is the source
transfer scale; all unselected coordinates agree with the pre-boundary. -/
def individualMixedRemainingSymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  selectedBlockCoefficientAssignment
    (data.orderedClusterPrefixConstantDerivativeCount
      (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
    (data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j)
    (boundary.individualMixedBoundarySymbolValue D representative offset radius
      Fsys x w₀ hw₀ data hA c
      (data.orderedClusterIndividualStepIndexEquiv c
        (boundary.preprocessed.fixedSteps c) j).succ)

/-- Every remaining-block coordinate is polynomially bounded at the
post-boundary scale. -/
theorem individualMixedRemainingSymbolValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : ClusterOperationSymbol
      (RemainingBlock (data.orderedClusterIndividualSelectedBlock c
        (boundary.preprocessed.fixedSteps c) j))
      (remainingBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j))) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j z) := by
  unfold individualMixedRemainingSymbolValue selectedBlockCoefficientAssignment
  simpa only [individualNumericBoundaryScale,
    RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
    Fin.val_succ,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
    using boundary.individualMixedBoundarySymbolValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c
      (data.orderedClusterIndividualStepIndexEquiv c
        (boundary.preprocessed.fixedSteps c) j).succ _

/-- Numeric value of one supported outer coefficient, evaluated through its
moving remaining-block polynomial representative.  Values outside the
canonical source support are set to zero. -/
noncomputable def individualMixedSourceCoefficientValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count))
    (e : RealJetTransferIndex 0
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j) →₀ ℕ)
    (n : ℕ) : ℝ := by
  classical
  exact
    if he : e ∈ ((boundary.individualMixedTransferData D representative offset
        radius Fsys x w₀ hw₀ data c j).certificate.source q).support then
      coefficients.polynomialValueAlong
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        ⟨q, ⟨e, he⟩⟩ n
    else 0

/-- Supported coefficient values are automatically polynomially bounded at
the post-boundary scale. -/
theorem individualMixedSourceCoefficientValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count))
    (e : RealJetTransferIndex 0
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j) →₀ ℕ)
    (he : e ∈ ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.source q).support) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (boundary.individualMixedSourceCoefficientValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j coefficients q e) := by
  refine (coefficients.polynomialValueAlong_hasPolynomialUpperBound
    (boundary.individualNumericAnalyticParameter D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (boundary.individualNumericAnalyticParameter_tendsto D representative offset
      radius Fsys x w₀ hw₀ data hA)
    (boundary.individualMixedRemainingSymbolValue D representative offset radius
      Fsys x w₀ hw₀ data hA c j)
    (data.orderedClusterBalancingPrefixScale A
      (boundary.individualQuantitativeSubsequence D representative offset radius
        Fsys x w₀ hw₀ data hA) c
      (boundary.preprocessed.fixedSteps c) j.succ)
    (Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c) j.succ n))
    (boundary.individualMixedRemainingSymbolValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c j)
    ⟨q, ⟨e, he⟩⟩).congr ?_
  intro n
  rw [individualMixedSourceCoefficientValue, dite_eq_left he]

/-- Restriction of the polynomially bounded mixed flat boundary to one
selected active block remains polynomially bounded. -/
theorem individualMixedActiveValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (selected : data.OrderedClusterPrefixBlock (c.val + 1))
    (z : ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected)) :
    HasPolynomialUpperBound atTop
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c q)
      (selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c q) z) := by
  unfold selectedBlockActiveAssignment
  exact boundary.individualMixedBoundarySymbolValue_hasPolynomialUpperBound D
    representative offset radius Fsys x w₀ hw₀ data hA c q _

/-- Every exact central coordinate at an individual post-boundary is bounded
by that boundary's canonical balancing scale. -/
theorem individualMixedCentralValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : CentralPolynomialIndex (Fin 1)
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j) (Fin 1)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦ realCentralTransferCentralValue A
        (fun i ↦ data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j i n)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j) z) := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  have hactive := boundary.individualMixedActiveValue_hasPolynomialUpperBound D
    representative offset radius Fsys x w₀ hw₀ data hA c step.succ selected
      (Sum.inr z)
  have hpost : selectedBlockActiveAssignment d selected
      (boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c step.succ) =
        individualCentralPostLogActiveAssignment A
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA q) c)
            (boundary.preprocessed.fixedSteps c) j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j) := by
    exact boundary.selectedBlockActiveAssignment_individualMixedBoundary_afterStep
      D representative offset radius Fsys x w₀ hw₀ data hA c j
  apply hactive.congr
  intro n
  simpa only [individualCentralPostLogActiveAssignment_central] using
    (congrFun (congrFun hpost (Sum.inr z)) n).symm

/-- The error-free real-jet main assignment at an individual step is
polynomially bounded by its post-boundary scale. -/
theorem individualMixedMainValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : RealJetTransferIndex 0
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (realJetMainAssignment A
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j) z) := by
  apply realJetMainAssignment_hasPolynomialUpperBound_of_central
  · exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j.succ n)
  · exact boundary.individualMixedCentralValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c j

/-- Residual finite analytic data for one mixed individual step.  The
displayed before/after values are the canonical values already selected by
`individualMixedNumericBoundaryCompatibility`; only their two finite
coefficientwise evaluation identities remain as input. -/
structure IndividualMixedFiniteAnalyticStepData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j) where
  centralCoefficient :
    Fin (((boundary.individualNumericDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).central.count + 1) →
    Fin ((boundary.individualMixedTransferData D representative offset radius
      Fsys x w₀ hw₀ data c j).certificate.count) → ℕ → ℝ
  sourceCoefficient :
    Fin ((boundary.individualMixedTransferData D representative offset radius
      Fsys x w₀ hw₀ data c j).certificate.count) →
    Fin (((boundary.individualNumericDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).source.count + 1) → ℕ → ℝ
  central_identity : ∀ᶠ n in atTop, ∀ b,
    (boundary.individualMixedNumericBoundaryCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c).afterValue
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j) b n =
      ∑ q, centralCoefficient b q n *
        realJetCoefficientwiseCentralEvaluation A
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedSourceCoefficientValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j)
          ((boundary.individualMixedTransferData D representative offset radius
            Fsys x w₀ hw₀ data c j).certificate.source q) n
  central_coefficient_bound : ∀ b q,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (centralCoefficient b q)
  source_identity : ∀ᶠ n in atTop, ∀ q,
    realJetCoefficientwiseSourceEvaluation
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualMixedSourceCoefficientValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j coefficients q)
        (data.orderedClusterIndividualPostLogScale c A
          (fun k ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA k) c)
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualMixedTraceJets D representative offset radius Fsys
          x w₀ hw₀ data hA c j)
        ((boundary.individualMixedTransferData D representative offset radius
          Fsys x w₀ hw₀ data c j).certificate.source q) n =
      ∑ k, sourceCoefficient q k n *
        (boundary.individualMixedNumericBoundaryCompatibility D representative
          offset radius Fsys x w₀ hw₀ data hA c).beforeValue
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j) k n
  source_coefficient_bound : ∀ q k,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (sourceCoefficient q k)

/-- Backward propagation through one actual mixed individual step.  The
moving source coefficients, hierarchy, main-value bounds, and mixed jet error
are all discharged from the concrete paper data. -/
theorem individualMixedBeforeValue_lower_of_afterValue_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (change : boundary.IndividualMixedFiniteAnalyticStepData D representative
      offset radius Fsys x w₀ hw₀ data hA c j coefficients)
    (hafter : HasInversePowerLowerBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      ((boundary.individualMixedNumericBoundaryCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c).afterValue
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j))) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      ((boundary.individualMixedNumericBoundaryCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c).beforeValue
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)) := by
  let shift : ℕ → ℕ := fun n ↦ n +
    boundary.individualQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat
      (boundary.individualQuantitativeTail D representative offset radius Fsys x
        w₀ hw₀ data hA)
  apply (boundary.individualNumericDisplayed D representative offset radius
    Fsys x w₀ hw₀ data c).beforeGenerator_lower_of_afterGenerator_lower_numeric
      (R := RealAnalyticGerm p)
      (data := data)
      (higher := paperRankHermiteHigherCount boundary.S)
      (c := c)
      (j := j)
      (hA := hA)
      (φ := boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (plans := boundary.individualQuantitativePlans D representative offset
        radius Fsys x w₀ hw₀ data hA c)
      (jets := boundary.individualMixedTraceJets D representative offset radius
        Fsys x w₀ hw₀ data hA c j)
      (coefficientValue :=
        boundary.individualMixedSourceCoefficientValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j coefficients)
      (afterValue :=
        (boundary.individualMixedNumericBoundaryCompatibility D representative
          offset radius Fsys x w₀ hw₀ data hA c).afterValue
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j))
      (centralCoefficientValue := change.centralCoefficient)
      (beforeValue :=
        (boundary.individualMixedNumericBoundaryCompatibility D representative
          offset radius Fsys x w₀ hw₀ data hA c).beforeValue
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j))
      (sourceCoefficientValue := change.sourceCoefficient)
      (N := separation.N c)
      (separationConstant := separation.separationConstant c)
  · intro n
    exact boundary.preprocessed.plans_steps (shift n) c
  · exact separation.separationConstant_pos c
  · exact separation.five_le_N c
  · exact (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c).comp hshift
  · exact hshift.eventually (separation.separated c)
  · intro q e he
    exact boundary.individualMixedSourceCoefficientValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c j coefficients
      q e he
  · exact boundary.individualMixedMainValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  · exact boundary.individualMixedTraceJets_error_superpolynomialDecay D
      representative offset radius Fsys x w₀ hw₀ data separation hA c j
  · exact change.central_identity
  · exact change.central_coefficient_bound
  · exact hafter
  · exact change.source_identity
  · exact change.source_coefficient_bound

/-- Finite analytic inputs for every step of one mixed individual segment. -/
structure IndividualMixedFiniteAnalyticTraceData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) where
  coefficients : (j : Fin (boundary.preprocessed.fixedSteps c).length) →
    boundary.IndividualMixedSourceCoefficientData D representative offset
      radius Fsys x w₀ hw₀ data c j
  step : (j : Fin (boundary.preprocessed.fixedSteps c).length) →
    boundary.IndividualMixedFiniteAnalyticStepData D representative offset
      radius Fsys x w₀ hw₀ data hA c j (coefficients j)

/-- A lower bound at the last mixed boundary propagates through every
individual decrement to boundary zero.  Empty individual traces are handled
by the reused finite recursion. -/
theorem individualMixedBoundaryValue_zero_lower_of_terminal
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (trace : boundary.IndividualMixedFiniteAnalyticTraceData D representative
      offset radius Fsys x w₀ hw₀ data hA c)
    (hlast : HasInversePowerLowerBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c)
        (Fin.last (boundary.individualNumericSteps D representative offset
          radius Fsys x w₀ hw₀ data c).length))
      ((boundary.individualMixedNumericBoundaryCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c).boundaryValue
        (Fin.last (boundary.individualNumericSteps D representative offset
          radius Fsys x w₀ hw₀ data c).length))) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) 0)
      ((boundary.individualMixedNumericBoundaryCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c).boundaryValue 0) := by
  let compatibility := boundary.individualMixedNumericBoundaryCompatibility D
    representative offset radius Fsys x w₀ hw₀ data hA c
  apply compatibility.boundaryLower_zero_of_last D representative offset radius
    Fsys x w₀ hw₀ data boundary hA c
  · intro j' hafter
    let e := data.orderedClusterIndividualStepIndexEquiv c
      (boundary.preprocessed.fixedSteps c)
    let j : Fin (boundary.preprocessed.fixedSteps c).length := e.symm j'
    have hj : e j = j' := e.apply_symm_apply j'
    rw [← hj] at hafter ⊢
    exact boundary.individualMixedBeforeValue_lower_of_afterValue_lower D
      representative offset radius Fsys x w₀ hw₀ data separation hA c j
      (trace.coefficients j) (trace.step j) hafter
  · exact hlast

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
