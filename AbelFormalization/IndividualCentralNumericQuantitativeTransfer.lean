import AbelFormalization.IndividualCentralQuantitativeTransfer

/-!
# Numeric quantitative transfer through individual central steps

The ring-homomorphic individual transfer evaluates every coefficient in the
retained coefficient ring.  A single displayed step only uses the finitely
many coefficients in its canonical source polynomials and its two finite
change-of-generators matrices.  This module exposes those values directly and
uses the existing coefficientwise quantitative theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v w

namespace IndividualCentralTransferData.DisplayedData

/-- One-step individual central transfer using only finitely many numeric
coefficient values and the two eventual displayed representation identities.

`hcentralIdentity` and `hsourceIdentity` are the exact evaluation seams.  No
map from `R`, the retained coefficient ring, or either polynomial ring to
real sequences is assumed. -/
theorem realJet_source_lower_of_central_lower_numeric
    {R : Type u} [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : IndividualCentralTransferData.DisplayedData R transferData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientValue : Fin transferData.certificate.count →
      (RealJetTransferIndex 0
        (selectedBlockDerivativeCount d selected) →₀ ℕ) → ℕ → ℝ)
    (u : Fin 1 → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (selectedBlockDerivativeCount d selected i))
    (Rscale Xscale : ℕ → ℝ)
    (hierarchy : BalancedRealJetTransferHierarchy 0 u Rscale)
    (domination : CrossClusterTransferScaleDomination 0 u Rscale Xscale)
    (centralValue : Fin (data.central.count + 1) → ℕ → ℝ)
    (centralCoefficientValue : Fin (data.central.count + 1) →
      Fin transferData.certificate.count → ℕ → ℝ)
    (sourceValue : Fin (data.source.count + 1) → ℕ → ℝ)
    (sourceCoefficientValue : Fin transferData.certificate.count →
      Fin (data.source.count + 1) → ℕ → ℝ)
    (hcoefficient : ∀ a e,
      e ∈ (transferData.certificate.source a).support →
        HasPolynomialUpperBound atTop Rscale (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u
          (selectedBlockDerivativeCount d selected) x))
    (hjetError : ∀ i
      (r : Fin (selectedBlockDerivativeCount d selected i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error r))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralValue b n =
        ∑ a, centralCoefficientValue b a n *
          realJetCoefficientwiseCentralEvaluation A
            (selectedBlockDerivativeCount d selected)
            (coefficientValue a) u
            (transferData.certificate.source a) n)
    (hcentralCoefficient : ∀ b a,
      HasPolynomialUpperBound atTop Rscale
        (centralCoefficientValue b a))
    (hcentralLower : HasInversePowerLowerBound atTop Rscale centralValue)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetCoefficientwiseSourceEvaluation
          (selectedBlockDerivativeCount d selected)
          (coefficientValue a) u jets
          (transferData.certificate.source a) n =
        ∑ k, sourceCoefficientValue a k n * sourceValue k n)
    (hsourceCoefficient : ∀ a k,
      HasPolynomialUpperBound atTop Xscale
        (sourceCoefficientValue a k)) :
    HasInversePowerLowerBound atTop Xscale sourceValue := by
  let d₁ := selectedBlockDerivativeCount d selected
  let certificate := transferData.certificate
  haveI : Nonempty (Fin certificate.count) := transferData.source_nonempty
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchy.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hXone : ∀ᶠ n in atTop, 1 ≤ Xscale n :=
    domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hcentralCoefficientUniform :
      HasUniformPolynomialUpperBound atTop Rscale
        centralCoefficientValue :=
    hasUniformPolynomialUpperBound_of_finite centralCoefficientValue hRone
      hcentralCoefficient
  have hsourceCoefficientUniform :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficientValue :=
    hasUniformPolynomialUpperBound_of_finite sourceCoefficientValue hXone
      hsourceCoefficient
  obtain ⟨Pweight, hweight⟩ := data.exists_leastWeight_bound
  have hpos : ∀ᶠ n in atTop, 0 < u (Fin.last 0) n :=
    Filter.Eventually.of_forall fun n ↦ hierarchy.positive n (Fin.last 0)
  have hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ realCentralTransferCoordinateError (jets n) x) :=
    realCentralTransferCoordinateError_superpolynomialDecay_of_errors
      jets hjetError
  have hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d₁ jets x) := by
    intro x
    apply ((hmainBound x).add hRone
      (superpolynomialDecay_hasPolynomialUpperBound
        (hcoordinateError x))).congr
    intro n
    rfl
  exact certificate.realJet_quantitativeTransfer_coefficientwise
    d₁ (individualCentralCurriedIdeal R d selected I) hA coefficientValue
    u hierarchy.positive jets Rscale Xscale centralValue
    centralCoefficientValue sourceValue sourceCoefficientValue
    hierarchy.order hpos hierarchy.scale_ge_two hierarchy.adjacent_ratios
    hierarchy.smallest_div_log_scale domination.scale_le
    domination.target_ge_two domination.exponential_le Pweight hweight
    hcoefficient hmainBound hperturbedBound hcoordinateError
    hcentralIdentity hcentralCoefficientUniform hcentralLower
    hsourceIdentity hsourceCoefficientUniform

end IndividualCentralTransferData.DisplayedData

namespace IndividualCentralDisplayedTraceData

variable (R : Type u) [CommRing R]
variable {Block : Type v} [Fintype Block] [DecidableEq Block]

/-- Finite reverse recursion for numeric individual-step values.  Each
boundary may use its own nonempty finite family.  The two matrices at a step
identify the successor boundary with the displayed after-family and the
displayed before-family with the predecessor boundary.

This is the coefficientwise replacement for the span-based recursion in
`boundaryLower_zero_of_last`.  Its only additional seams are the two eventual
numeric change-of-family identities at each internal boundary. -/
theorem boundaryLower_zero_of_last_numeric
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {traceData : IndividualCentralIdealTraceData R d steps I}
    (displayed : IndividualCentralDisplayedTraceData R d steps I traceData)
    {X : Type w} (l : Filter X)
    (scale : Fin (steps.length + 1) → X → ℝ)
    (boundaryCount : Fin (steps.length + 1) → ℕ)
    (boundaryValue : (q : Fin (steps.length + 1)) →
      Fin (boundaryCount q + 1) → X → ℝ)
    (afterValue : (j : Fin steps.length) →
      Fin ((displayed.displayed j).central.count + 1) → X → ℝ)
    (beforeValue : (j : Fin steps.length) →
      Fin ((displayed.displayed j).source.count + 1) → X → ℝ)
    (afterBoundaryCoefficient : (j : Fin steps.length) →
      Fin (boundaryCount j.succ + 1) →
        Fin ((displayed.displayed j).central.count + 1) → X → ℝ)
    (beforeBoundaryCoefficient : (j : Fin steps.length) →
      Fin ((displayed.displayed j).source.count + 1) →
        Fin (boundaryCount j.castSucc + 1) → X → ℝ)
    (hscale : ∀ q, ∀ᶠ x in l, 1 ≤ scale q x)
    (hafterBoundaryCoefficient : ∀ j b a,
      HasPolynomialUpperBound l (scale j.succ)
        (afterBoundaryCoefficient j b a))
    (hbeforeBoundaryCoefficient : ∀ j k b,
      HasPolynomialUpperBound l (scale j.castSucc)
        (beforeBoundaryCoefficient j k b))
    (hafterBoundaryIdentity : ∀ j, ∀ᶠ x in l, ∀ b,
      boundaryValue j.succ b x =
        ∑ a, afterBoundaryCoefficient j b a x * afterValue j a x)
    (hbeforeBoundaryIdentity : ∀ j, ∀ᶠ x in l, ∀ k,
      beforeValue j k x =
        ∑ b, beforeBoundaryCoefficient j k b x *
          boundaryValue j.castSucc b x)
    (hstep : ∀ j,
      HasInversePowerLowerBound l (scale j.succ) (afterValue j) →
        HasInversePowerLowerBound l (scale j.castSucc) (beforeValue j))
    (hlast : HasInversePowerLowerBound l (scale (Fin.last steps.length))
      (boundaryValue (Fin.last steps.length))) :
    HasInversePowerLowerBound l (scale 0) (boundaryValue 0) := by
  let motive := fun (k : ℕ) (hk : k ≤ steps.length) ↦
    HasInversePowerLowerBound l
      (scale ⟨k, Nat.lt_succ_iff.mpr hk⟩)
      (boundaryValue ⟨k, Nat.lt_succ_iff.mpr hk⟩)
  have htop : motive steps.length le_rfl := by
    change HasInversePowerLowerBound l
      (scale ⟨steps.length, Nat.lt_succ_self _⟩)
      (boundaryValue ⟨steps.length, Nat.lt_succ_self _⟩)
    have hindex :
        (⟨steps.length, Nat.lt_succ_self _⟩ : Fin (steps.length + 1)) =
          Fin.last steps.length := Fin.ext rfl
    rw [hindex]
    exact hlast
  have hdescent : motive 0 (Nat.zero_le _) :=
    Nat.decreasingInduction (n := steps.length) (motive := motive)
      (fun k hk ih ↦ by
        let j : Fin steps.length := ⟨k, hk⟩
        have hafter : HasInversePowerLowerBound l (scale j.succ)
            (afterValue j) := by
          apply hasInversePowerLowerBound_of_linearCombinations
            (afterValue j) (boundaryValue j.succ)
              (afterBoundaryCoefficient j) (hscale j.succ)
          · exact hafterBoundaryIdentity j
          · exact hasUniformPolynomialUpperBound_of_finite
              (afterBoundaryCoefficient j) (hscale j.succ)
              (hafterBoundaryCoefficient j)
          · exact ih
        have hbefore : HasInversePowerLowerBound l (scale j.castSucc)
            (beforeValue j) := hstep j hafter
        apply hasInversePowerLowerBound_of_linearCombinations
          (boundaryValue j.castSucc) (beforeValue j)
            (beforeBoundaryCoefficient j) (hscale j.castSucc)
        · exact hbeforeBoundaryIdentity j
        · exact hasUniformPolynomialUpperBound_of_finite
            (beforeBoundaryCoefficient j) (hscale j.castSucc)
            (hbeforeBoundaryCoefficient j)
        · exact hbefore)
      htop (Nat.zero_le _)
  exact hdescent

end IndividualCentralDisplayedTraceData

namespace RepresentativeClusterSubsequence

namespace OrderedClusterIndividualDisplayedTraceData

variable (R : Type u) [CommRing R]
variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable (data : RepresentativeClusterSubsequence time)
variable (higher : ℕ) (c : Fin data.orderedClusterCount)

noncomputable local instance orderedClusterNumericBlockDecidableEq :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Numeric/coefficientwise analog of
`beforeGenerator_lower_of_afterGenerator_lower` for one actual balancing
step.  The displayed before and after values, finite source coefficients,
and two generator-change matrices are supplied directly. -/
theorem beforeGenerator_lower_of_afterGenerator_lower_numeric
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    (j : Fin fixedSteps.length)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (φ : ℕ → ℕ)
    (plans : ∀ n, ClusterBalancingPlan
      (data.orderedClusterRawTime (φ n) c)
      (data.orderedClusterMinTime c (φ n)))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : 5 ≤ N)
    (hbaseTop : Tendsto
      (fun n ↦ data.orderedClusterMinTime c (φ n)) atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (data.orderedClusterTailSize c + 1), i ≠ k →
        separationConstant /
            inverse A (data.orderedClusterMinTime c (φ n) - N) ≤
          integerDistance
            (data.orderedClusterRawTime (φ n) c i -
              data.orderedClusterRawTime (φ n) c k))
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime (φ q) c)
        fixedSteps j i n)
      (data.orderedClusterQuantitativeStepDerivativeCount
        higher c fixedSteps j i))
    (coefficientValue :
      Fin (traceData.transferData
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).certificate.count →
      (RealJetTransferIndex 0
        (data.orderedClusterQuantitativeStepDerivativeCount
          higher c fixedSteps j) →₀ ℕ) → ℕ → ℝ)
    (afterValue : Fin
      ((displayed.displayed
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).central.count + 1) →
      ℕ → ℝ)
    (centralCoefficientValue : Fin
      ((displayed.displayed
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).central.count + 1) →
      Fin (traceData.transferData
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).certificate.count →
      ℕ → ℝ)
    (beforeValue : Fin
      ((displayed.displayed
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).source.count + 1) →
      ℕ → ℝ)
    (sourceCoefficientValue :
      Fin (traceData.transferData
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).certificate.count →
      Fin ((displayed.displayed
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).source.count + 1) →
      ℕ → ℝ)
    (hcoefficient : ∀ a e,
      e ∈ ((traceData.transferData
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).certificate.source a).support →
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (realJetMainAssignment A
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) x))
    (hjetError : ∀ i
      (r : Fin (data.orderedClusterQuantitativeStepDerivativeCount
        higher c fixedSteps j i)),
      Asymptotics.SuperpolynomialDecay atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (fun n ↦ (jets n i).error r))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      afterValue b n =
        ∑ a, centralCoefficientValue b a n *
          realJetCoefficientwiseCentralEvaluation A
            (data.orderedClusterQuantitativeStepDerivativeCount
              higher c fixedSteps j)
            (coefficientValue a)
            (data.orderedClusterIndividualPostLogScale c A
              (fun q ↦ data.orderedClusterRawTime (φ q) c)
              fixedSteps j)
            ((traceData.transferData
              (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).certificate.source a) n)
    (hcentralCoefficient : ∀ b a,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (centralCoefficientValue b a))
    (hcentralLower : HasInversePowerLowerBound atTop
      (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
      afterValue)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetCoefficientwiseSourceEvaluation
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j)
          (coefficientValue a)
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j) jets
          ((traceData.transferData
            (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).certificate.source a) n =
        ∑ k, sourceCoefficientValue a k n * beforeValue k n)
    (hsourceCoefficient : ∀ a k,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.castSucc)
        (sourceCoefficientValue a k)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.castSucc)
      beforeValue := by
  let rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ :=
    fun q ↦ data.orderedClusterRawTime (φ q) c
  let u := data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j
  let Rscale := data.orderedClusterBalancingPrefixScale
    A φ c fixedSteps j.succ
  let Xscale := data.orderedClusterBalancingPrefixScale
    A φ c fixedSteps j.castSucc
  let step := displayed.displayed
    (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)
  obtain ⟨hierarchy₀, domination₀⟩ :=
    hA.orderedClusterBalancingStep_transferHierarchies data φ c
      fixedSteps plans hfixedSteps j hseparationConstant hN
      hbaseTop hseparated
  have hierarchy : BalancedRealJetTransferHierarchy 0 u Rscale := by
    change BalancedRealJetTransferHierarchy 0
      (fun _ n ↦ clusterBalancingStepValue A rawTime fixedSteps j n)
      Rscale
    simpa only [rawTime, Rscale, orderedClusterBalancingPrefixScale,
      orderedClusterBalancingStepValue]
      using hierarchy₀
  have domination : CrossClusterTransferScaleDomination
      0 u Rscale Xscale := by
    change CrossClusterTransferScaleDomination 0
      (fun _ n ↦ clusterBalancingStepValue A rawTime fixedSteps j n)
      Rscale Xscale
    simpa only [rawTime, Rscale, Xscale,
      orderedClusterBalancingPrefixScale,
      orderedClusterBalancingStepValue] using domination₀
  apply step.realJet_source_lower_of_central_lower_numeric hA
    coefficientValue u jets Rscale Xscale hierarchy domination afterValue
    centralCoefficientValue beforeValue sourceCoefficientValue
  · simpa only [step] using hcoefficient
  · exact hmainBound
  · exact hjetError
  · simpa only [rawTime, u, step,
      orderedClusterQuantitativeStepDerivativeCount,
      orderedClusterIndividualSelectedBlock] using hcentralIdentity
  · exact hcentralCoefficient
  · exact hcentralLower
  · simpa only [rawTime, u, step,
      orderedClusterQuantitativeStepDerivativeCount,
      orderedClusterIndividualSelectedBlock] using hsourceIdentity
  · exact hsourceCoefficient

end OrderedClusterIndividualDisplayedTraceData
end RepresentativeClusterSubsequence
end AbelFormalization
