import AbelFormalization.IndividualCentralIdealStep
import AbelFormalization.IndividualCentralIdealTraceData
import AbelFormalization.IndividualCentralRealJetIdentities
import AbelFormalization.IndividualCentralRealJetEvaluation
import AbelFormalization.OrderedClusterIndividualRealJetEvaluation
import AbelFormalization.IndividualClusterBalancingHierarchy
import AbelFormalization.AnalyticPolynomialEvaluationBounds
import AbelFormalization.RealHermiteJetIntegration
import AbelFormalization.RealQuantitativeTransferAssembly

/-!
# Quantitative transfer through one individual balancing decrement

This module is the one-step quantitative bridge for the individual central
operation.  The algebraic certificate and its displayed source/central
families come from `IndividualCentralIdealTraceData`; the two generator
identities come from `IndividualCentralRealJetIdentities`; and the analytic
scale hypotheses come from `IndividualClusterBalancingHierarchy`.

The main theorem evaluates the fixed polynomial matrices stored in
`DisplayedData.identities` directly and obtains their bounds from polynomial
evaluation.  An additional analytic-matrix variant records the alternative
interface in which those evaluations are represented by analytic functions
on one common finite-dimensional parameter neighborhood.  No algebraic
identity or asymptotic hierarchy is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v w

/-! ## Polynomial bounds for the retained coefficient ring -/

/-- A polynomial upper bound at one scale remains a polynomial upper bound
at an eventually larger scale. -/
theorem HasPolynomialUpperBound.mono_scale
    {X : Type*} {l : Filter X} {Rscale Xscale f : X → ℝ}
    (hR : ∀ᶠ x in l, 1 ≤ Rscale x)
    (hRX : ∀ᶠ x in l, Rscale x ≤ Xscale x)
    (hf : HasPolynomialUpperBound l Rscale f) :
    HasPolynomialUpperBound l Xscale f := by
  obtain ⟨C, hC, P, hf⟩ := hf
  refine ⟨C, hC, P, ?_⟩
  filter_upwards [hR, hRX, hf] with x hxR hxRX hxf
  exact hxf.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans hxR) hxRX P) hC.le)

/-- Rapid decay gives, in particular, a polynomial upper bound of exponent
zero. -/
theorem superpolynomialDecay_hasPolynomialUpperBound
    {X : Type*} {l : Filter X} {scale f : X → ℝ}
    (hf : Asymptotics.SuperpolynomialDecay l scale f) :
    HasPolynomialUpperBound l scale f := by
  apply HasPolynomialUpperBound.of_tendsto
  simpa using hf 0

/-- Evaluating a fixed polynomial in the unselected block variables is
polynomially bounded as soon as the ground coefficients and every retained
coordinate are polynomially bounded.  This is the reusable coefficient-ring
input needed by an individual central transfer. -/
theorem selectedBlockCoefficientEvaluationHom_hasPolynomialUpperBound
    {R : Type u} [CommRing R]
    {Block : Type v} [DecidableEq Block]
    (d : Block → ℕ) (selected : Block)
    (coefficientMap : R →+* (ℕ → ℝ))
    (flatValue : ClusterOperationSymbol Block d → ℕ → ℝ)
    (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop scale (coefficientMap r))
    (hretained : ∀ z : ClusterOperationSymbol (RemainingBlock selected)
        (remainingBlockDerivativeCount d selected),
      HasPolynomialUpperBound atTop scale
        (selectedBlockCoefficientAssignment d selected flatValue z)) :
    ∀ r : IndividualCentralCoefficientRing R d selected,
      HasPolynomialUpperBound atTop scale
        (selectedBlockCoefficientEvaluationHom coefficientMap d selected
          flatValue r) := by
  intro r
  exact mvPolynomial_eval₂Hom_hasPolynomialUpperBound
    hscale coefficientMap
      (selectedBlockCoefficientAssignment d selected flatValue)
      hcoefficient hretained r

/-- A convenient form of the preceding fixed-polynomial estimate when a
bound is known for every coordinate of the original flat assignment. -/
theorem selectedBlockCoefficientEvaluationHom_hasPolynomialUpperBound_of_flat
    {R : Type u} [CommRing R]
    {Block : Type v} [DecidableEq Block]
    (d : Block → ℕ) (selected : Block)
    (coefficientMap : R →+* (ℕ → ℝ))
    (flatValue : ClusterOperationSymbol Block d → ℕ → ℝ)
    (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop scale (coefficientMap r))
    (hflat : ∀ z,
      HasPolynomialUpperBound atTop scale (flatValue z)) :
    ∀ r : IndividualCentralCoefficientRing R d selected,
      HasPolynomialUpperBound atTop scale
        (selectedBlockCoefficientEvaluationHom coefficientMap d selected
          flatValue r) := by
  apply selectedBlockCoefficientEvaluationHom_hasPolynomialUpperBound
    d selected coefficientMap flatValue scale hscale hcoefficient
  intro z
  exact hflat _

/-- Analytic scalar coefficients along a convergent parameter sequence,
together with polynomially bounded retained coordinates, give the preceding
fixed-polynomial coefficient-ring bound. -/
theorem selectedBlockCoefficientEvaluationHom_hasPolynomialUpperBound_of_analytic
    {R : Type u} [CommRing R]
    {Block : Type v} [DecidableEq Block]
    {Param : Type w} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    (d : Block → ℕ) (selected : Block)
    (coefficientMap : R →+* (ℕ → ℝ))
    (coefficientRepresentative : R → Param → ℝ)
    (parameter : ℕ → Param) (x₀ : Param) (U : Set Param)
    (hx₀U : x₀ ∈ U)
    (hanalytic : ∀ r,
      AnalyticOnNhd ℝ (coefficientRepresentative r) U)
    (hparameter : Tendsto parameter atTop (𝓝 x₀))
    (hrepresentative : ∀ r n,
      coefficientMap r n = coefficientRepresentative r (parameter n))
    (flatValue : ClusterOperationSymbol Block d → ℕ → ℝ)
    (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hflat : ∀ z,
      HasPolynomialUpperBound atTop scale (flatValue z)) :
    ∀ r : IndividualCentralCoefficientRing R d selected,
      HasPolynomialUpperBound atTop scale
        (selectedBlockCoefficientEvaluationHom coefficientMap d selected
          flatValue r) := by
  apply selectedBlockCoefficientEvaluationHom_hasPolynomialUpperBound_of_flat
    d selected coefficientMap flatValue scale hscale
  · exact coefficientHom_hasPolynomialUpperBound_of_analyticRepresentatives
      coefficientMap coefficientRepresentative parameter x₀ U hx₀U
        hanalytic hparameter hrepresentative scale
  · exact hflat

/-! ## A displayed individual real-jet transfer -/

namespace IndividualCentralTransferData.DisplayedData

/-- A natural number bounds the finite family of least-weight norms attached
to the canonical certificate sources. -/
theorem exists_leastWeight_bound
    {R : Type u} [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : IndividualCentralTransferData.DisplayedData R transferData) :
    ∃ Pweight : ℕ, ∀ a,
      (∑ i, |(coefficientwiseLeastWeight
        (centralLaurentWeight
          (centralTransferShear
            (selectedBlockDerivativeCount d selected)))
        (transferData.certificate.source a) i : ℝ)|) ≤
          (Pweight : ℝ) := by
  classical
  let total : ℝ := ∑ a : Fin transferData.certificate.count,
    ∑ i, |(coefficientwiseLeastWeight
      (centralLaurentWeight
        (centralTransferShear
          (selectedBlockDerivativeCount d selected)))
      (transferData.certificate.source a) i : ℝ)|
  obtain ⟨Pweight, hPweight⟩ := exists_nat_ge total
  refine ⟨Pweight, fun a ↦ ?_⟩
  exact (Finset.single_le_sum
    (fun b _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ a)).trans hPweight

/-- Direct one-step propagation for the displayed generator families.

Both generator-change matrices are the evaluations of the fixed polynomial
matrices in `data.identities`.  Their uniform bounds are proved internally by
`mvPolynomial_eval₂Hom_hasPolynomialUpperBound`; no analytic representatives
of those matrix entries are introduced.  The two extra coordinate-bound
hypotheses are exactly what fixed-polynomial evaluation needs: central
coordinates at the post-step scale and literal source coordinates at the
pre-step scale. -/
theorem realJet_source_lower_of_central_lower_direct
    {R : Type u} [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : IndividualCentralTransferData.DisplayedData R transferData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientEval : IndividualCentralCoefficientRing R d selected →+*
      (ℕ → ℝ))
    (u : Fin 1 → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (selectedBlockDerivativeCount d selected i))
    (Rscale Xscale : ℕ → ℝ)
    (hierarchy : BalancedRealJetTransferHierarchy 0 u Rscale)
    (domination : CrossClusterTransferScaleDomination 0 u Rscale Xscale)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop Rscale (coefficientEval r))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u
          (selectedBlockDerivativeCount d selected) x))
    (hcentralValueBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (fun n ↦ realCentralTransferCentralValue A (fun i ↦ u i n)
          (selectedBlockDerivativeCount d selected) x))
    (hsourceValueBound : ∀ x,
      HasPolynomialUpperBound atTop Xscale
        (realJetActualAssignment u
          (selectedBlockDerivativeCount d selected) jets x))
    (hjetError : ∀ i (r : Fin (selectedBlockDerivativeCount d selected i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error r))
    (hcentralLower : HasInversePowerLowerBound atTop Rscale
      (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u
        (selectedBlockDerivativeCount d selected) n
        (data.central.generator b))) :
    HasInversePowerLowerBound atTop Xscale
      (fun k n ↦ realJetSourceEvaluationHom coefficientEval u
        (selectedBlockDerivativeCount d selected) jets n
        (data.source.generator k)) := by
  let d₁ := selectedBlockDerivativeCount d selected
  let certificate := transferData.certificate
  haveI : Nonempty (Fin certificate.count) := transferData.source_nonempty
  let centralCoefficient : Fin (data.central.count + 1) →
      Fin certificate.count → ℕ → ℝ :=
    fun b a n ↦ realJetCentralEvaluationHom A coefficientEval u d₁ n
      (data.identities.centralCoefficient b a)
  let sourceCoefficient : Fin certificate.count →
      Fin (data.source.count + 1) → ℕ → ℝ :=
    fun a k n ↦ realJetSourceEvaluationHom coefficientEval u d₁ jets n
      (data.identities.sourceCoefficient a k)
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchy.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hcoefficientX : ∀ r,
      HasPolynomialUpperBound atTop Xscale (coefficientEval r) := by
    intro r
    exact (hcoefficient r).mono_scale hRone domination.scale_le
  have hcentralCoefficientPointwise : ∀ b a,
      HasPolynomialUpperBound atTop Rscale (centralCoefficient b a) := by
    intro b a
    have h := mvPolynomial_eval₂Hom_hasPolynomialUpperBound
      hRone coefficientEval
      (fun x n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d₁ x)
      hcoefficient hcentralValueBound
      (data.identities.centralCoefficient b a)
    apply h.congr
    intro n
    exact (mvPolynomial_eval₂Hom_pi_apply coefficientEval
      (fun x n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d₁ x)
      (data.identities.centralCoefficient b a) n).symm
  have hsourceCoefficientPointwise : ∀ a k,
      HasPolynomialUpperBound atTop Xscale (sourceCoefficient a k) := by
    intro a k
    have h := mvPolynomial_eval₂Hom_hasPolynomialUpperBound
      (domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn)
      coefficientEval (realJetActualAssignment u d₁ jets)
      hcoefficientX hsourceValueBound
      (data.identities.sourceCoefficient a k)
    apply h.congr
    intro n
    exact (mvPolynomial_eval₂Hom_pi_apply coefficientEval
      (realJetActualAssignment u d₁ jets)
      (data.identities.sourceCoefficient a k) n).symm
  have hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient :=
    hasUniformPolynomialUpperBound_of_finite centralCoefficient hRone
      hcentralCoefficientPointwise
  have hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient :=
    hasUniformPolynomialUpperBound_of_finite sourceCoefficient
      (domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn)
      hsourceCoefficientPointwise
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
  have hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      realJetCentralEvaluationHom A coefficientEval u d₁ n
          (data.central.generator b) =
        ∑ a, centralCoefficient b a n *
          realJetCentralEvaluation A coefficientEval u d₁
            (certificate.source a) n := by
    apply Filter.Eventually.of_forall
    intro n b
    calc
      realJetCentralEvaluationHom A coefficientEval u d₁ n
          (data.central.generator b) =
          realJetCentralEvaluationHom A coefficientEval u d₁ n
            (∑ a, data.identities.centralCoefficient b a *
              centralPolynomialPhi
                (IndividualCentralCoefficientRing R d selected)
                (Fin 1) d₁ (Fin 1)
                (centralNormalizedInitialPolynomial
                  (centralTransferShear d₁) (certificate.source a))) :=
        congrArg (realJetCentralEvaluationHom A coefficientEval u d₁ n)
          (data.identities.central_identity b)
      _ = ∑ a, centralCoefficient b a n *
          realJetCentralEvaluation A coefficientEval u d₁
            (certificate.source a) n := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [map_mul]
        rfl
  have hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetSourceEvaluation coefficientEval u d₁ jets
          (certificate.source a) n =
        ∑ k, sourceCoefficient a k n *
          realJetSourceEvaluationHom coefficientEval u d₁ jets n
            (data.source.generator k) := by
    apply Filter.Eventually.of_forall
    intro n a
    calc
      realJetSourceEvaluation coefficientEval u d₁ jets
          (certificate.source a) n =
          realJetSourceEvaluationHom coefficientEval u d₁ jets n
            (certificate.source a) := rfl
      _ = realJetSourceEvaluationHom coefficientEval u d₁ jets n
          (∑ k, data.identities.sourceCoefficient a k *
            data.source.generator k) :=
        congrArg (realJetSourceEvaluationHom coefficientEval u d₁ jets n)
          (data.identities.source_identity a)
      _ = ∑ k, sourceCoefficient a k n *
          realJetSourceEvaluationHom coefficientEval u d₁ jets n
            (data.source.generator k) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_mul]
  exact certificate.realJet_quantitativeTransfer
    d₁ (individualCentralCurriedIdeal R d selected I) hA
    coefficientEval u hierarchy.positive jets Rscale Xscale
    (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u d₁ n
      (data.central.generator b))
    centralCoefficient
    (fun k n ↦ realJetSourceEvaluationHom coefficientEval u d₁ jets n
      (data.source.generator k))
    sourceCoefficient hierarchy.order hpos hierarchy.scale_ge_two
    hierarchy.adjacent_ratios hierarchy.smallest_div_log_scale
    domination.scale_le domination.target_ge_two domination.exponential_le
    Pweight hweight hcoefficient hmainBound hperturbedBound
    hcoordinateError hcentralIdentity hcentralCoefficient hcentralLower
    hsourceIdentity hsourceCoefficient

/-- Quantitative lower-bound propagation through one displayed individual
central step.

The generator families, their exact identities, and the certificate are the
fixed algebraic data in `data`.  The two hierarchy records contain precisely
the canonical scale hypotheses.  Coordinatewise jet-error decay is converted
to the global error assignment by `RealHermiteJetIntegration`.

The two `...Representation` equalities are the residual analytic seam: they
say that the evaluated fixed polynomial change-of-generators matrices are
realized by the displayed analytic representatives along `parameter`.
-/
theorem realJet_source_lower_of_central_lower
    {R : Type u} [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : IndividualCentralTransferData.DisplayedData R transferData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientEval : IndividualCentralCoefficientRing R d selected →+*
      (ℕ → ℝ))
    (u : Fin 1 → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (selectedBlockDerivativeCount d selected i))
    (Rscale Xscale : ℕ → ℝ)
    {Param : Type w} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    (parameter : ℕ → Param) (x₀ : Param) (U : Set Param)
    (hx₀U : x₀ ∈ U)
    (hparameter : Tendsto parameter atTop (𝓝 x₀))
    (centralCoefficient : Fin (data.central.count + 1) →
      Fin transferData.certificate.count → Param → ℝ)
    (sourceCoefficient : Fin transferData.certificate.count →
      Fin (data.source.count + 1) → Param → ℝ)
    (hcentralCoefficientAnalytic : ∀ b a,
      AnalyticOnNhd ℝ (centralCoefficient b a) U)
    (hsourceCoefficientAnalytic : ∀ a k,
      AnalyticOnNhd ℝ (sourceCoefficient a k) U)
    (hcentralCoefficientRepresentation : ∀ b a n,
      centralCoefficient b a (parameter n) =
        realJetCentralEvaluationHom A coefficientEval u
          (selectedBlockDerivativeCount d selected) n
          (data.identities.centralCoefficient b a))
    (hsourceCoefficientRepresentation : ∀ a k n,
      sourceCoefficient a k (parameter n) =
        realJetSourceEvaluationHom coefficientEval u
          (selectedBlockDerivativeCount d selected) jets n
          (data.identities.sourceCoefficient a k))
    (hierarchy : BalancedRealJetTransferHierarchy 0 u Rscale)
    (domination : CrossClusterTransferScaleDomination 0 u Rscale Xscale)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop Rscale (coefficientEval r))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u
          (selectedBlockDerivativeCount d selected) x))
    (hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u
          (selectedBlockDerivativeCount d selected) jets x))
    (hjetError : ∀ i (r : Fin (selectedBlockDerivativeCount d selected i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error r))
    (hcentralLower : HasInversePowerLowerBound atTop Rscale
      (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u
        (selectedBlockDerivativeCount d selected) n
        (data.central.generator b))) :
    HasInversePowerLowerBound atTop Xscale
      (fun k n ↦ realJetSourceEvaluationHom coefficientEval u
        (selectedBlockDerivativeCount d selected) jets n
        (data.source.generator k)) := by
  let d₁ := selectedBlockDerivativeCount d selected
  let certificate := transferData.certificate
  haveI : Nonempty (Fin certificate.count) := transferData.source_nonempty
  obtain ⟨Pweight, hweight⟩ := data.exists_leastWeight_bound
  have hpos : ∀ᶠ n in atTop, 0 < u (Fin.last 0) n :=
    Filter.Eventually.of_forall fun n ↦ hierarchy.positive n (Fin.last 0)
  have hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ realCentralTransferCoordinateError (jets n) x) :=
    realCentralTransferCoordinateError_superpolynomialDecay_of_errors
      jets hjetError
  have hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      realJetCentralEvaluationHom A coefficientEval u d₁ n
          (data.central.generator b) =
        ∑ a, centralCoefficient b a (parameter n) *
          realJetCentralEvaluation A coefficientEval u d₁
            (certificate.source a) n := by
    apply Filter.Eventually.of_forall
    intro n b
    calc
      realJetCentralEvaluationHom A coefficientEval u d₁ n
          (data.central.generator b) =
          realJetCentralEvaluationHom A coefficientEval u d₁ n
            (∑ a, data.identities.centralCoefficient b a *
              centralPolynomialPhi
                (IndividualCentralCoefficientRing R d selected)
                (Fin 1) d₁ (Fin 1)
                (centralNormalizedInitialPolynomial
                  (centralTransferShear d₁) (certificate.source a))) :=
        congrArg (realJetCentralEvaluationHom A coefficientEval u d₁ n)
          (data.identities.central_identity b)
      _ = ∑ a, centralCoefficient b a (parameter n) *
          realJetCentralEvaluation A coefficientEval u d₁
            (certificate.source a) n := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [map_mul, hcentralCoefficientRepresentation]
        rfl
  have hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetSourceEvaluation coefficientEval u d₁ jets
          (certificate.source a) n =
        ∑ k, sourceCoefficient a k (parameter n) *
          realJetSourceEvaluationHom coefficientEval u d₁ jets n
            (data.source.generator k) := by
    apply Filter.Eventually.of_forall
    intro n a
    calc
      realJetSourceEvaluation coefficientEval u d₁ jets
          (certificate.source a) n =
          realJetSourceEvaluationHom coefficientEval u d₁ jets n
            (certificate.source a) := rfl
      _ = realJetSourceEvaluationHom coefficientEval u d₁ jets n
          (∑ k, data.identities.sourceCoefficient a k *
            data.source.generator k) :=
        congrArg (realJetSourceEvaluationHom coefficientEval u d₁ jets n)
          (data.identities.source_identity a)
      _ = ∑ k, sourceCoefficient a k (parameter n) *
          realJetSourceEvaluationHom coefficientEval u d₁ jets n
            (data.source.generator k) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_mul, hsourceCoefficientRepresentation]
  exact certificate.realJet_quantitativeTransfer_of_analyticMatrices
    d₁ (individualCentralCurriedIdeal R d selected I) hA
    coefficientEval u hierarchy.positive jets Rscale Xscale
    parameter x₀ U hx₀U hparameter
    (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u d₁ n
      (data.central.generator b))
    centralCoefficient
    (fun k n ↦ realJetSourceEvaluationHom coefficientEval u d₁ jets n
      (data.source.generator k))
    sourceCoefficient hcentralCoefficientAnalytic hsourceCoefficientAnalytic
    hierarchy.order hpos hierarchy.scale_ge_two hierarchy.adjacent_ratios
    hierarchy.smallest_div_log_scale domination.scale_le
    domination.target_ge_two domination.exponential_le Pweight hweight
    hcoefficient hmainBound hperturbedBound hcoordinateError
    hcentralIdentity hcentralLower hsourceIdentity

end IndividualCentralTransferData.DisplayedData

/-! ## Canonical ordered-cluster specialization -/

namespace RepresentativeClusterSubsequence

/-- The singleton derivative-count function used by the quantitative
certificate at source-indexed balancing step `j`. -/
abbrev orderedClusterQuantitativeStepDerivativeCount
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) : Fin 1 → ℕ :=
  selectedBlockDerivativeCount
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterIndividualSelectedBlock c fixedSteps j)

namespace OrderedClusterIndividualDisplayedTraceData

variable (R : Type u) [CommRing R]
variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable (data : RepresentativeClusterSubsequence time)
variable (higher : ℕ) (c : Fin data.orderedClusterCount)

noncomputable local instance orderedClusterQuantitativeBlockDecidableEq :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Quantitative propagation for one actual ordered-cluster balancing step,
stated on the displayed polynomials in the full prefix ring.  The post- and
pre-step scales are the canonical full-tuple prefix maxima.  The exact
real-jet evaluations are supplied by the ordered-cluster evaluation bridge,
and all hierarchy fields follow from the fixed balancing plans and the
within-cluster separation estimate. -/
theorem beforeGenerator_lower_of_afterGenerator_lower
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    (j : Fin fixedSteps.length)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientMap : R →+* (ℕ → ℝ))
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
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime (φ q) c)
        fixedSteps j i n)
      (data.orderedClusterQuantitativeStepDerivativeCount
        higher c fixedSteps j i))
    (hcoefficientMap : ∀ r,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (coefficientMap r))
    (hbaseValue : ∀ z,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (baseValue z))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (realJetMainAssignment A
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) x))
    (hcentralValueBound : ∀ x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (fun n ↦ realCentralTransferCentralValue A
          (fun i ↦ data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j i n)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) x))
    (hsourceValueBound : ∀ x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.castSucc)
        (realJetActualAssignment
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) jets x))
    (hjetError : ∀ i
      (r : Fin (data.orderedClusterQuantitativeStepDerivativeCount
        higher c fixedSteps j i)),
      Asymptotics.SuperpolynomialDecay atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (fun n ↦ (jets n i).error r))
    (hcentralLower : HasInversePowerLowerBound atTop
      (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
      (fun b n ↦ MvPolynomial.eval₂Hom coefficientMap
        (data.orderedClusterIndividualPostLogFlatAssignment higher c A
          (fun q ↦ data.orderedClusterRawTime (φ q) c)
          fixedSteps j baseValue)
        (IndividualCentralTransferData.DisplayedData.afterGenerator R
          (displayed.displayed
            (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)) b) n)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.castSucc)
      (fun k n ↦ MvPolynomial.eval₂Hom coefficientMap
        (data.orderedClusterIndividualPreLogFlatAssignment higher c
          (fun q ↦ data.orderedClusterRawTime (φ q) c)
          fixedSteps j baseValue jets)
        (IndividualCentralTransferData.DisplayedData.beforeGenerator R
          (displayed.displayed
            (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)) k) n) := by
  let rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ :=
    fun q ↦ data.orderedClusterRawTime (φ q) c
  let dflat := data.orderedClusterPrefixConstantDerivativeCount
    (higher + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c fixedSteps j
  let d₁ := data.orderedClusterQuantitativeStepDerivativeCount
    higher c fixedSteps j
  let u := data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j
  let Rscale := data.orderedClusterBalancingPrefixScale
    A φ c fixedSteps j.succ
  let Xscale := data.orderedClusterBalancingPrefixScale
    A φ c fixedSteps j.castSucc
  let coefficientEval := data.orderedClusterIndividualCoefficientEvaluationHom
    higher c R coefficientMap fixedSteps j baseValue
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
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchy.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop Rscale (coefficientEval r) := by
    have h :=
      selectedBlockCoefficientEvaluationHom_hasPolynomialUpperBound_of_flat
        dflat selected coefficientMap baseValue Rscale hRone
        hcoefficientMap hbaseValue
    simpa only [coefficientEval,
      orderedClusterIndividualCoefficientEvaluationHom, dflat, selected]
      using h
  have hcentralLowerRealJet : HasInversePowerLowerBound atTop Rscale
      (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u d₁ n
        (step.central.generator b)) := by
    apply hasInversePowerLowerBound_of_eventuallyEq
      (Filter.Eventually.of_forall fun n b ↦ ?_) hcentralLower
    simpa only [rawTime, Rscale, coefficientEval, u, d₁, step] using
      displayed.eval_afterGenerator_postLog R data higher c j A
        coefficientMap rawTime baseValue b n
  have hsourceLowerRealJet : HasInversePowerLowerBound atTop Xscale
      (fun k n ↦ realJetSourceEvaluationHom coefficientEval u d₁ jets n
        (step.source.generator k)) :=
    step.realJet_source_lower_of_central_lower_direct hA
    coefficientEval u jets Rscale Xscale hierarchy domination
    hcoefficient hmainBound hcentralValueBound hsourceValueBound
      hjetError hcentralLowerRealJet
  apply hasInversePowerLowerBound_of_eventuallyEq
    (Filter.Eventually.of_forall fun n k ↦ ?_) hsourceLowerRealJet
  simpa only [rawTime, Xscale, coefficientEval, u, d₁, step] using
    (displayed.eval_beforeGenerator_preLog R data higher c j
      coefficientMap rawTime baseValue jets k n).symm

end OrderedClusterIndividualDisplayedTraceData
end RepresentativeClusterSubsequence

end AbelFormalization
