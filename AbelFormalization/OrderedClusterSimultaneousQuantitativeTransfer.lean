import AbelFormalization.OrderedClusterSimultaneousRealJetEvaluation
import AbelFormalization.IndividualCentralQuantitativeTransfer
import AbelFormalization.FiniteGeneratorSpanLowerBound
import AbelFormalization.OrderedClusterIndividualQuantitativeTrace

/-!
# Quantitative transfer through ordered-cluster simultaneous operations

This module supplies the quantitative companion to
`OrderedClusterSimultaneousRealJetEvaluation`.  The first theorem applies to
any displayed full central step whose nonempty block cardinality is written
as a successor.  It evaluates the two fixed polynomial coefficient matrices
stored in the displayed algebraic data and proves their uniform polynomial
bounds internally.

The ordered-cluster specialization then uses the fixed balancing plan and its
final order to construct the canonical hierarchy at every simultaneous
operation.  Its source and central families are the literal before/after
generators from the evaluation module, so no extra algebraic or evaluation
identity is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

/-- Error-free normalized central coordinates with a literal `Fin h` block
type. -/
def finiteRealJetMainAssignment
    {h : ℕ} (A : ℝ → ℝ) (u : Fin h → ℕ → ℝ)
    (d : Fin h → ℕ) :
    ClusterOperationSymbol (Fin h) d → ℕ → ℝ :=
  fun x n ↦ realCentralTransferMainValue A (fun i ↦ u i n) d x

/-- Literal source coordinates with a native finite block cardinality. -/
def finiteRealJetActualAssignment
    {h : ℕ} {A : ℝ → ℝ} (u : Fin h → ℕ → ℝ)
    (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    ClusterOperationSymbol (Fin h) d → ℕ → ℝ :=
  fun x n ↦ realCentralTransferActualValue A (fun i ↦ u i n) d
    (jets n) x

/-- Polynomial bounds for the literal source coordinates imply the bounds
needed for the un-translated pre-log coordinates.  The only difference is
that a fresh representative coordinate is `E u = exp u - 1`; all retained
coordinates agree literally. -/
theorem simultaneousCentralPreLogActiveAssignment_hasPolynomialUpperBound
    {h : ℕ} {A : ℝ → ℝ} (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    {scale : ℕ → ℝ} (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hactual : ∀ x, HasPolynomialUpperBound atTop scale
      (finiteRealJetActualAssignment u d jets x)) :
    ∀ x, HasPolynomialUpperBound atTop scale
      (simultaneousCentralPreLogActiveAssignment u d jets x) := by
  intro x
  rcases x with i | x
  · apply ((hactual (Sum.inl i)).sub hscale
      (HasPolynomialUpperBound.one atTop scale)).congr
    intro n
    simp [finiteRealJetActualAssignment,
      simultaneousCentralPreLogActiveAssignment,
      realCentralTransferActualValue, E]
  · apply (hactual (Sum.inr x)).congr
    intro n
    rfl

/-- The maintained real-jet hierarchy API uses a successor presentation of
the block cardinality.  This record packages only that cardinality transport
together with the existing hierarchy and domination structures. -/
def FiniteRealJetTransferHierarchies
    (h : ℕ) (u : Fin h → ℕ → ℝ)
    (Rscale Xscale : ℕ → ℝ) : Prop :=
  ∃ tail : ℕ, ∃ card_eq : tail + 1 = h,
    BalancedRealJetTransferHierarchy tail
        (fun i n ↦ u (finCongr card_eq i) n) Rscale ∧
      CrossClusterTransferScaleDomination tail
        (fun i n ↦ u (finCongr card_eq i) n) Rscale Xscale

theorem FiniteRealJetTransferHierarchies.scale_ge_two
    {h : ℕ} {u : Fin h → ℕ → ℝ} {Rscale Xscale : ℕ → ℝ}
    (hierarchies : FiniteRealJetTransferHierarchies
      h u Rscale Xscale) :
    ∀ᶠ n in atTop, 2 ≤ Rscale n := by
  rcases hierarchies with ⟨_, _, hierarchy, _⟩
  exact hierarchy.scale_ge_two

namespace ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

/-- A single natural number bounds all least-weight norms of the finite
canonical source family belonging to a displayed full central step. -/
theorem exists_leastWeight_bound
    {R : Type u} [CommRing R]
    {m : ℕ} {higher : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin (m + 1))
        (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate
      R (m + 1) higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r) :
    ∃ Pweight : ℕ, ∀ a,
      (∑ i, |(coefficientwiseLeastWeight
        (centralLaurentWeight
          (centralTransferShear (terminalTotalDerivativeCount higher)))
        ((transferData.transferCertificate r).source a) i : ℝ)|) ≤
          (Pweight : ℝ) := by
  classical
  let transferCertificate := transferData.transferCertificate r
  let total : ℝ := ∑ a : Fin transferCertificate.count,
    ∑ i, |(coefficientwiseLeastWeight
      (centralLaurentWeight
        (centralTransferShear (terminalTotalDerivativeCount higher)))
      (transferCertificate.source a) i : ℝ)|
  obtain ⟨Pweight, hPweight⟩ := exists_nat_ge total
  refine ⟨Pweight, fun a ↦ ?_⟩
  exact (Finset.single_le_sum
    (fun b _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ a)).trans hPweight

/-- Direct quantitative propagation through one displayed simultaneous
central step.

Both change-of-generators matrices are fixed polynomial matrices from
`data.identities`.  Their evaluated matrix bounds, the finite certificate
weight bound, and the two exact algebraic identities are derived inside the
proof.  The remaining assumptions are precisely the scale hierarchy,
coefficient/coordinate polynomial bounds, coordinate-error decay, and the
lower bound on the displayed central family. -/
theorem realJet_source_lower_of_central_lower_direct_successor
    {R : Type u} [CommRing R]
    {m : ℕ} {higher : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin (m + 1))
        (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate
      R (m + 1) higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (terminalTotalDerivativeCount higher i))
    (Rscale Xscale : ℕ → ℝ)
    (hierarchy : BalancedRealJetTransferHierarchy m u Rscale)
    (domination : CrossClusterTransferScaleDomination
      m u Rscale Xscale)
    (hcoefficient : ∀ q,
      HasPolynomialUpperBound atTop Rscale (coefficientEval q))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u
          (terminalTotalDerivativeCount higher) x))
    (hcentralValueBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (fun n ↦ realCentralTransferCentralValue A (fun i ↦ u i n)
          (terminalTotalDerivativeCount higher) x))
    (hsourceValueBound : ∀ x,
      HasPolynomialUpperBound atTop Xscale
        (realJetActualAssignment u (terminalTotalDerivativeCount higher)
          jets x))
    (hjetError : ∀ i
      (q : Fin (terminalTotalDerivativeCount higher i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error q))
    (hcentralLower : HasInversePowerLowerBound atTop Rscale
      (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount higher) n
        (data.central.generator b))) :
    HasInversePowerLowerBound atTop Xscale
      (fun k n ↦ realJetSourceEvaluationHom coefficientEval u
        (terminalTotalDerivativeCount higher) jets n
        (data.source.generator k)) := by
  let d := terminalTotalDerivativeCount higher
  let transferCertificate := transferData.transferCertificate r
  haveI : Nonempty (Fin transferCertificate.count) :=
    transferData.source_nonempty r
  let centralCoefficient : Fin (data.central.count + 1) →
      Fin transferCertificate.count → ℕ → ℝ :=
    fun b a n ↦ realJetCentralEvaluationHom A coefficientEval u d n
      (data.identities.centralCoefficient b a)
  let sourceCoefficient : Fin transferCertificate.count →
      Fin (data.source.count + 1) → ℕ → ℝ :=
    fun a k n ↦ realJetSourceEvaluationHom coefficientEval u d jets n
      (data.identities.sourceCoefficient a k)
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchy.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hcoefficientX : ∀ q,
      HasPolynomialUpperBound atTop Xscale (coefficientEval q) := by
    intro q
    exact (hcoefficient q).mono_scale hRone domination.scale_le
  have hcentralCoefficientPointwise : ∀ b a,
      HasPolynomialUpperBound atTop Rscale
        (centralCoefficient b a) := by
    intro b a
    have h := mvPolynomial_eval₂Hom_hasPolynomialUpperBound
      hRone coefficientEval
      (fun x n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d x)
      hcoefficient hcentralValueBound
      (data.identities.centralCoefficient b a)
    apply h.congr
    intro n
    exact (mvPolynomial_eval₂Hom_pi_apply coefficientEval
      (fun x n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d x)
      (data.identities.centralCoefficient b a) n).symm
  have hsourceCoefficientPointwise : ∀ a k,
      HasPolynomialUpperBound atTop Xscale
        (sourceCoefficient a k) := by
    intro a k
    have h := mvPolynomial_eval₂Hom_hasPolynomialUpperBound
      (domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn)
      coefficientEval (realJetActualAssignment u d jets)
      hcoefficientX hsourceValueBound
      (data.identities.sourceCoefficient a k)
    apply h.congr
    intro n
    exact (mvPolynomial_eval₂Hom_pi_apply coefficientEval
      (realJetActualAssignment u d jets)
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
  have hpos : ∀ᶠ n in atTop, 0 < u (Fin.last m) n :=
    Filter.Eventually.of_forall fun n ↦ hierarchy.positive n (Fin.last m)
  have hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ realCentralTransferCoordinateError (jets n) x) :=
    realCentralTransferCoordinateError_superpolynomialDecay_of_errors
      jets hjetError
  have hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d jets x) := by
    intro x
    apply ((hmainBound x).add hRone
      (superpolynomialDecay_hasPolynomialUpperBound
        (hcoordinateError x))).congr
    intro n
    rfl
  have hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      realJetCentralEvaluationHom A coefficientEval u d n
          (data.central.generator b) =
        ∑ a, centralCoefficient b a n *
          realJetCentralEvaluation A coefficientEval u d
            (transferCertificate.source a) n := by
    apply Filter.Eventually.of_forall
    intro n b
    calc
      realJetCentralEvaluationHom A coefficientEval u d n
          (data.central.generator b) =
          realJetCentralEvaluationHom A coefficientEval u d n
            (∑ a, data.identities.centralCoefficient b a *
              centralPolynomialPhi R (Fin (m + 1)) d (Fin (m + 1))
                (centralNormalizedInitialPolynomial
                  (centralTransferShear d)
                  (transferCertificate.source a))) :=
        congrArg (realJetCentralEvaluationHom A coefficientEval u d n)
          (data.identities.central_identity b)
      _ = ∑ a, centralCoefficient b a n *
          realJetCentralEvaluation A coefficientEval u d
            (transferCertificate.source a) n := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [map_mul]
        rfl
  have hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetSourceEvaluation coefficientEval u d jets
          (transferCertificate.source a) n =
        ∑ k, sourceCoefficient a k n *
          realJetSourceEvaluationHom coefficientEval u d jets n
            (data.source.generator k) := by
    apply Filter.Eventually.of_forall
    intro n a
    calc
      realJetSourceEvaluation coefficientEval u d jets
          (transferCertificate.source a) n =
          realJetSourceEvaluationHom coefficientEval u d jets n
            (transferCertificate.source a) := rfl
      _ = realJetSourceEvaluationHom coefficientEval u d jets n
          (∑ k, data.identities.sourceCoefficient a k *
            data.source.generator k) :=
        congrArg (realJetSourceEvaluationHom coefficientEval u d jets n)
          (data.identities.source_identity a)
      _ = ∑ k, sourceCoefficient a k n *
          realJetSourceEvaluationHom coefficientEval u d jets n
            (data.source.generator k) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_mul]
  exact transferCertificate.realJet_quantitativeTransfer
    d (certificate.centralTransferInput r) hA
    coefficientEval u hierarchy.positive jets Rscale Xscale
    (fun b n ↦ realJetCentralEvaluationHom A coefficientEval u d n
      (data.central.generator b))
    centralCoefficient
    (fun k n ↦ realJetSourceEvaluationHom coefficientEval u d jets n
      (data.source.generator k))
    sourceCoefficient hierarchy.order hpos hierarchy.scale_ge_two
    hierarchy.adjacent_ratios hierarchy.smallest_div_log_scale
    domination.scale_le domination.target_ge_two domination.exponential_le
    Pweight hweight hcoefficient hmainBound hperturbedBound
    hcoordinateError hcentralIdentity hcentralCoefficient hcentralLower
    hsourceIdentity hsourceCoefficient

/-- Cardinality-independent form of direct quantitative propagation through
one displayed full central step.  `FiniteRealJetTransferHierarchies` merely
transports the existing successor-indexed hierarchy across a proof of the
finite cardinality; no transfer theorem is duplicated. -/
theorem realJet_source_lower_of_central_lower_direct
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h)
        (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (terminalTotalDerivativeCount higher i))
    (Rscale Xscale : ℕ → ℝ)
    (hierarchies : FiniteRealJetTransferHierarchies
      h u Rscale Xscale)
    (hcoefficient : ∀ q,
      HasPolynomialUpperBound atTop Rscale (coefficientEval q))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (finiteRealJetMainAssignment A u
          (terminalTotalDerivativeCount higher) x))
    (hcentralValueBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (fun n ↦ realCentralTransferCentralValue A (fun i ↦ u i n)
          (terminalTotalDerivativeCount higher) x))
    (hsourceValueBound : ∀ x,
      HasPolynomialUpperBound atTop Xscale
        (finiteRealJetActualAssignment u (terminalTotalDerivativeCount higher)
          jets x))
    (hjetError : ∀ i
      (q : Fin (terminalTotalDerivativeCount higher i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error q))
    (hcentralLower : HasInversePowerLowerBound atTop Rscale
      (fun b n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount higher) n
        (data.central.generator b))) :
    HasInversePowerLowerBound atTop Xscale
      (fun k n ↦ finiteRealJetSourceEvaluationHom coefficientEval u
        (terminalTotalDerivativeCount higher) jets n
        (data.source.generator k)) := by
  rcases hierarchies with ⟨m, hcard, hierarchy, domination⟩
  subst h
  exact data.realJet_source_lower_of_central_lower_direct_successor hA
    coefficientEval u jets Rscale Xscale hierarchy domination
    hcoefficient hmainBound hcentralValueBound hsourceValueBound
    hjetError hcentralLower

end ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

namespace RepresentativeClusterSubsequence

/-- The canonical scale at simultaneous boundary `r`: the largest
final-order balanced representative after `r` common logarithmic
decrements.  Boundary `r + 1` is the post-step scale and boundary `r` is the
corresponding source scale. -/
def orderedClusterSimultaneousBoundaryScale
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (r n : ℕ) : ℝ :=
  inverse A
    (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) - (r : ℝ))

/-- The post-log value at final position zero is exactly the next canonical
simultaneous boundary scale. -/
theorem orderedClusterSimultaneousPostLogScale_zero_eq_boundaryScale
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (r n : ℕ) :
    data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
        finalOrder r (data.orderedClusterBalancingToActiveEquiv c 0) n =
      data.orderedClusterSimultaneousBoundaryScale c A rawTime fixedSteps
        finalOrder (r + 1) n := by
  simp only [orderedClusterSimultaneousPostLogScale_apply,
    orderedClusterSimultaneousBoundaryScale]

/-- A fixed polynomial in the smaller-prefix coefficient ring remains
polynomially bounded after applying the common prefix evaluation. -/
theorem OrderedClusterPreprocessedAlgebraicStage.coefficientSequenceHom_hasPolynomialUpperBound
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
      fixedSteps fixedOrder initialIdeal j hj)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hbase : ∀ q, HasPolynomialUpperBound atTop scale (base q))
    (hprefix : ∀ z, HasPolynomialUpperBound atTop scale (prefixValue z)) :
    ∀ q, HasPolynomialUpperBound atTop scale
      (stage.coefficientSequenceHom base prefixValue q) := by
  intro q
  exact mvPolynomial_eval₂Hom_hasPolynomialUpperBound
    hscale base prefixValue hbase hprefix q

end RepresentativeClusterSubsequence

/-- Fixed balancing and final-order data construct both hierarchy records at
an arbitrary simultaneous operation.  The internal hierarchy is the
maintained balanced-cluster theorem at iterate `r + 1`; domination by the
preceding boundary follows from the Abel recurrence and final-order
monotonicity. -/
theorem IsAbel.orderedClusterSimultaneousStep_transferHierarchies
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (baseTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (baseTime n))
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    (hfixedOrder : ∀ n, (plans n).finalOrder = finalOrder)
    (r : ℕ)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : ((r + 6 : ℕ) : ℝ) ≤ N)
    (hbaseTop : Tendsto baseTime atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (data.orderedClusterTailSize c + 1), i ≠ k →
        separationConstant / inverse A (baseTime n - N) ≤
          integerDistance (rawTime n i - rawTime n k)) :
    FiniteRealJetTransferHierarchies
      (data.orderedCluster c).card
      (data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
        finalOrder r)
      (data.orderedClusterSimultaneousBoundaryScale c A rawTime fixedSteps
        finalOrder (r + 1))
      (data.orderedClusterSimultaneousBoundaryScale c A rawTime fixedSteps
        finalOrder r) := by
  let e := data.orderedClusterBalancingToActiveEquiv c
  let uActive := data.orderedClusterSimultaneousPostLogScale c A rawTime
    fixedSteps finalOrder r
  let u : Fin (data.orderedClusterTailSize c + 1) → ℕ → ℝ :=
    fun i n ↦ uActive (e i) n
  let Rscale := data.orderedClusterSimultaneousBoundaryScale c A rawTime
    fixedSteps finalOrder (r + 1)
  let Xscale := data.orderedClusterSimultaneousBoundaryScale c A rawTime
    fixedSteps finalOrder r
  have hmargin : (0 : ℝ) + (r + 1 : ℕ) + 5 ≤ N := by
    norm_num at hN ⊢
    linarith
  have hierarchy₀ := hA.balanced_realJetTransferHierarchy
    rawTime baseTime baseTime plans finalOrder hfixedOrder (r + 1)
      hseparationConstant hmargin hbaseTop
      (Filter.Eventually.of_forall fun n ↦ by simp) hseparated
  have hierarchy : BalancedRealJetTransferHierarchy
      (data.orderedClusterTailSize c) u Rscale := by
    change BalancedRealJetTransferHierarchy
      (data.orderedClusterTailSize c) u
        (fun n ↦ inverse A
          (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
            ((r + 1 : ℕ) : ℝ)))
    simpa only [u, uActive, e,
      RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale_apply,
      ClusterBalancingPlan.finalTimes, hfixedSteps,
      hA.L_iterate_inverse] using hierarchy₀
  have hRleX : ∀ n, Rscale n ≤ Xscale n := by
    intro n
    change inverse A
        (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
          ((r + 1 : ℕ) : ℝ)) ≤
      inverse A
        (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
          (r : ℝ))
    apply hA.inverse_strictMono.monotone
    push_cast
    linarith
  have hEuZero : ∀ n, E (u 0 n) = Xscale n := by
    intro n
    change E (inverse A
        (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
          ((r + 1 : ℕ) : ℝ))) =
      inverse A
        (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
          (r : ℝ))
    calc
      E (inverse A
          (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
            ((r + 1 : ℕ) : ℝ))) =
          inverse A
            ((clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
              ((r + 1 : ℕ) : ℝ)) + 1) :=
        (hA.inverse_add_one _).symm
      _ = inverse A
          (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder 0) -
            (r : ℝ)) := by
        congr 1
        push_cast
        ring
  have domination : CrossClusterTransferScaleDomination
      (data.orderedClusterTailSize c) u Rscale Xscale := by
    refine {
      scale_le := Filter.Eventually.of_forall hRleX
      target_ge_two := ?_
      exponential_le := ?_ }
    · filter_upwards [hierarchy.scale_ge_two] with n hn
      exact hn.trans (hRleX n)
    · filter_upwards [hierarchy.order] with n hn
      intro i
      calc
        E (u i n) ≤ E (u 0 n) :=
          E_strictMono.monotone (hn.antitone (Fin.zero_le i))
        _ = Xscale n := hEuZero n
  refine ⟨data.orderedClusterTailSize c,
    data.orderedClusterTailSize_add_one c, ?_, ?_⟩
  · simpa only [u, uActive, e,
      RepresentativeClusterSubsequence.orderedClusterBalancingToActiveEquiv,
      Rscale] using hierarchy
  · simpa only [u, uActive, e,
      RepresentativeClusterSubsequence.orderedClusterBalancingToActiveEquiv,
      Rscale, Xscale] using domination

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

/-- Evaluation of the exact source-side displayed family at one simultaneous
operation. -/
def simultaneousBeforeGeneratorValue
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    {A : ℝ → ℝ} (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)) :
    Fin ((trace.simultaneousDisplayed r).source.count + 1) → ℕ → ℝ :=
  fun k n ↦ MvPolynomial.eval₂Hom
    (stage.coefficientSequenceHom base prefixValue)
    (simultaneousCentralPreLogActiveAssignment
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets)
    (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
      (data.OrderedClusterPrefixRing R higher j)
      (trace.simultaneousDisplayed r) k) n

/-- Evaluation of the exact central-side displayed family at one
simultaneous operation. -/
def simultaneousAfterGeneratorValue
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ) :
    Fin ((trace.simultaneousDisplayed r).central.count + 1) → ℕ → ℝ :=
  fun b n ↦ MvPolynomial.eval₂Hom
    (stage.coefficientSequenceHom base prefixValue)
    (simultaneousCentralPostLogActiveAssignment A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)))
    (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
      (data.OrderedClusterPrefixRing R higher j)
      (trace.simultaneousDisplayed r) b) n

/-- The genuinely analytic inputs for one simultaneous step.  Fixed
algebraic identities, finite matrix bounds, and hierarchy fields are omitted
because the transfer theorem derives them. -/
structure SimultaneousQuantitativeData
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (r : ℕ) where
  jets : ∀ n i, RealCentralJetSubstitutionData A
    (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r i n)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)
  base_bound : ∀ q, HasPolynomialUpperBound atTop
    (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r + 1))
    (base q)
  prefix_bound : ∀ z, HasPolynomialUpperBound atTop
    (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r + 1))
    (prefixValue z)
  main_bound : ∀ x, HasPolynomialUpperBound atTop
    (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r + 1))
    (finiteRealJetMainAssignment A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) x)
  central_value_bound : ∀ x, HasPolynomialUpperBound atTop
    (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r + 1))
    (fun n ↦ realCentralTransferCentralValue A
      (fun i ↦ data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩
        A rawTime (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) x)
  source_value_bound : ∀ x, HasPolynomialUpperBound atTop
    (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r)
    (finiteRealJetActualAssignment
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets x)
  jet_error : ∀ i
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)),
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r + 1))
      (fun n ↦ (jets n i).error q)

/-- Quantitative lower-bound propagation at an arbitrary simultaneous
operation of one preprocessed ordered-cluster stage.

The hierarchy and both fixed polynomial matrix bounds are discharged in the
proof.  The hypotheses left to the concrete Hermite construction are bounds
for coefficients and coordinates, decay of the actual jet errors, and the
lower bound on the next displayed family. -/
theorem simultaneousBeforeGenerator_lower_of_afterGenerator_lower
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    {A : ℝ → ℝ} (hA : IsAbel A)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
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
      ∀ i k : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        i ≠ k →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n i - rawTime n k))
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (hbase : ∀ q, HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (base q))
    (hprefix : ∀ z, HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (prefixValue z))
    (hmainBound : ∀ x, HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (finiteRealJetMainAssignment A
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) x))
    (hcentralValueBound : ∀ x, HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (fun n ↦ realCentralTransferCentralValue A
        (fun i ↦ data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩
          A rawTime (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩)
            r.val i n)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) x))
    (hsourceValueBound : ∀ x, HasPolynomialUpperBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      (finiteRealJetActualAssignment
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets x))
    (hjetError : ∀ i
      (q : Fin (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i)),
      Asymptotics.SuperpolynomialDecay atTop
        (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
        (fun n ↦ (jets n i).error q))
    (hcentralLower : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (fun b n ↦ MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPostLogActiveAssignment A
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed r) b) n)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      (fun k n ↦ MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPreLogActiveAssignment
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets)
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed r) k) n) := by
  let c : Fin data.orderedClusterCount := ⟨j, hj⟩
  let u := data.orderedClusterSimultaneousPostLogScale c A rawTime
    (fixedSteps c) (fixedOrder c) r.val
  let d := terminalTotalDerivativeCount
    (fun _ : Fin (data.orderedCluster c).card ↦ higher)
  let Rscale := data.orderedClusterSimultaneousBoundaryScale c A rawTime
    (fixedSteps c) (fixedOrder c) (r.val + 1)
  let Xscale := data.orderedClusterSimultaneousBoundaryScale c A rawTime
    (fixedSteps c) (fixedOrder c) r.val
  let coefficientEval := stage.coefficientSequenceHom base prefixValue
  let step := trace.simultaneousDisplayed r
  have hierarchies : FiniteRealJetTransferHierarchies
      (data.orderedCluster c).card u Rscale Xscale :=
    hA.orderedClusterSimultaneousStep_transferHierarchies data c rawTime
      baseTime plans (fixedSteps c) (fixedOrder c) hfixedSteps hfixedOrder
      r.val hseparationConstant hN hbaseTop hseparated
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchies.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hcoefficient : ∀ q,
      HasPolynomialUpperBound atTop Rscale (coefficientEval q) := by
    exact stage.coefficientSequenceHom_hasPolynomialUpperBound base
      prefixValue Rscale hRone hbase hprefix
  have hcentralLowerRealJet : HasInversePowerLowerBound atTop Rscale
      (fun b n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u d n
        (step.central.generator b)) := by
    apply hasInversePowerLowerBound_of_eventuallyEq
      (Filter.Eventually.of_forall fun n b ↦ ?_) hcentralLower
    simpa only [c, u, d, Rscale, coefficientEval, step] using
      trace.eval_simultaneousAfterGenerator_postLog
        r A base prefixValue rawTime b n
  have hsourceLowerRealJet : HasInversePowerLowerBound atTop Xscale
      (fun k n ↦ finiteRealJetSourceEvaluationHom coefficientEval u d
        jets n (step.source.generator k)) :=
    step.realJet_source_lower_of_central_lower_direct hA coefficientEval u
      jets Rscale Xscale hierarchies hcoefficient hmainBound
      hcentralValueBound hsourceValueBound hjetError hcentralLowerRealJet
  apply hasInversePowerLowerBound_of_eventuallyEq
    (Filter.Eventually.of_forall fun n k ↦ ?_) hsourceLowerRealJet
  simpa only [c, u, d, Xscale, coefficientEval, step] using
    (trace.eval_simultaneousBeforeGenerator_preLog
      r base prefixValue rawTime jets k n).symm

/-- The arbitrary-step theorem with its genuine analytic hypotheses bundled
in `SimultaneousQuantitativeData`. -/
theorem simultaneousBeforeGenerator_lower_of_afterGenerator_lower_of_data
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    {A : ℝ → ℝ} (hA : IsAbel A)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
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
      ∀ i k : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        i ≠ k →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n i - rawTime n k))
    (quantitative : SimultaneousQuantitativeData
      A base prefixValue rawTime r.val)
    (hcentralLower : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (r.val + 1))
      (trace.simultaneousAfterGeneratorValue
        r A base prefixValue rawTime)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
      (trace.simultaneousBeforeGeneratorValue
        r base prefixValue rawTime quantitative.jets) := by
  unfold simultaneousAfterGeneratorValue at hcentralLower
  unfold simultaneousBeforeGeneratorValue
  exact trace.simultaneousBeforeGenerator_lower_of_afterGenerator_lower r hA
    base prefixValue rawTime baseTime plans hfixedSteps hfixedOrder
    hseparationConstant hN hbaseTop hseparated quantitative.jets
    quantitative.base_bound quantitative.prefix_bound
    quantitative.main_bound quantitative.central_value_bound
    quantitative.source_value_bound quantitative.jet_error hcentralLower

/-- Quantitative propagation through the distinguished first simultaneous
operation.  It starts at simultaneous boundary zero and ends at boundary
one. -/
theorem firstSimultaneousBeforeGenerator_lower_of_afterGenerator_lower
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (baseTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (baseTime n))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps ⟨j, hj⟩)
    (hfixedOrder : ∀ n, (plans n).finalOrder = fixedOrder ⟨j, hj⟩)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : (6 : ℝ) ≤ N)
    (hbaseTop : Tendsto baseTime atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        i ≠ k →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n i - rawTime n k))
    (quantitative : SimultaneousQuantitativeData
      A base prefixValue rawTime 0)
    (hcentralLower : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 1)
      (trace.simultaneousAfterGeneratorValue
        stage.certificate.firstCentralStepIndex
        A base prefixValue rawTime)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
      (trace.simultaneousBeforeGeneratorValue
        stage.certificate.firstCentralStepIndex
        base prefixValue rawTime quantitative.jets) := by
  exact trace.simultaneousBeforeGenerator_lower_of_afterGenerator_lower_of_data
    stage.certificate.firstCentralStepIndex hA base prefixValue rawTime
    baseTime plans hfixedSteps hfixedOrder hseparationConstant hN hbaseTop
    hseparated quantitative hcentralLower

/-- Quantitative propagation through arbitrary extra retained operation
`i`.  Its simultaneous index is `i + 1`, so it propagates from boundary
`i + 2` back to boundary `i + 1`. -/
theorem extraRetainedBeforeGenerator_lower_of_afterGenerator_lower
    (trace : stage.FullTransferTraceData)
    (i : Fin stage.certificate.terminalized.extraSteps)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (baseTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (baseTime n))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps ⟨j, hj⟩)
    (hfixedOrder : ∀ n, (plans n).finalOrder = fixedOrder ⟨j, hj⟩)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : (((i.val + 7 : ℕ) : ℝ)) ≤ N)
    (hbaseTop : Tendsto baseTime atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ a b : Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1),
        a ≠ b →
          separationConstant / inverse A (baseTime n - N) ≤
            integerDistance (rawTime n a - rawTime n b))
    (quantitative : SimultaneousQuantitativeData
      A base prefixValue rawTime (i.val + 1))
    (hcentralLower : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 2))
      (trace.simultaneousAfterGeneratorValue
        i.succ A base prefixValue rawTime)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
      (trace.simultaneousBeforeGeneratorValue
        i.succ base prefixValue rawTime quantitative.jets) := by
  exact trace.simultaneousBeforeGenerator_lower_of_afterGenerator_lower_of_data
    i.succ hA base prefixValue rawTime baseTime plans hfixedSteps hfixedOrder
    hseparationConstant hN hbaseTop hseparated quantitative hcentralLower

/-! ## Reverse propagation through the complete simultaneous segment -/

/-- The re-extended central family at simultaneous operation `i` and the
un-translated source family at operation `i + 1` span the same stored unused
representative extension.  This is the algebraic boundary identification
used between consecutive quantitative steps. -/
theorem simultaneousAfter_span_eq_nextBefore_span
    (trace : stage.FullTransferTraceData)
    (i : Fin stage.certificate.terminalized.extraSteps) :
    Ideal.span (Set.range
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
        (data.OrderedClusterPrefixRing R higher j)
        (trace.simultaneousDisplayed i.castSucc))) =
      Ideal.span (Set.range
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed i.succ))) := by
  rw [(trace.simultaneousDisplayed i.castSucc).after_span,
    (trace.simultaneousDisplayed i.succ).before_span]
  congr 1
  have hout : stage.certificate.centralTransferOutput i.castSucc =
      stage.certificate.terminalized.centralIterationIdeal i.val := by
    by_cases hi : i.val = 0
    · have hidx : i.castSucc =
          stage.certificate.firstCentralStepIndex := Fin.ext hi
      rw [hidx, hi]
      simp [ClusterAlgebraicReductionCertificate.centralTransferOutput,
        ClusterAlgebraicReductionCertificate.firstCentralStepIndex,
        TerminalizedClusterCertificate.centralIterationIdeal]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have hklt : k < stage.certificate.terminalized.extraSteps := by omega
      let q : Fin stage.certificate.terminalized.extraSteps := ⟨k, hklt⟩
      have hidx : i.castSucc = q.succ := Fin.ext hk
      rw [hidx, hk]
      simp [ClusterAlgebraicReductionCertificate.centralTransferOutput, q]
  rw [hout]

/-- Analytic input for the whole finite simultaneous portion of one stage.
Each operation carries exactly the one-step data consumed by
`simultaneousBeforeGenerator_lower_of_afterGenerator_lower_of_data`.
The additional equality identifies the post-log assignment of operation
`i` with the pre-log assignment of operation `i + 1`, which is the sole
analytic compatibility needed at an internal retained boundary. -/
structure SimultaneousSegmentQuantitativeData
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ) where
  step : (r : Fin (stage.certificate.terminalized.extraSteps + 1)) →
    SimultaneousQuantitativeData A base prefixValue rawTime r.val
  adjacent_assignment :
    ∀ i : Fin stage.certificate.terminalized.extraSteps,
      simultaneousCentralPostLogActiveAssignment A
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) i.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) =
        simultaneousCentralPreLogActiveAssignment
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher))
          (step i.succ).jets

/-- Reverse quantitative propagation through every simultaneous operation
of a preprocessed stage.

The input is the lower bound on the displayed central family of the final
operation.  Decreasing induction first applies the final one-step theorem,
then at each retained boundary changes generators across the common unused
representative extension and applies the preceding one-step theorem.  The
result is the lower bound on the literal source family of the distinguished
first operation.  When `extraSteps = 0`, the induction has no internal
boundary and this is exactly the first one-step transfer. -/
theorem simultaneousBeforeGenerator_lower_of_terminalAfterGenerator_lower
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
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
    (segment : SimultaneousSegmentQuantitativeData (stage := stage)
      A base prefixValue rawTime)
    (hterminal : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩)
        (stage.certificate.terminalized.extraSteps + 1))
      (trace.simultaneousAfterGeneratorValue
        (Fin.last stage.certificate.terminalized.extraSteps)
        A base prefixValue rawTime)) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
      (trace.simultaneousBeforeGeneratorValue
        stage.certificate.firstCentralStepIndex
        base prefixValue rawTime
        (segment.step stage.certificate.firstCentralStepIndex).jets) := by
  let extra := stage.certificate.terminalized.extraSteps
  let scale := data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A
    rawTime (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩)
  let StepLower := fun r : Fin (extra + 1) ↦
    HasInversePowerLowerBound atTop (scale r.val)
      (trace.simultaneousBeforeGeneratorValue r base prefixValue rawTime
        (segment.step r).jets)
  have margin (r : Fin (extra + 1)) : (((r.val + 6 : ℕ) : ℝ)) ≤ N := by
    calc
      (((r.val + 6 : ℕ) : ℝ)) ≤ (((extra + 6 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ r.isLt) 6
      _ ≤ N := hN
  have top : StepLower (Fin.last extra) := by
    exact trace.simultaneousBeforeGenerator_lower_of_afterGenerator_lower_of_data
      (Fin.last extra) hA base prefixValue rawTime baseTime plans
      hfixedSteps hfixedOrder hseparationConstant (margin (Fin.last extra))
      hbaseTop hseparated (segment.step (Fin.last extra)) hterminal
  have descent : StepLower (stage.certificate.firstCentralStepIndex) := by
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
      let nextPre := simultaneousCentralPreLogActiveAssignment
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) next.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher))
        (segment.step next).jets
      have hierarchy := hA.orderedClusterSimultaneousStep_transferHierarchies
        data ⟨j, hj⟩ rawTime baseTime plans (fixedSteps ⟨j, hj⟩)
        (fixedOrder ⟨j, hj⟩) hfixedSteps hfixedOrder previous.val
        hseparationConstant (margin previous) hbaseTop hseparated
      have hscale : ∀ᶠ n in atTop, 1 ≤ scale next.val n := by
        have htwo := hierarchy.scale_ge_two
        simpa only [scale, next, previous, Fin.val_succ, Fin.val_castSucc,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          htwo.mono (fun _ hn ↦ one_le_two.trans hn)
      have hcoefficient : ∀ q,
          HasPolynomialUpperBound atTop (scale next.val)
            (stage.coefficientSequenceHom base prefixValue q) := by
        intro q
        apply stage.coefficientSequenceHom_hasPolynomialUpperBound base
          prefixValue (scale next.val) hscale
        · simpa only [scale, next, previous, Fin.val_succ,
            Fin.val_castSucc] using (segment.step previous).base_bound
        · simpa only [scale, next, previous, Fin.val_succ,
            Fin.val_castSucc] using (segment.step previous).prefix_bound
      have hcoordinate : ∀ z,
          HasPolynomialUpperBound atTop (scale next.val) (nextPre z) := by
        apply simultaneousCentralPreLogActiveAssignment_hasPolynomialUpperBound
          _ _ _ hscale
        intro z
        simpa only [scale, next, Fin.val_succ] using
          (segment.step next).source_value_bound z
      have hafterNextAssignment : HasInversePowerLowerBound atTop
          (scale next.val)
          (fun b n ↦ MvPolynomial.eval₂Hom
            (stage.coefficientSequenceHom base prefixValue) nextPre
            (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
              (data.OrderedClusterPrefixRing R higher j)
              (trace.simultaneousDisplayed previous) b) n) := by
        apply hasInversePowerLowerBound_mvPolynomial_eval₂Hom_of_span_eq
          (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
            (data.OrderedClusterPrefixRing R higher j)
            (trace.simultaneousDisplayed previous))
          (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
            (data.OrderedClusterPrefixRing R higher j)
            (trace.simultaneousDisplayed next))
          (stage.coefficientSequenceHom base prefixValue) nextPre
          hscale hcoefficient hcoordinate
        · exact trace.simultaneousAfter_span_eq_nextBefore_span i
        · change HasInversePowerLowerBound atTop (scale next.val)
            (fun k n ↦ MvPolynomial.eval₂Hom
              (stage.coefficientSequenceHom base prefixValue) nextPre
              (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
                (data.OrderedClusterPrefixRing R higher j)
                (trace.simultaneousDisplayed next) k) n) at ihNext
          exact ihNext
      have hcentral : HasInversePowerLowerBound atTop
          (scale (previous.val + 1))
          (trace.simultaneousAfterGeneratorValue previous A base
            prefixValue rawTime) := by
        unfold simultaneousAfterGeneratorValue
        have hadj := segment.adjacent_assignment i
        change HasInversePowerLowerBound atTop (scale (i.val + 1))
          (fun b n ↦ MvPolynomial.eval₂Hom
            (stage.coefficientSequenceHom base prefixValue)
            (simultaneousCentralPostLogActiveAssignment A
              (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
                (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) i.val)
              (terminalTotalDerivativeCount (fun _ :
                Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)))
            (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
              (data.OrderedClusterPrefixRing R higher j)
              (trace.simultaneousDisplayed i.castSucc) b) n)
        rw [hadj]
        simpa only [scale, next, previous, nextPre, Fin.val_succ,
          Fin.val_castSucc] using hafterNextAssignment
      have hprevious :=
        trace.simultaneousBeforeGenerator_lower_of_afterGenerator_lower_of_data
          previous hA base prefixValue rawTime baseTime plans
          hfixedSteps hfixedOrder hseparationConstant (margin previous)
          hbaseTop hseparated (segment.step previous) hcentral
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

/-- Compatibility between the first curried simultaneous source evaluation
and an actual flat boundary evaluation in the `(j+1)`-prefix ring.  The
scale equality and evaluation equality are the exact seam supplied by a
coherent sequence boundary; the polynomial pullback and its ideal span are
already fixed by `flatBeforeGenerator` and `firstFlatBefore_span`. -/
structure FirstFlatBoundaryCompatibility
    (trace : stage.FullTransferTraceData)
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0 i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (coefficientMap : R →+* (ℕ → ℝ))
    (terminalScale : ℕ → ℝ)
    (terminalValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (j + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (j + 1)) → ℕ → ℝ) where
  scale_eq : terminalScale =
    data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0
  evaluation_eq : ∀ k n,
    MvPolynomial.eval₂Hom coefficientMap terminalValue
        (trace.flatBeforeGenerator stage.certificate.firstCentralStepIndex k) n =
      trace.simultaneousBeforeGeneratorValue
        stage.certificate.firstCentralStepIndex base prefixValue rawTime jets k n

/-- Pull a first-simultaneous source lower bound back through final-order
relabeling and ordered-prefix currying.  The result is an existentially
padded lower package for the literal preprocessing output ideal. -/
noncomputable def firstFlatBoundaryLower_of_simultaneousBeforeGenerator_lower
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0 i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (coefficientMap : R →+* (ℕ → ℝ))
    (terminalScale : ℕ → ℝ)
    (terminalValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (j + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (j + 1)) → ℕ → ℝ)
    (compatibility : FirstFlatBoundaryCompatibility trace A base prefixValue
      rawTime jets coefficientMap terminalScale terminalValue)
    (hfirst : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
      (trace.simultaneousBeforeGeneratorValue
        stage.certificate.firstCentralStepIndex
        base prefixValue rawTime jets)) :
    EvaluatedPaddedIdealLowerBound
      (ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (j + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (j + 1)))
      atTop terminalScale coefficientMap terminalValue
      stage.preprocessingOutput := by
  refine {
    count := (trace.simultaneousDisplayed
      stage.certificate.firstCentralStepIndex).source.count
    generator := trace.flatBeforeGenerator
      stage.certificate.firstCentralStepIndex
    span_eq := trace.firstFlatBefore_span
    lower := ?_ }
  rw [compatibility.scale_eq]
  apply hasInversePowerLowerBound_of_eventuallyEq
    (Filter.Eventually.of_forall fun n k ↦ ?_) hfirst
  exact (compatibility.evaluation_eq k n).symm

/-- Specialize the flat pullback to the exact terminal boundary package of
the stage's selected individual preprocessing trace.  This is the output
type required by `SimultaneousSegmentBackward` and
`SimultaneousSegmentBackwardFrom`. -/
noncomputable def individualTerminalBoundaryLower_of_simultaneousBeforeGenerator_lower
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (φ : ℕ → ℕ)
    (boundary : data.OrderedClusterIndividualQuantitativeBoundaryData
      higher ⟨j, hj⟩ A φ (fixedSteps ⟨j, hj⟩))
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0 i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (coefficientMap : R →+* (ℕ → ℝ))
    (compatibility : FirstFlatBoundaryCompatibility trace A base prefixValue
      rawTime jets coefficientMap
      (data.orderedClusterIndividualBoundaryScale A φ ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length))
      (boundary.value
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length)))
    (hfirst : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
      (trace.simultaneousBeforeGeneratorValue
        stage.certificate.firstCentralStepIndex
        base prefixValue rawTime jets)) :
    data.OrderedClusterIndividualBoundaryLower R higher ⟨j, hj⟩ A φ
      (fixedSteps ⟨j, hj⟩) stage.preprocessingInput coefficientMap boundary
      (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)).length) := by
  have hout :=
    trace.firstFlatBoundaryLower_of_simultaneousBeforeGenerator_lower
      base prefixValue rawTime jets coefficientMap
      (data.orderedClusterIndividualBoundaryScale A φ ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length))
      (boundary.value
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length)) compatibility hfirst
  change EvaluatedPaddedIdealLowerBound
    (ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (j + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (j + 1)))
    atTop
    (data.orderedClusterIndividualBoundaryScale A φ ⟨j, hj⟩
      (fixedSteps ⟨j, hj⟩)
      (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)).length))
    coefficientMap
    (boundary.value
      (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)).length))
    (data.orderedClusterIndividualIdealBoundary R higher ⟨j, hj⟩
      (fixedSteps ⟨j, hj⟩) stage.preprocessingInput
      (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)).length))
  rw [trace.individual_terminal_boundary]
  exact hout

/-- Complete local callback from the last displayed simultaneous central
family to the exact terminal package of the preceding individual segment.
This composes the finite reverse simultaneous recursion with the flat
final-order/curry pullback, and therefore has precisely the codomain required
by the global `SimultaneousSegmentBackward` interfaces. -/
noncomputable def individualTerminalBoundaryLower_of_terminalAfterGenerator_lower
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A) (φ : ℕ → ℕ)
    (boundary : data.OrderedClusterIndividualQuantitativeBoundaryData
      higher ⟨j, hj⟩ A φ (fixedSteps ⟨j, hj⟩))
    (base coefficientMap : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
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
    (segment : SimultaneousSegmentQuantitativeData (stage := stage)
      A base prefixValue rawTime)
    (compatibility : FirstFlatBoundaryCompatibility trace A base prefixValue
      rawTime
      (segment.step stage.certificate.firstCentralStepIndex).jets
      coefficientMap
      (data.orderedClusterIndividualBoundaryScale A φ ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length))
      (boundary.value
        (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
          (fixedSteps ⟨j, hj⟩)).length)))
    (hterminal : HasInversePowerLowerBound atTop
      (data.orderedClusterSimultaneousBoundaryScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩)
        (stage.certificate.terminalized.extraSteps + 1))
      (trace.simultaneousAfterGeneratorValue
        (Fin.last stage.certificate.terminalized.extraSteps)
        A base prefixValue rawTime)) :
    data.OrderedClusterIndividualBoundaryLower R higher ⟨j, hj⟩ A φ
      (fixedSteps ⟨j, hj⟩) stage.preprocessingInput coefficientMap boundary
      (Fin.last (data.orderedClusterPrefixIndividualSteps ⟨j, hj⟩
        (fixedSteps ⟨j, hj⟩)).length) := by
  have hfirst :=
    trace.simultaneousBeforeGenerator_lower_of_terminalAfterGenerator_lower
      hA base prefixValue rawTime baseTime plans hfixedSteps hfixedOrder
      hseparationConstant hN hbaseTop hseparated segment hterminal
  exact trace.individualTerminalBoundaryLower_of_simultaneousBeforeGenerator_lower
    φ boundary base prefixValue rawTime
    (segment.step stage.certificate.firstCentralStepIndex).jets
    coefficientMap compatibility hfirst

end OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData

end RepresentativeClusterSubsequence

end AbelFormalization
