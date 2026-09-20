import AbelFormalization.OrderedClusterSimultaneousQuantitativeTransfer

/-!
# Numeric quantitative transfer through one displayed central step

The existing displayed-step theorem evaluates the entire coefficient ring by
a homomorphism into real sequences.  For analytic-germ coefficients, only
the coefficients of the finite canonical source family and the two finite
change-of-generators matrices are used.  This file exposes that finite
numeric interface and reuses the support-local quantitative transfer theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

namespace ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

/-- Quantitative propagation through a displayed central step from finite
numeric coefficient data.

The two eventual identities are the evaluated forms of the displayed
central and source changes of generators.  Coefficient bounds are required
only on the actual supports of the finite canonical source family.  No
sequence-valued evaluation homomorphism on `R` is used.
-/
theorem realJet_source_lower_of_central_lower_numeric_successor
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
    (coefficientValue :
      Fin (transferData.transferCertificate r).count →
        (RealJetTransferIndex m
          (terminalTotalDerivativeCount higher) →₀ ℕ) → ℕ → ℝ)
    (u : Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (terminalTotalDerivativeCount higher i))
    (Rscale Xscale : ℕ → ℝ)
    (hierarchy : BalancedRealJetTransferHierarchy m u Rscale)
    (domination : CrossClusterTransferScaleDomination
      m u Rscale Xscale)
    (centralValue : Fin (data.central.count + 1) → ℕ → ℝ)
    (centralCoefficient : Fin (data.central.count + 1) →
      Fin (transferData.transferCertificate r).count → ℕ → ℝ)
    (sourceValue : Fin (data.source.count + 1) → ℕ → ℝ)
    (sourceCoefficient : Fin (transferData.transferCertificate r).count →
      Fin (data.source.count + 1) → ℕ → ℝ)
    (hcoefficient : ∀ a e,
      e ∈ ((transferData.transferCertificate r).source a).support →
        HasPolynomialUpperBound atTop Rscale (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u
          (terminalTotalDerivativeCount higher) x))
    (hjetError : ∀ i
      (q : Fin (terminalTotalDerivativeCount higher i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error q))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralValue b n =
        ∑ a, centralCoefficient b a n *
          realJetCoefficientwiseCentralEvaluation A
            (terminalTotalDerivativeCount higher) (coefficientValue a) u
            ((transferData.transferCertificate r).source a) n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralValue)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount higher) (coefficientValue a) u jets
          ((transferData.transferCertificate r).source a) n =
        ∑ k, sourceCoefficient a k n * sourceValue k n)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient) :
    HasInversePowerLowerBound atTop Xscale sourceValue := by
  let d := terminalTotalDerivativeCount higher
  let transferCertificate := transferData.transferCertificate r
  haveI : Nonempty (Fin transferCertificate.count) :=
    transferData.source_nonempty r
  obtain ⟨Pweight, hweight⟩ := data.exists_leastWeight_bound
  have hpos : ∀ᶠ n in atTop, 0 < u (Fin.last m) n :=
    Filter.Eventually.of_forall fun n ↦ hierarchy.positive n (Fin.last m)
  have hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ realCentralTransferCoordinateError (jets n) x) :=
    realCentralTransferCoordinateError_superpolynomialDecay_of_errors
      jets hjetError
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hierarchy.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  have hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d jets x) := by
    intro x
    apply ((hmainBound x).add hRone
      (superpolynomialDecay_hasPolynomialUpperBound
        (hcoordinateError x))).congr
    intro n
    rfl
  exact transferCertificate.realJet_quantitativeTransfer_coefficientwise
    d (certificate.centralTransferInput r) hA coefficientValue u
    hierarchy.positive jets Rscale Xscale centralValue centralCoefficient
    sourceValue sourceCoefficient hierarchy.order hpos hierarchy.scale_ge_two
    hierarchy.adjacent_ratios hierarchy.smallest_div_log_scale
    domination.scale_le domination.target_ge_two domination.exponential_le
    Pweight hweight hcoefficient hmainBound hperturbedBound hcoordinateError
    hcentralIdentity hcentralCoefficient hcentralLower hsourceIdentity
    hsourceCoefficient

/-- Support-local source evaluation for an arbitrary finite block
cardinality.  This is the cardinality-independent spelling of
`realJetCoefficientwiseSourceEvaluation`. -/
def finiteRealJetCoefficientwiseSourceEvaluation
    {R : Type u} [CommRing R] {h : ℕ} {A : ℝ → ℝ}
    (d : Fin h → ℕ)
    (coefficientValue :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) → ℕ → ℝ)
    (u : Fin h → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (f : MvPolynomial (ClusterOperationSymbol (Fin h) d) R)
    (n : ℕ) : ℝ :=
  finiteSupportPolynomialEvaluation f (fun e ↦ coefficientValue e n)
    (fun x ↦ finiteRealJetActualAssignment u d jets x n)

/-- Support-local central initial evaluation for an arbitrary finite block
cardinality. -/
def finiteRealJetCoefficientwiseCentralEvaluation
    {R : Type u} [CommRing R] {h : ℕ}
    (A : ℝ → ℝ) (d : Fin h → ℕ)
    (coefficientValue :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) → ℕ → ℝ)
    (u : Fin h → ℕ → ℝ)
    (f : MvPolynomial (ClusterOperationSymbol (Fin h) d) R)
    (n : ℕ) : ℝ :=
  finiteSupportInitialEvaluation
    (centralLaurentWeight (centralTransferShear d)) f
    (fun e ↦ coefficientValue e n)
    (fun x ↦ finiteRealJetMainAssignment A u d x n)

/-- Cardinality-independent form of the finite numeric displayed-step
transfer.  `FiniteRealJetTransferHierarchies` supplies a successor
presentation of the nonempty block type and the two already-proved hierarchy
records; the proof merely transports the successor theorem across that
cardinality equality. -/
theorem realJet_source_lower_of_central_lower_numeric
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
    (coefficientValue :
      Fin (transferData.transferCertificate r).count →
        (ClusterOperationSymbol (Fin h)
          (terminalTotalDerivativeCount higher) →₀ ℕ) → ℕ → ℝ)
    (u : Fin h → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (terminalTotalDerivativeCount higher i))
    (Rscale Xscale : ℕ → ℝ)
    (hierarchies : FiniteRealJetTransferHierarchies
      h u Rscale Xscale)
    (centralValue : Fin (data.central.count + 1) → ℕ → ℝ)
    (centralCoefficient : Fin (data.central.count + 1) →
      Fin (transferData.transferCertificate r).count → ℕ → ℝ)
    (sourceValue : Fin (data.source.count + 1) → ℕ → ℝ)
    (sourceCoefficient : Fin (transferData.transferCertificate r).count →
      Fin (data.source.count + 1) → ℕ → ℝ)
    (hcoefficient : ∀ a e,
      e ∈ ((transferData.transferCertificate r).source a).support →
        HasPolynomialUpperBound atTop Rscale (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (finiteRealJetMainAssignment A u
          (terminalTotalDerivativeCount higher) x))
    (hjetError : ∀ i
      (q : Fin (terminalTotalDerivativeCount higher i)),
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n ↦ (jets n i).error q))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralValue b n =
        ∑ a, centralCoefficient b a n *
          finiteRealJetCoefficientwiseCentralEvaluation A
            (terminalTotalDerivativeCount higher) (coefficientValue a) u
            ((transferData.transferCertificate r).source a) n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralValue)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount higher) (coefficientValue a) u jets
          ((transferData.transferCertificate r).source a) n =
        ∑ k, sourceCoefficient a k n * sourceValue k n)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient) :
    HasInversePowerLowerBound atTop Xscale sourceValue := by
  rcases hierarchies with ⟨m, hcard, hierarchy, domination⟩
  subst h
  simpa only [finiteRealJetCoefficientwiseCentralEvaluation,
    finiteRealJetCoefficientwiseSourceEvaluation,
    realJetCoefficientwiseCentralEvaluation,
    realJetCoefficientwiseSourceEvaluation,
    finiteRealJetMainAssignment, finiteRealJetActualAssignment] using
      data.realJet_source_lower_of_central_lower_numeric_successor hA
        coefficientValue u jets Rscale Xscale hierarchy domination centralValue
        centralCoefficient sourceValue sourceCoefficient hcoefficient
        hmainBound hjetError hcentralIdentity hcentralCoefficient hcentralLower
        hsourceIdentity hsourceCoefficient

end ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
end AbelFormalization
