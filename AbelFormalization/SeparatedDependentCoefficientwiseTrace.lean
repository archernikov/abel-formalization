import AbelFormalization.SeparatedRingHomRealJetStep
import AbelFormalization.SeparatedFiniteRealJetTrace

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

/-- A finite family of coefficientwise real-jet/localization steps whose
coefficient rings and active-cluster sizes may vary from stage to stage. -/
theorem separatedClustersBackwardTrace_of_coefficientwise_realJet_transfer_family
    (R : ℕ → Type u) [∀ j, CommRing (R j)]
    (clusterCount : ℕ)
    (generatorCount : ℕ → ℕ)
    (m : ℕ → ℕ) (d : ∀ j, Fin (m j + 1) → ℕ)
    (higher : ∀ j, Fin (m j + 1) → ℕ)
    (Q : ∀ j, Ideal (CentralPolynomial (R j) (Fin (m j + 1))
      (terminalTotalDerivativeCount (higher j)) (Fin (m j + 1))))
    (clusterCertificate : ∀ j,
      TerminalizedClusterCertificate (R j) (m j + 1) (higher j) (Q j))
    (contractedGenerator : ∀ j,
      Fin (generatorCount (j + 1) + 1) →
        MvPolynomial (Fin (m j + 1)) (R j))
    (terminalGenerator : ∀ j,
      Fin (generatorCount j + 1) →
        TerminalMultiblockSourceRing (R j) (m j + 1) (higher j)
          (Fin (m j + 1)))
    (identityData : ∀ j,
      TerminalGeneratorBackwardIdentity (R j) (higher j)
        (clusterCertificate j) (contractedGenerator j)
        (terminalGenerator j))
    (eval : ∀ j, ℕ →
      TerminalMultiblockSourceRing (R j) (m j + 1) (higher j)
        (Fin (m j + 1)) →+* ℝ)
    (stageScale : ℕ → ℕ → ℝ)
    (I : ∀ j, Ideal
      (MvPolynomial (RealJetTransferIndex (m j) (d j)) (R j)))
    (transferCertificate : ∀ j,
      CentralQuantitativeTransferCertificate (R j)
        (Fin (m j + 1)) (Fin (m j + 1)) (d j) (m j + 1)
        (centralTransferShear (d j)) (I j))
    (hcount : ∀ j, Nonempty (Fin (transferCertificate j).count))
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientValue : ∀ j,
      Fin (transferCertificate j).count →
        (RealJetTransferIndex (m j) (d j) →₀ ℕ) → ℕ → ℝ)
    (u : ∀ j, Fin (m j + 1) → ℕ → ℝ)
    (jets : ∀ j n i,
      RealCentralJetSubstitutionData A (u j i n) (d j i))
    (internalHierarchy : ∀ j, j < clusterCount →
      BalancedRealJetTransferHierarchy (m j) (u j) (stageScale (j + 1)))
    (crossDomination : ∀ j, j < clusterCount →
      CrossClusterTransferScaleDomination (m j) (u j)
        (stageScale (j + 1)) (stageScale j))
    (centralCoefficient : ∀ j,
      Fin (generatorCount (j + 1) + 1) →
        Fin (transferCertificate j).count → ℕ → ℝ)
    (sourceCoefficient : ∀ j,
      Fin (transferCertificate j).count →
        Fin (generatorCount (j + 1) + 1) → ℕ → ℝ)
    (hcoefficient : ∀ j, j < clusterCount → ∀ a e,
      e ∈ ((transferCertificate j).source a).support →
        HasPolynomialUpperBound atTop (stageScale (j + 1))
          (coefficientValue j a e))
    (hcentralCoefficient : ∀ j, j < clusterCount →
      HasUniformPolynomialUpperBound atTop (stageScale (j + 1))
        (centralCoefficient j))
    (hsourceCoefficient : ∀ j, j < clusterCount →
      HasUniformPolynomialUpperBound atTop (stageScale j)
        (sourceCoefficient j))
    (Pweight : ℕ → ℕ)
    (hweight : ∀ j, j < clusterCount →
      ∀ a : Fin (transferCertificate j).count,
        (∑ i, abs
          (coefficientwiseLeastWeight
            (centralLaurentWeight (centralTransferShear (d j)))
            ((transferCertificate j).source a) i : ℝ)) ≤
              (Pweight j : ℝ))
    (hmainBound : ∀ j, j < clusterCount → ∀ x,
      HasPolynomialUpperBound atTop (stageScale (j + 1))
        (realJetMainAssignment A (u j) (d j) x))
    (hperturbedBound : ∀ j, j < clusterCount → ∀ x,
      HasPolynomialUpperBound atTop (stageScale (j + 1))
        (realJetPerturbedAssignment (u j) (d j) (jets j) x))
    (hcoordinateError : ∀ j, j < clusterCount → ∀ x,
      Asymptotics.SuperpolynomialDecay atTop (stageScale (j + 1))
        (fun n ↦ realCentralTransferCoordinateError (jets j n) x))
    (hcentralIdentity : ∀ j, j < clusterCount →
      ∀ᶠ n in atTop, ∀ b : Fin (generatorCount (j + 1) + 1),
        eval (j + 1) n (terminalGenerator (j + 1) b) =
          ∑ a, centralCoefficient j b a n *
            realJetCoefficientwiseCentralEvaluation A (d j)
              (coefficientValue j a) (u j)
              ((transferCertificate j).source a) n)
    (hsourceIdentity : ∀ j, j < clusterCount →
      ∀ᶠ n in atTop, ∀ a : Fin (transferCertificate j).count,
        realJetCoefficientwiseSourceEvaluation (d j)
            (coefficientValue j a) (u j) (jets j)
            ((transferCertificate j).source a) n =
          ∑ k, sourceCoefficient j a k n *
            eval j n
              (terminalMultiblockRetainedSourceHom (R j)
                (Fin (m j + 1)) (m j + 1) (higher j)
                (contractedGenerator j k)))
    (hfirst : ∀ j, j < clusterCount → ∀ i : Fin (m j + 1),
      HasScalarInversePowerLowerBound atTop (stageScale j)
        (fun n ↦ eval j n
          (MvPolynomial.X
            (Sum.inl ⟨i, (0 : Fin (higher j i + 1))⟩))))
    (hlocalizationCoefficient : ∀ j, j < clusterCount → ∀ a k,
      HasPolynomialUpperBound atTop (stageScale j)
        (fun n ↦ eval j n ((identityData j).coefficient a k))) :
    SeparatedClustersBackwardTrace atTop clusterCount generatorCount
      stageScale
      (fun j a n ↦ eval j n (terminalGenerator j a)) := by
  refine ⟨?_⟩
  intro j hj hnext
  letI : Nonempty (Fin (transferCertificate j).count) := hcount j
  let internal := internalHierarchy j hj
  let cross := crossDomination j hj
  exact (identityData j).terminal_lower_of_realJet_transfer_coefficientwise
    (eval j) (d j) (I j) (transferCertificate j) hA
    (coefficientValue j) (u j) internal.positive (jets j)
    (stageScale (j + 1)) (stageScale j)
    (fun b n ↦ eval (j + 1) n (terminalGenerator (j + 1) b))
    (centralCoefficient j) (sourceCoefficient j)
    internal.order
    (Filter.Eventually.of_forall fun n ↦ internal.positive n (Fin.last (m j)))
    internal.scale_ge_two internal.adjacent_ratios
    internal.smallest_div_log_scale cross.scale_le
    cross.target_ge_two cross.exponential_le
    (Pweight j) (hweight j hj) (hcoefficient j hj)
    (hmainBound j hj) (hperturbedBound j hj) (hcoordinateError j hj)
    (hcentralIdentity j hj) (hcentralCoefficient j hj) hnext
    (hsourceIdentity j hj) (hsourceCoefficient j hj)
    (hfirst j hj) (hlocalizationCoefficient j hj)

end AbelFormalization
