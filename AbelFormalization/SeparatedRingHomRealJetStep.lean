import AbelFormalization.SeparatedDenominatorStep

/-!
# One-cluster transfer with a sequence-valued coefficient-ring evaluation

At every cluster after the first, the coefficient ring still contains the
unprocessed clusters.  Its evaluated coefficients need polynomial growth,
not bounded analytic dependence on the box parameter alone.  This module
connects the general ring-hom form of real-jet transfer to the maintained
terminal-localization step.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

/-- End-to-end one-cluster backward propagation when the coefficient ring is
evaluated by a ring homomorphism into real sequences.  This is the form used
while smaller, as-yet-unprocessed clusters remain in the coefficient ring. -/
theorem TerminalGeneratorBackwardIdentity.terminal_lower_of_realJet_transfer_ringHom
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {clusterCertificate : TerminalizedClusterCertificate R h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {contractedGenerator : Contracted → MvPolynomial (Fin h) R}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity R higher clusterCertificate
      contractedGenerator terminalGenerator)
    (eval : Nat → TerminalMultiblockSourceRing R h higher (Fin h) →+* ℝ)
    {m : Nat}
    (d : Fin (m + 1) → Nat)
    (I : Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (transferCertificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    [Nonempty (Fin transferCertificate.count)]
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientEval : R →+* (Nat → ℝ))
    (u : Fin (m + 1) → Nat → ℝ)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (Rscale Xscale : Nat → ℝ)
    {Central : Type} [Fintype Central] [Nonempty Central]
    (centralGenerator : Central → Nat → ℝ)
    (centralCoefficient : Central → Fin transferCertificate.count → Nat → ℝ)
    (sourceCoefficient : Fin transferCertificate.count → Contracted → Nat → ℝ)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last m) n)
    (hR : ∀ᶠ n in atTop, 2 ≤ Rscale n)
    (hratios : ∀ i : Fin m,
      Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto
      (fun n => u (Fin.last m) n / Real.log (Rscale n)) atTop atTop)
    (hRX : ∀ᶠ n in atTop, Rscale n ≤ Xscale n)
    (hX : ∀ᶠ n in atTop, 2 ≤ Xscale n)
    (hEX : ∀ᶠ n in atTop, ∀ i, E (u i n) ≤ Xscale n)
    (Pweight : Nat)
    (hweight : ∀ a,
      (∑ i, abs
        (coefficientwiseLeastWeight
          (centralLaurentWeight (centralTransferShear d))
          (transferCertificate.source a) i : ℝ)) ≤ (Pweight : ℝ))
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop Rscale (coefficientEval r))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u d x))
    (hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d jets x))
    (hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n => realCentralTransferCoordinateError (jets n) x))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n =
        ∑ a, centralCoefficient b a n *
          realJetCentralEvaluation A coefficientEval u d
            (transferCertificate.source a) n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop,
      ∀ a : Fin transferCertificate.count,
        realJetSourceEvaluation coefficientEval u d jets
            (transferCertificate.source a) n =
          ∑ j, sourceCoefficient a j n *
            eval n
              (terminalMultiblockRetainedSourceHom R (Fin h) h higher
                (contractedGenerator j)))
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient)
    (hfirst : ∀ i : Fin h,
      HasScalarInversePowerLowerBound atTop Xscale
        (fun n => eval n
          (MvPolynomial.X
            (Sum.inl ⟨i, (0 : Fin (higher i + 1))⟩))))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound atTop Xscale
        (fun n => eval n (data.coefficient a j))) :
    HasInversePowerLowerBound atTop Xscale
      (fun j n => eval n (terminalGenerator j)) := by
  have hcontractedLower : HasInversePowerLowerBound atTop Xscale
      (fun j n => eval n
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator j))) := by
    exact transferCertificate.realJet_quantitativeTransfer
      d I hA coefficientEval u hu jets Rscale Xscale centralGenerator
      centralCoefficient
      (fun j n => eval n
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator j)))
      sourceCoefficient horder hpos hR hratios hscale hRX hX hEX
      Pweight hweight hcoefficient hmainBound hperturbedBound
      hcoordinateError hcentralIdentity hcentralCoefficient
      hcentralLower hsourceIdentity hsourceCoefficient
  exact data.terminal_lower_of_contracted_lower eval
    (hX.mono (fun _ hn => one_le_two.trans hn)) hfirst
    hlocalizationCoefficient hcontractedLower

/-- End-to-end one-cluster backward propagation with independently selected
values for the finitely many source coefficients.  Only coefficients in the
actual finite supports need polynomial bounds.  This is the exact interface
for polynomial coefficient rings over analytic germs: the unprocessed block
variables are evaluated along the sequence, while only the finitely many
analytic-germ coefficients require representatives. -/
theorem TerminalGeneratorBackwardIdentity.terminal_lower_of_realJet_transfer_coefficientwise
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {clusterCertificate : TerminalizedClusterCertificate R h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {contractedGenerator : Contracted → MvPolynomial (Fin h) R}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity R higher clusterCertificate
      contractedGenerator terminalGenerator)
    (eval : Nat → TerminalMultiblockSourceRing R h higher (Fin h) →+* ℝ)
    {m : Nat}
    (d : Fin (m + 1) → Nat)
    (I : Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (transferCertificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    [Nonempty (Fin transferCertificate.count)]
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientValue : Fin transferCertificate.count →
      (RealJetTransferIndex m d →₀ Nat) → Nat → ℝ)
    (u : Fin (m + 1) → Nat → ℝ)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (Rscale Xscale : Nat → ℝ)
    {Central : Type} [Fintype Central] [Nonempty Central]
    (centralGenerator : Central → Nat → ℝ)
    (centralCoefficient : Central → Fin transferCertificate.count → Nat → ℝ)
    (sourceCoefficient : Fin transferCertificate.count → Contracted → Nat → ℝ)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last m) n)
    (hR : ∀ᶠ n in atTop, 2 ≤ Rscale n)
    (hratios : ∀ i : Fin m,
      Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto
      (fun n => u (Fin.last m) n / Real.log (Rscale n)) atTop atTop)
    (hRX : ∀ᶠ n in atTop, Rscale n ≤ Xscale n)
    (hX : ∀ᶠ n in atTop, 2 ≤ Xscale n)
    (hEX : ∀ᶠ n in atTop, ∀ i, E (u i n) ≤ Xscale n)
    (Pweight : Nat)
    (hweight : ∀ a,
      (∑ i, abs
        (coefficientwiseLeastWeight
          (centralLaurentWeight (centralTransferShear d))
          (transferCertificate.source a) i : ℝ)) ≤ (Pweight : ℝ))
    (hcoefficient : ∀ a e,
      e ∈ (transferCertificate.source a).support →
        HasPolynomialUpperBound atTop Rscale (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u d x))
    (hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d jets x))
    (hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n => realCentralTransferCoordinateError (jets n) x))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n =
        ∑ a, centralCoefficient b a n *
          realJetCoefficientwiseCentralEvaluation A d
            (coefficientValue a) u (transferCertificate.source a) n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop,
      ∀ a : Fin transferCertificate.count,
        realJetCoefficientwiseSourceEvaluation d (coefficientValue a)
            u jets (transferCertificate.source a) n =
          ∑ j, sourceCoefficient a j n *
            eval n
              (terminalMultiblockRetainedSourceHom R (Fin h) h higher
                (contractedGenerator j)))
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient)
    (hfirst : ∀ i : Fin h,
      HasScalarInversePowerLowerBound atTop Xscale
        (fun n => eval n
          (MvPolynomial.X
            (Sum.inl ⟨i, (0 : Fin (higher i + 1))⟩))))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound atTop Xscale
        (fun n => eval n (data.coefficient a j))) :
    HasInversePowerLowerBound atTop Xscale
      (fun j n => eval n (terminalGenerator j)) := by
  have hcontractedLower : HasInversePowerLowerBound atTop Xscale
      (fun j n => eval n
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator j))) := by
    exact transferCertificate.realJet_quantitativeTransfer_coefficientwise
      d I hA coefficientValue u hu jets Rscale Xscale centralGenerator
      centralCoefficient
      (fun j n => eval n
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator j)))
      sourceCoefficient horder hpos hR hratios hscale hRX hX hEX
      Pweight hweight hcoefficient hmainBound hperturbedBound
      hcoordinateError hcentralIdentity hcentralCoefficient
      hcentralLower hsourceIdentity hsourceCoefficient
  exact data.terminal_lower_of_contracted_lower eval
    (hX.mono (fun _ hn => one_le_two.trans hn)) hfirst
    hlocalizationCoefficient hcontractedLower

end AbelFormalization
