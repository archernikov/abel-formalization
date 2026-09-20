import AbelFormalization.SeparatedRingHomRealJetStep
import AbelFormalization.TerminalLocalizationNumericBridge

/-!
# One-cluster transfer with finite numeric terminal data

The coefficientwise real-jet transfer already works with independently
chosen values for the finitely many coefficients in the transfer
polynomials.  Terminal localization only needs finitely many further values
and its evaluated denominator-clearing identity.  Combining those two
interfaces removes the residual requirement for a ring homomorphism from the
whole terminal polynomial ring to real sequences.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

/-- End-to-end one-cluster backward propagation using only the numeric values
of the finitely many polynomials that occur in real-jet transfer and terminal
localization.

The first eventual identity evaluates the finite change of generators from
the real-jet source family to the contracted family.  The second evaluates
the denominator-cleared terminal-localization identity.  No evaluation map
on the ambient coefficient or polynomial ring is required.
-/
theorem TerminalGeneratorBackwardIdentity.terminal_lower_of_realJet_transfer_numeric
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
    (contractedValue : Contracted → Nat → ℝ)
    (terminalValue : Terminal → Nat → ℝ)
    (firstDerivativeValue : Fin h → Nat → ℝ)
    (localizationCoefficientValue : Contracted → Terminal → Nat → ℝ)
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
          ∑ j, sourceCoefficient a j n * contractedValue j n)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient)
    (hfirst : ∀ i : Fin h,
      HasScalarInversePowerLowerBound atTop Xscale
        (firstDerivativeValue i))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound atTop Xscale
        (localizationCoefficientValue a j))
    (hlocalizationIdentity : ∀ᶠ n in atTop, ∀ a : Contracted,
      (∏ i, firstDerivativeValue i n) ^
          clusterCertificate.denominatorExponent * contractedValue a n =
        ∑ j, localizationCoefficientValue a j n * terminalValue j n) :
    HasInversePowerLowerBound atTop Xscale terminalValue := by
  have hcontractedLower : HasInversePowerLowerBound atTop Xscale
      contractedValue := by
    exact transferCertificate.realJet_quantitativeTransfer_coefficientwise
      d I hA coefficientValue u hu jets Rscale Xscale centralGenerator
      centralCoefficient contractedValue sourceCoefficient horder hpos hR
      hratios hscale hRX hX hEX Pweight hweight hcoefficient hmainBound
      hperturbedBound hcoordinateError hcentralIdentity hcentralCoefficient
      hcentralLower hsourceIdentity hsourceCoefficient
  exact data.terminal_lower_of_numeric_identity contractedValue terminalValue
    firstDerivativeValue localizationCoefficientValue
    (hX.mono (fun _ hn => one_le_two.trans hn)) hfirst
    hlocalizationCoefficient hlocalizationIdentity hcontractedLower

end AbelFormalization
