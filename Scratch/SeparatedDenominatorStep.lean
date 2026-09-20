import AbelFormalization.ClusterLocalizationIdentities
import AbelFormalization.SeparatedClustersReduction

/-!
# A concrete one-cluster denominator-cleared backward step

This scratch module exposes the fixed algebraic coefficients supplied by a
terminalized cluster certificate before introducing an evaluation, filter,
or comparison scale. Evaluating those same fixed polynomials then produces
the exact `DenominatorClearedBackwardStep` used by the finite separated-
cluster assembly.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v w

/-- Fixed algebraic data for the localization-clearing identities attached
to displayed generators of the contracted and terminal ideals. This data
depends only on the terminalized cluster certificate and on the two fixed
generating lists. -/
structure TerminalGeneratorBackwardIdentity
    (R : Type u) [CommRing R]
    {h : Nat} (higher : Fin h → Nat)
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    (contractedGenerator : Contracted → MvPolynomial (Fin h) R)
    (terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h)) where
  coefficient : Contracted → Terminal →
    TerminalMultiblockSourceRing R h higher (Fin h)
  identity : ∀ a,
    terminalFirstDerivativeProduct R (Fin h) h higher ^
          certificate.denominatorExponent *
        terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator a) =
      ∑ j, coefficient a j * terminalGenerator j

/-- The localization theorem produces the fixed backward identities before
any analytic choices are made. -/
theorem TerminalizedClusterCertificate.nonempty_terminalGeneratorBackwardIdentity
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    (contractedGenerator : Contracted → MvPolynomial (Fin h) R)
    (terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h))
    (hcontracted : Ideal.span (Set.range contractedGenerator) =
      certificate.timeIdeal)
    (hterminal : Ideal.span (Set.range terminalGenerator) =
      certificate.terminalIdeal) :
    Nonempty (TerminalGeneratorBackwardIdentity R higher certificate
      contractedGenerator terminalGenerator) := by
  obtain ⟨coefficient, hcoefficient⟩ :=
    certificate.exists_generatorIdentities contractedGenerator
      terminalGenerator hcontracted hterminal
  exact ⟨{
    coefficient := coefficient
    identity := hcoefficient
  }⟩

/-- Every evaluation of the fixed algebraic identities gives a literal
`DenominatorClearedBackwardStep`, once the analytic estimates for precisely
those fixed coefficient polynomials and the first derivatives are supplied.
-/
def TerminalGeneratorBackwardIdentity.denominatorClearedBackwardStep
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate R h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {contractedGenerator : Contracted → MvPolynomial (Fin h) R}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity R higher certificate
      contractedGenerator terminalGenerator)
    {X : Type w}
    (eval : X → TerminalMultiblockSourceRing R h higher (Fin h) →+* ℝ)
    (l : Filter X) (scale : X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hfirst : ∀ d : Fin h,
      HasScalarInversePowerLowerBound l scale
        (fun x => eval x
          (MvPolynomial.X
            (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩))))
    (hcoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (fun x => eval x (data.coefficient a j))) :
    DenominatorClearedBackwardStep (Derivative := Fin h) l scale
      (fun (a : Contracted) x => eval x
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator a)))
      (fun (j : Terminal) x => eval x (terminalGenerator j)) where
  firstDerivative := fun d x => eval x
    (MvPolynomial.X (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩))
  exponent := certificate.denominatorExponent
  coefficient := fun a j x => eval x (data.coefficient a j)
  scale_ge_one := hscale
  firstDerivative_lower := hfirst
  coefficient_bound :=
    hasUniformPolynomialUpperBound_of_finite _ hscale hcoefficient
  identity := by
    apply Filter.Eventually.of_forall
    intro x a
    have hid := congrArg (eval x) (data.identity a)
    simpa [terminalFirstDerivativeProduct_eq_prod] using hid

/-- A genuine one-cluster backward propagation theorem. The fixed
localization coefficients are selected algebraically first; an inverse-power
lower bound obtained from the central quantitative-transfer theorem can then
be passed as `hcontractedLower`, and the evaluated localization step
propagates it to the terminal generators. -/
theorem TerminalGeneratorBackwardIdentity.terminal_lower_of_contracted_lower
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate R h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {contractedGenerator : Contracted → MvPolynomial (Fin h) R}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity R higher certificate
      contractedGenerator terminalGenerator)
    {X : Type w}
    (eval : X → TerminalMultiblockSourceRing R h higher (Fin h) →+* ℝ)
    {l : Filter X} {scale : X → ℝ}
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hfirst : ∀ d : Fin h,
      HasScalarInversePowerLowerBound l scale
        (fun x => eval x
          (MvPolynomial.X
            (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩))))
    (hcoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (fun x => eval x (data.coefficient a j)))
    (hcontractedLower : HasInversePowerLowerBound l scale
      (fun a x => eval x
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (contractedGenerator a)))) :
    HasInversePowerLowerBound l scale
      (fun j x => eval x (terminalGenerator j)) := by
  exact (data.denominatorClearedBackwardStep eval l scale hscale hfirst
    hcoefficient).propagate hcontractedLower

/-- End-to-end composition of one central quantitative-transfer call with
one evaluated terminal-localization step.  The `originalGenerator` family in
the transfer theorem is definitionally the evaluation of the fixed
contracted generators, so no generator-identification premise is hidden.
-/
theorem TerminalGeneratorBackwardIdentity.terminal_lower_of_realJet_transfer
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
    {Param : Type}
    [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    (w : Nat → Param) (x₀ : Param) (U : Set Param) (hx₀U : x₀ ∈ U)
    (hw : Tendsto w atTop (𝓝 x₀))
    (coefficientRepresentative : Fin transferCertificate.count →
      (RealJetTransferIndex m d →₀ Nat) → Param → ℝ)
    (hcoefficientAnalytic : ∀ a e,
      e ∈ (transferCertificate.source a).support →
        AnalyticOnNhd ℝ (coefficientRepresentative a e) U)
    (u : Fin (m + 1) → Nat → ℝ)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (Rscale Xscale : Nat → ℝ)
    {Central : Type} [Fintype Central] [Nonempty Central]
    (centralGenerator : Central → Nat → ℝ)
    (centralCoefficient :
      Central → Fin transferCertificate.count → Param → ℝ)
    (sourceCoefficient :
      Fin transferCertificate.count → Contracted → Param → ℝ)
    (hcentralCoefficientAnalytic : ∀ b a,
      AnalyticOnNhd ℝ (centralCoefficient b a) U)
    (hsourceCoefficientAnalytic : ∀ a j,
      AnalyticOnNhd ℝ (sourceCoefficient a j) U)
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
        ∑ a, centralCoefficient b a (w n) *
          realJetCoefficientwiseCentralEvaluation A d
            (fun e n => coefficientRepresentative a e (w n))
            u (transferCertificate.source a) n)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop,
      ∀ a : Fin transferCertificate.count,
        realJetCoefficientwiseSourceEvaluation d
            (fun e n => coefficientRepresentative a e (w n))
            u jets (transferCertificate.source a) n =
          ∑ j, sourceCoefficient a j (w n) *
            eval n
              (terminalMultiblockRetainedSourceHom R (Fin h) h higher
                (contractedGenerator j)))
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
    exact
      CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer_of_analyticRepresentatives
        d I transferCertificate hA w x₀ U hx₀U hw
        coefficientRepresentative hcoefficientAnalytic u hu jets
        Rscale Xscale centralGenerator centralCoefficient
        (fun j n => eval n
          (terminalMultiblockRetainedSourceHom R (Fin h) h higher
            (contractedGenerator j)))
        sourceCoefficient hcentralCoefficientAnalytic
        hsourceCoefficientAnalytic horder hpos hR hratios hscale hRX hX
        hEX Pweight hweight hmainBound hperturbedBound hcoordinateError
        hcentralIdentity hcentralLower hsourceIdentity
  exact data.terminal_lower_of_contracted_lower eval
    (hX.mono (fun _ hn => one_le_two.trans hn)) hfirst
    hlocalizationCoefficient hcontractedLower

end AbelFormalization
