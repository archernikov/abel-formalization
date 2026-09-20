import AbelFormalization.BottomPolynomialQuantitativeSeed
import AbelFormalization.OrderedClusterSimultaneousRealJetEvaluation
import AbelFormalization.SeparatedDenominatorStep

/-!
# Quantitative bridge from a terminal time ideal to the last central family

The bottom polynomial gives a lower bound on a finite family spanning a
terminalized cluster's time ideal.  The localization identities already in
the algebraic certificate turn this into a lower bound on the final central
family.  This module packages that exact bridge and proves that the last
displayed central output is the stored terminal ideal, including when there
are no extra retained steps.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Topology

universe u

namespace ClusterAlgebraicReductionCertificate

/-- The output of the last full central operation is the terminal ideal of
the stored cluster certificate. -/
theorem centralTransferOutput_last
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I) :
    certificate.centralTransferOutput
        (Fin.last certificate.terminalized.extraSteps) =
      certificate.terminalized.terminalIdeal := by
  have hgeneral : ∀
      (r : Fin (certificate.terminalized.extraSteps + 1)),
      r.val = certificate.terminalized.extraSteps →
      certificate.centralTransferOutput r =
        certificate.terminalized.terminalIdeal := by
    intro r
    refine Fin.cases ?_ (fun k ↦ ?_) r
    · intro hr
      have hzero : certificate.terminalized.extraSteps = 0 := hr.symm
      simpa [centralTransferOutput, hzero] using
        certificate.terminalized.centralIterationIdeal_extraSteps
    · intro hr
      simpa [centralTransferOutput, ← hr] using
        certificate.terminalized.centralIterationIdeal_extraSteps
  exact hgeneral _ rfl

end ClusterAlgebraicReductionCertificate

/-- Central real-jet evaluation restricts along the retained-variable
inclusion to ordinary evaluation of the time polynomial at `A (u i)`. -/
theorem finiteRealJetCentralEvaluationHom_retainedSourceHom
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    (A : ℝ → ℝ) (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ)
    (P : MvPolynomial (Fin h) R) (n : ℕ) :
    finiteRealJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount higher) n
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher P) =
      MvPolynomial.eval₂Hom coefficientEval
        (fun i n ↦ A (u i n)) P n := by
  rw [mvPolynomial_eval₂Hom_pi_apply]
  unfold finiteRealJetCentralEvaluationHom
  change MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
      (realCentralTransferCentralValue A (fun i ↦ u i n)
        (terminalTotalDerivativeCount higher))
      (MvPolynomial.rename Sum.inr P) = _
  rw [MvPolynomial.eval₂Hom_rename]
  rfl

namespace ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

/-- A finite time-ideal presentation together with the fixed localization
identity relating it to the displayed output of the last central step. -/
structure TerminalLocalizationData
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps)) where
  time : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (MvPolynomial (Fin h) R) certificate.terminalized.timeIdeal
  identity : TerminalGeneratorBackwardIdentity R higher
    certificate.terminalized time.generator data.central.generator

/-- Noetherianity chooses the time family and the localization identity for
the already displayed last central family. -/
theorem nonempty_terminalLocalizationData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps)) :
    Nonempty data.TerminalLocalizationData := by
  let time := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      (MvPolynomial (Fin h) R) certificate.terminalized.timeIdeal)
  have hterminal : Ideal.span (Set.range data.central.generator) =
      certificate.terminalized.terminalIdeal :=
    data.central.span_eq.trans certificate.centralTransferOutput_last
  let identity := Classical.choice
    (certificate.terminalized.nonempty_terminalGeneratorBackwardIdentity
      time.generator data.central.generator time.span_eq hterminal)
  exact ⟨{ time := time, identity := identity }⟩

/-- An evaluated lower bound for the time ideal propagates through the fixed
terminal localization identity to the displayed last central family. -/
theorem terminal_lower_of_time_lower
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (A : ℝ → ℝ) (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ) (scale : ℕ → ℝ)
    (timeLower : EvaluatedPaddedIdealLowerBound (Fin h) atTop scale
      coefficientEval (fun i n ↦ A (u i n))
      certificate.terminalized.timeIdeal)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop scale (coefficientEval r))
    (htimeCoordinate : ∀ i,
      HasPolynomialUpperBound atTop scale (fun n ↦ A (u i n)))
    (hfirst : ∀ i : Fin h,
      HasScalarInversePowerLowerBound atTop scale
        (fun n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
          (terminalTotalDerivativeCount higher) n
          (MvPolynomial.X
            (Sum.inl ⟨i, (0 : Fin (higher i + 1))⟩))))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound atTop scale
        (fun n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
          (terminalTotalDerivativeCount higher) n
          (localization.identity.coefficient a j))) :
    HasInversePowerLowerBound atTop scale
      (fun j n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount higher) n
        (data.central.generator j)) := by
  let eval := fun n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
    (terminalTotalDerivativeCount higher) n
  have htime : HasInversePowerLowerBound atTop scale
      (fun a n ↦ MvPolynomial.eval₂Hom coefficientEval
        (fun i n ↦ A (u i n)) (localization.time.generator a) n) :=
    timeLower.lower_of_span_eq localization.time.generator
      localization.time.span_eq hscale hcoefficient htimeCoordinate
  have hcontracted : HasInversePowerLowerBound atTop scale
      (fun a n ↦ eval n
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (localization.time.generator a))) := by
    simpa only [eval,
      finiteRealJetCentralEvaluationHom_retainedSourceHom] using htime
  exact localization.identity.terminal_lower_of_contracted_lower eval
    hscale hfirst hlocalizationCoefficient hcontracted

end ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
end AbelFormalization
