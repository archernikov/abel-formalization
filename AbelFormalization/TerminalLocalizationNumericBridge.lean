import AbelFormalization.TerminalTimeQuantitativeBridge

/-!
# Numeric terminal-localization transport

The algebraic terminal-localization identity is normally evaluated by a ring
homomorphism on the whole coefficient ring.  Applications only use the
resulting finitely many real-valued functions.  This module exposes that
coefficientwise interface: callers may supply those numeric functions and the
eventual evaluated identity directly, without constructing a global sequence-
valued evaluation homomorphism.

The proof is exactly one application of `DenominatorClearedBackwardStep`.
Thus the theorem retains the same explicit analytic inputs: a lower bound for
each first derivative, polynomial upper bounds for the fixed localization
coefficients, and a lower bound for the contracted family.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped BigOperators

universe u v

/-- Propagate a lower bound through a terminal localization identity using
only the numeric values of the finitely many terms in that identity.

`hidentity` is the exact residual evaluation seam: it says that the supplied
numeric functions are an eventual evaluation of `data.identity`.  No ring
homomorphism on `R` or on the terminal multiblock polynomial ring is needed.
-/
theorem TerminalGeneratorBackwardIdentity.terminal_lower_of_numeric_identity
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate R h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {contractedGenerator : Contracted → MvPolynomial (Fin h) R}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing R h higher (Fin h)}
    (_data : TerminalGeneratorBackwardIdentity R higher certificate
      contractedGenerator terminalGenerator)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (contractedValue : Contracted → X → ℝ)
    (terminalValue : Terminal → X → ℝ)
    (firstDerivativeValue : Fin h → X → ℝ)
    (localizationCoefficientValue : Contracted → Terminal → X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hfirst : ∀ d,
      HasScalarInversePowerLowerBound l scale (firstDerivativeValue d))
    (hcoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (localizationCoefficientValue a j))
    (hidentity : ∀ᶠ x in l, ∀ a : Contracted,
      (∏ d, firstDerivativeValue d x) ^
          certificate.denominatorExponent * contractedValue a x =
        ∑ j, localizationCoefficientValue a j x * terminalValue j x)
    (hcontractedLower :
      HasInversePowerLowerBound l scale contractedValue) :
    HasInversePowerLowerBound l scale terminalValue := by
  let step : DenominatorClearedBackwardStep (Derivative := Fin h)
      l scale contractedValue terminalValue := {
    firstDerivative := firstDerivativeValue
    exponent := certificate.denominatorExponent
    coefficient := localizationCoefficientValue
    scale_ge_one := hscale
    firstDerivative_lower := hfirst
    coefficient_bound :=
      hasUniformPolynomialUpperBound_of_finite
        localizationCoefficientValue hscale hcoefficient
    identity := hidentity
  }
  exact step.propagate hcontractedLower

namespace ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

/-- Numeric specialization of terminal localization for the last displayed
central step.  The contracted family is indexed by the chosen padded time-
ideal presentation, while the output family is indexed by the displayed
terminal central generators.

This is deliberately independent of any particular real-jet evaluation.
Concrete Hermite data need only identify its numeric functions and prove the
single eventual identity below.
-/
theorem terminal_lower_of_numeric_time_lower
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
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (timeValue : Fin (localization.time.count + 1) → X → ℝ)
    (terminalValue : Fin (data.central.count + 1) → X → ℝ)
    (firstDerivativeValue : Fin h → X → ℝ)
    (localizationCoefficientValue :
      Fin (localization.time.count + 1) →
        Fin (data.central.count + 1) → X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hfirst : ∀ d,
      HasScalarInversePowerLowerBound l scale (firstDerivativeValue d))
    (hcoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (localizationCoefficientValue a j))
    (hidentity :
      ∀ᶠ x in l, ∀ a : Fin (localization.time.count + 1),
        (∏ d, firstDerivativeValue d x) ^
            certificate.terminalized.denominatorExponent * timeValue a x =
          ∑ j, localizationCoefficientValue a j x * terminalValue j x)
    (htimeLower : HasInversePowerLowerBound l scale timeValue) :
    HasInversePowerLowerBound l scale terminalValue := by
  exact localization.identity.terminal_lower_of_numeric_identity
    timeValue terminalValue firstDerivativeValue localizationCoefficientValue
    hscale hfirst hcoefficient hidentity htimeLower

end ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
end AbelFormalization
