import AbelFormalization.FiniteAnalyticNestedChangeOfGenerators
import AbelFormalization.TerminalLocalizationNumericBridge
import AbelFormalization.TerminalLocalizationAnalyticAdapter
import AbelFormalization.TransferLowerBoundTransport

/-!
# Finite analytic transport from a coefficient ideal to a terminal family

At a non-bottom ordered-cluster stage the incoming prefix ideal is the
coefficient ideal of that stage's terminalized certificate.  This module
constructs the two finite analytic changes needed to cross that boundary:

* coefficient-ideal generators, embedded as constants, are expressed in a
  finite family spanning the terminal time ideal;
* the denominator-cleared time generators are expressed in the displayed
  last central family.

The quantitative consumer evaluates only the finitely many representatives
selected by those two changes.  It does not require an evaluation map from
the whole analytic-germ coefficient ring to sequences.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v

namespace RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily

/-- Regard one padded generating family as a presentation of an equal ideal.
This keeps its index type and literal generators unchanged, which is useful
at a dependent ordered-cluster boundary. -/
def castIdeal
    {R : Type u} [CommRing R] {I J : Ideal R}
    (family : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily R I)
    (hIJ : I = J) :
    RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily R J where
  count := family.count
  generator := family.generator
  span_eq := family.span_eq.trans hIJ

end RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily

namespace FiniteAnalyticNestedChangeOfGeneratorsData

/-- Quantitative finite change of generators in a nested polynomial ring.
This is the sequence-level consumer of the flattened analytic adapter. -/
theorem sourceValue_lower_of_targetValue_lower
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type} {Coeff : Type v}
    {Source Target : Type}
    [Fintype Source] [Nonempty Source]
    [Fintype Target] [Nonempty Target]
    {x : E}
    {source : Source →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
    {target : Target →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : Outer → X → ℝ)
    (coefficientValue : Coeff → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (houter : ∀ i, HasPolynomialUpperBound l scale (outerValue i))
    (hcoefficient : ∀ j,
      HasPolynomialUpperBound l scale (coefficientValue j))
    (htarget : HasInversePowerLowerBound l scale
      (data.targetValue parameter outerValue coefficientValue)) :
    HasInversePowerLowerBound l scale
      (data.sourceValue parameter outerValue coefficientValue) := by
  exact FiniteAnalyticChangeOfGeneratorsData.sourceValue_lower_of_targetValue_lower
    data parameter hparameter (Sum.elim outerValue coefficientValue) hscale
    (by
      rintro (i | j)
      · exact houter i
      · exact hcoefficient j) htarget

end FiniteAnalyticNestedChangeOfGeneratorsData

namespace ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Coeff : Type v}
variable {x : E}
variable {h : ℕ} {higher : Fin h → ℕ}
variable {I : Ideal (MvPolynomial
  (Fin h ⊕ CentralPolynomialIndex (Fin h)
    (terminalTotalDerivativeCount higher) (Fin h))
  (MvPolynomial Coeff (AnalyticGermAt x)))}
variable {certificate : ClusterAlgebraicReductionCertificate
  (MvPolynomial Coeff (AnalyticGermAt x)) h higher I}
variable {transferData : certificate.FullCentralTransferData}

/-- Embed a displayed coefficient-ideal family as constant time
polynomials. -/
def coefficientIdealTimeTarget
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal)
    (b : Fin (coefficientFamily.count + 1)) :
    MvPolynomial (Fin h) (MvPolynomial Coeff (AnalyticGermAt x)) :=
  MvPolynomial.C (coefficientFamily.generator b)

/-- The embedded coefficient-ideal family lies in the terminal time ideal. -/
theorem coefficientIdealTimeTarget_span_le
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal) :
    Ideal.span (Set.range (coefficientIdealTimeTarget coefficientFamily)) ≤
      Ideal.span (Set.range localization.time.generator) := by
  rw [localization.time.span_eq]
  apply Ideal.span_le.2
  rintro _ ⟨b, rfl⟩
  let g := coefficientFamily.generator b
  have hb : g ∈
      certificate.terminalized.coefficientIdeal := by
    exact coefficientFamily.span_eq.le Ideal.mem_span_range_self
  have hb' : g ∈ certificate.terminalized.timeIdeal.comap MvPolynomial.C := by
    rw [← certificate.terminalized.coefficient_eq]
    exact hb
  change MvPolynomial.C g ∈ certificate.terminalized.timeIdeal
  exact hb'

/-- Canonical finite analytic representatives for transporting a numeric
lower bound from coefficient generators to terminal time generators. -/
noncomputable def coefficientIdealTimeAnalyticChange
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal) :
    FiniteAnalyticNestedChangeOfGeneratorsData x
      localization.time.generator
      (coefficientIdealTimeTarget coefficientFamily) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan x
    localization.time.generator
    (coefficientIdealTimeTarget coefficientFamily)
    (coefficientIdealTimeTarget_span_le data localization coefficientFamily)

/-- The denominator-cleared retained image of one terminal time generator. -/
def clearedTimeTarget
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (a : Fin (localization.time.count + 1)) :
    TerminalMultiblockSourceRing
      (MvPolynomial Coeff (AnalyticGermAt x)) h higher (Fin h) :=
  terminalFirstDerivativeProduct
        (MvPolynomial Coeff (AnalyticGermAt x)) (Fin h) h higher ^
      certificate.terminalized.denominatorExponent *
    terminalMultiblockRetainedSourceHom
      (MvPolynomial Coeff (AnalyticGermAt x)) (Fin h) h higher
      (localization.time.generator a)

/-- Every cleared time generator lies in the displayed last central span. -/
theorem clearedTimeTarget_span_le
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData) :
    Ideal.span (Set.range (clearedTimeTarget data localization)) ≤
      Ideal.span (Set.range data.central.generator) := by
  apply Ideal.span_le.2
  rintro _ ⟨a, rfl⟩
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  exact ⟨localization.identity.coefficient a,
    (localization.identity.identity a).symm⟩

/-- Canonical finite analytic representatives for the localization-cleared
change from the displayed last central family to the time family. -/
noncomputable def terminalAnalyticChange
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData) :
    FiniteAnalyticNestedChangeOfGeneratorsData x
      data.central.generator (clearedTimeTarget data localization) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan x
    data.central.generator (clearedTimeTarget data localization)
    (clearedTimeTarget_span_le data localization)

/-- The only numeric compatibility needed between the two independently
chosen finite analytic changes and an incoming concrete coefficient family.

The first field identifies the incoming values with the target
representatives of the coefficient-to-time change.  The second identifies
the cleared target representatives with the product of first derivatives
and the time-source representatives. -/
structure TerminalCoefficientNumericCompatibility
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal)
    {X : Type v} (l : Filter X)
    (parameter : X → E)
    (timeValue : Fin h → X → ℝ)
    (coefficientValue : Coeff → X → ℝ)
    (terminalSymbolValue :
      TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (incomingValue : Fin (coefficientFamily.count + 1) → X → ℝ) : Prop where
  incoming_eq : ∀ᶠ n in l, ∀ b,
    incomingValue b n =
      (coefficientIdealTimeAnalyticChange data localization coefficientFamily).targetValue
        parameter timeValue coefficientValue b n
  cleared_eq : ∀ᶠ n in l, ∀ a,
    (terminalAnalyticChange data localization).targetValue parameter
        terminalSymbolValue coefficientValue a n =
      (∏ d : Fin h, terminalSymbolValue
          (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n) ^
          certificate.terminalized.denominatorExponent *
        (coefficientIdealTimeAnalyticChange data localization coefficientFamily).sourceValue
          parameter timeValue coefficientValue a n

/-- Transport an incoming coefficient-family lower bound through the time
ideal and the denominator-cleared localization span.  All coefficient bounds
and both finite linear-combination identities come from the two canonical
analytic changes. -/
theorem terminalAnalyticSourceValue_lower_of_coefficientValue_lower
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E)
    (timeValue : Fin h → X → ℝ)
    (coefficientValue : Coeff → X → ℝ)
    (terminalSymbolValue :
      TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (incomingValue : Fin (coefficientFamily.count + 1) → X → ℝ)
    (hparameter : Tendsto parameter l (𝓝 x))
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (htime : ∀ i, HasPolynomialUpperBound l scale (timeValue i))
    (hcoefficient : ∀ i,
      HasPolynomialUpperBound l scale (coefficientValue i))
    (hterminal : ∀ i,
      HasPolynomialUpperBound l scale (terminalSymbolValue i))
    (hfirst : ∀ d : Fin h,
      HasScalarInversePowerLowerBound l scale
        (fun n ↦ terminalSymbolValue
          (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n))
    (compatibility : TerminalCoefficientNumericCompatibility data localization
      coefficientFamily l parameter timeValue coefficientValue
      terminalSymbolValue incomingValue)
    (hincoming : HasInversePowerLowerBound l scale incomingValue) :
    HasInversePowerLowerBound l scale
      ((terminalAnalyticChange data localization).sourceValue parameter
        terminalSymbolValue coefficientValue) := by
  have hcoefficientTarget : HasInversePowerLowerBound l scale
      ((coefficientIdealTimeAnalyticChange data localization coefficientFamily).targetValue
        parameter timeValue coefficientValue) :=
    hincoming.congr_of_eventually compatibility.incoming_eq
  have htimeLower : HasInversePowerLowerBound l scale
      ((coefficientIdealTimeAnalyticChange data localization coefficientFamily).sourceValue
        parameter timeValue coefficientValue) :=
    (coefficientIdealTimeAnalyticChange data localization coefficientFamily).sourceValue_lower_of_targetValue_lower
      parameter hparameter timeValue coefficientValue hscale htime hcoefficient
      hcoefficientTarget
  have hproduct : HasScalarInversePowerLowerBound l scale
      (fun n ↦ ∏ d : Fin h,
        terminalSymbolValue
          (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n) := by
    simpa using hasScalarInversePowerLowerBound_finset_prod
      (Finset.univ : Finset (Fin h))
      (fun d n ↦ terminalSymbolValue
        (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n)
      hscale (fun d _hd ↦ hfirst d)
  have hpower := hproduct.pow hscale
    certificate.terminalized.denominatorExponent
  have hcleared : HasInversePowerLowerBound l scale
      ((terminalAnalyticChange data localization).targetValue parameter
        terminalSymbolValue coefficientValue) := by
    have hleft := hpower.mul_family hscale htimeLower
    apply hleft.congr_of_eventually
    filter_upwards [compatibility.cleared_eq] with n hn
    intro a
    exact (hn a).symm
  exact (terminalAnalyticChange data localization).sourceValue_lower_of_targetValue_lower
    parameter hparameter terminalSymbolValue coefficientValue hscale hterminal
    hcoefficient hcleared

/-- Final callback form for a concrete simultaneous trace.  Besides the
numeric compatibility above, the caller identifies the selected source
representatives of the displayed last central family with the corrected
terminal simultaneous values. -/
theorem terminalValue_lower_of_coefficientValue_lower
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E)
    (timeValue : Fin h → X → ℝ)
    (coefficientValue : Coeff → X → ℝ)
    (terminalSymbolValue :
      TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (incomingValue : Fin (coefficientFamily.count + 1) → X → ℝ)
    (terminalValue : Fin (data.central.count + 1) → X → ℝ)
    (hparameter : Tendsto parameter l (𝓝 x))
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (htime : ∀ i, HasPolynomialUpperBound l scale (timeValue i))
    (hcoefficient : ∀ i,
      HasPolynomialUpperBound l scale (coefficientValue i))
    (hterminal : ∀ i,
      HasPolynomialUpperBound l scale (terminalSymbolValue i))
    (hfirst : ∀ d : Fin h,
      HasScalarInversePowerLowerBound l scale
        (fun n ↦ terminalSymbolValue
          (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n))
    (compatibility : TerminalCoefficientNumericCompatibility data localization
      coefficientFamily l parameter timeValue coefficientValue
      terminalSymbolValue incomingValue)
    (hterminalValue : ∀ᶠ n in l, ∀ j,
      (terminalAnalyticChange data localization).sourceValue parameter
          terminalSymbolValue coefficientValue j n = terminalValue j n)
    (hincoming : HasInversePowerLowerBound l scale incomingValue) :
    HasInversePowerLowerBound l scale terminalValue := by
  exact (terminalAnalyticSourceValue_lower_of_coefficientValue_lower data
    localization coefficientFamily parameter timeValue coefficientValue
    terminalSymbolValue incomingValue hparameter hscale htime hcoefficient
    hterminal hfirst compatibility hincoming).congr_of_eventually hterminalValue

/-- Cross-boundary form allowing the incoming individual-boundary lower and
the next cluster's terminal simultaneous values to use different scales.
An eventual domination of the former scale by the latter is the sole scale
compatibility required. -/
theorem terminalValue_lower_of_coefficientValue_lower_of_scale_le
    (data : FullCentralStepDisplayedData transferData
      (Fin.last certificate.terminalized.extraSteps))
    (localization : data.TerminalLocalizationData)
    (coefficientFamily :
      RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
        (MvPolynomial Coeff (AnalyticGermAt x))
        certificate.terminalized.coefficientIdeal)
    {X : Type v} {l : Filter X}
    (incomingScale terminalScale : X → ℝ)
    (parameter : X → E)
    (timeValue : Fin h → X → ℝ)
    (coefficientValue : Coeff → X → ℝ)
    (terminalSymbolValue :
      TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (incomingValue : Fin (coefficientFamily.count + 1) → X → ℝ)
    (terminalValue : Fin (data.central.count + 1) → X → ℝ)
    (hparameter : Tendsto parameter l (𝓝 x))
    (hincomingScale : ∀ᶠ n in l, 1 ≤ incomingScale n)
    (hscaleLe : ∀ᶠ n in l, incomingScale n ≤ terminalScale n)
    (hterminalScale : ∀ᶠ n in l, 1 ≤ terminalScale n)
    (htime : ∀ i,
      HasPolynomialUpperBound l terminalScale (timeValue i))
    (hcoefficient : ∀ i,
      HasPolynomialUpperBound l terminalScale (coefficientValue i))
    (hterminal : ∀ i,
      HasPolynomialUpperBound l terminalScale (terminalSymbolValue i))
    (hfirst : ∀ d : Fin h,
      HasScalarInversePowerLowerBound l terminalScale
        (fun n ↦ terminalSymbolValue
          (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n))
    (compatibility : TerminalCoefficientNumericCompatibility data localization
      coefficientFamily l parameter timeValue coefficientValue
      terminalSymbolValue incomingValue)
    (hterminalValue : ∀ᶠ n in l, ∀ j,
      (terminalAnalyticChange data localization).sourceValue parameter
          terminalSymbolValue coefficientValue j n = terminalValue j n)
    (hincoming : HasInversePowerLowerBound l incomingScale incomingValue) :
    HasInversePowerLowerBound l terminalScale terminalValue := by
  have hincoming' : HasInversePowerLowerBound l terminalScale incomingValue :=
    hasInversePowerLowerBound_mono_scale hincomingScale hscaleLe hincoming
  exact terminalValue_lower_of_coefficientValue_lower data localization
    coefficientFamily parameter timeValue coefficientValue terminalSymbolValue
    incomingValue terminalValue hparameter hterminalScale htime hcoefficient
    hterminal hfirst compatibility hterminalValue hincoming'

end ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

end AbelFormalization
