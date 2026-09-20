import AbelFormalization.AnalyticPolynomialEvaluationBounds
import AbelFormalization.HermiteRankBottomTerminalQuantitativeSeed
import AbelFormalization.TerminalLocalizationNumericBridge

/-!
# Numeric quantitative seed from the bottom polynomial

The existing bottom seed evaluates every element of the analytic-germ
coefficient ring through one sequence-valued ring homomorphism.  The actual
argument only needs finitely many numeric values.  This module isolates that
smaller interface.

First, a nonzero univariate polynomial lower bound is transferred through an
eventual finite linear-combination identity.  The paper-specific adapter then
chooses the exact span coefficients supplied by `bottomEmbedding_mem` and
allows callers to represent only those finitely many coefficient polynomials.
The final theorem composes this numeric time-ideal seed with the numeric
terminal-localization bridge; no global evaluation homomorphism is present.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Polynomial Topology BigOperators

universe u v

/-- A nonzero scalar polynomial evaluated along a diverging coordinate gives
an inverse-power lower bound for any nonempty finite family into which it has
an eventual polynomially bounded numeric linear-combination expansion. -/
theorem hasInversePowerLowerBound_of_nonzeroPolynomial_linearCombination
    {X ι : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter X} {scale : X → ℝ}
    (familyValue : ι → X → ℝ)
    (coefficientValue : ι → X → ℝ)
    (timeValue : X → ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ i,
      HasPolynomialUpperBound l scale (coefficientValue i))
    (htime : Tendsto timeValue l atTop)
    (hidentity : ∀ᶠ x in l,
      P.eval (timeValue x) =
        ∑ i, coefficientValue i x * familyValue i x) :
    HasInversePowerLowerBound l scale familyValue := by
  let targetValue : Fin 1 → X → ℝ :=
    fun _ x ↦ P.eval (timeValue x)
  let coefficientMatrix : Fin 1 → ι → X → ℝ :=
    fun _ i ↦ coefficientValue i
  apply hasInversePowerLowerBound_of_linearCombinations
    familyValue targetValue coefficientMatrix hscale
  · filter_upwards [hidentity] with x hx
    intro b
    simpa only [targetValue, coefficientMatrix] using hx
  · apply hasUniformPolynomialUpperBound_of_finite coefficientMatrix hscale
    intro b i
    exact hcoefficient i
  · exact nonzeroPolynomial_hasInversePowerLowerBound P hP htime scale

namespace RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily

/-- Fixed algebraic coefficients expressing one member of the ideal in the
chosen padded generating family. -/
noncomputable def spanCoefficientOfMem
    {R : Type u} [CommRing R] {I : Ideal R}
    (family : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily R I)
    (q : R) (hq : q ∈ I) : Fin (family.count + 1) → R :=
  Classical.choose (Ideal.mem_span_range_iff_exists_fun.mp (by
    rw [family.span_eq]
    exact hq))

/-- The coefficients chosen by `spanCoefficientOfMem` satisfy the literal
finite linear-combination identity. -/
theorem sum_spanCoefficientOfMem_mul_generator
    {R : Type u} [CommRing R] {I : Ideal R}
    (family : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily R I)
    (q : R) (hq : q ∈ I) :
    ∑ i, family.spanCoefficientOfMem q hq i * family.generator i = q :=
  Classical.choose_spec (Ideal.mem_span_range_iff_exists_fun.mp (by
    rw [family.span_eq]
    exact hq))

end RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily

namespace RepresentativeClusterSubsequence

variable {ι : Type*}

/-- The exact coefficients expressing the stored bottom scalar polynomial in
an arbitrary padded presentation of the literal bottom time ideal. -/
noncomputable def PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeSpanCoefficient
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal) :
    Fin (family.count + 1) →
      MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0) :=
  family.spanCoefficientOfMem
    (scalarUnivariateEmbedding ℝ
      (data.OrderedClusterPrefixRing
        (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
      trace.bottomIndex trace.bottomPolynomial)
    trace.bottomEmbedding_mem

/-- Literal algebraic identity underlying the numeric bottom seed. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomEmbedding_eq_sum_spanCoefficient
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal) :
    scalarUnivariateEmbedding ℝ
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
        trace.bottomIndex trace.bottomPolynomial =
      ∑ k, trace.bottomTimeSpanCoefficient family k * family.generator k := by
  exact (family.sum_spanCoefficientOfMem_mul_generator
    (scalarUnivariateEmbedding ℝ
      (data.OrderedClusterPrefixRing
        (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
      trace.bottomIndex trace.bottomPolynomial)
    trace.bottomEmbedding_mem).symm

/-- Coefficientwise bottom seed for the literal padded time family.  The
coefficient functions are numeric values of the exact finite family selected
by `bottomTimeSpanCoefficient`; `hidentity` is the sole evaluation seam. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeLower_of_numeric_identity
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (timeValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (familyValue : Fin (family.count + 1) → X → ℝ)
    (coefficientValue : Fin (family.count + 1) → X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ k,
      HasPolynomialUpperBound l scale (coefficientValue k))
    (htime : Tendsto (timeValue trace.bottomIndex) l atTop)
    (hidentity : ∀ᶠ x in l,
      trace.bottomPolynomial.eval (timeValue trace.bottomIndex x) =
        ∑ k, coefficientValue k x * familyValue k x) :
    HasInversePowerLowerBound l scale familyValue := by
  exact hasInversePowerLowerBound_of_nonzeroPolynomial_linearCombination
    familyValue coefficientValue (timeValue trace.bottomIndex)
      trace.bottomPolynomial trace.bottomPolynomial_ne hscale hcoefficient
      htime hidentity

/-- Map the exact bottom span coefficient through the canonical coefficient
equivalence at prefix zero, obtaining a polynomial over analytic germs. -/
noncomputable def PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeSpanCoefficientOverGerms
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal)
    (k : Fin (family.count + 1)) :
    MvPolynomial
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
      (RealAnalyticGerm p) :=
  MvPolynomial.map
    (data.orderedClusterPrefixRingZeroAlgEquiv
      (RealAnalyticGerm p) (paperRankHermiteHigherCount S)).toRingHom
    (trace.bottomTimeSpanCoefficient family k)

/-- Finite analytic representatives for exactly the span coefficients chosen
from `bottomEmbedding_mem`. -/
structure PaperRankHermiteTopPrefixPreprocessedTraceData.BottomTimeSpanCoefficientRepresentatives
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal) where
  representative : Fin (family.count + 1) → RestrictedBoxSpace p →
    MvPolynomial
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) ℝ
  neighborhood : _root_.Set (RestrictedBoxSpace p)
  neighborhood_open : IsOpen neighborhood
  origin_mem : (0 : RestrictedBoxSpace p) ∈ neighborhood
  support_subset : ∀ k w,
    (representative k w).support ⊆
      (trace.bottomTimeSpanCoefficientOverGerms family k).support
  coefficient_analytic : ∀ k e,
    AnalyticOnNhd ℝ (fun w ↦ (representative k w).coeff e) neighborhood
  germ_eq : ∀ k,
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (trace.bottomTimeSpanCoefficientOverGerms family k) =
      (representative k : Germ
        (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial
          (Fin (data.orderedCluster
            ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) ℝ))

/-- The exact finite bottom span coefficients always have simultaneous
analytic representatives on one neighborhood of the origin. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.nonempty_bottomTimeSpanCoefficientRepresentatives
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal) :
    Nonempty (trace.BottomTimeSpanCoefficientRepresentatives family) := by
  obtain ⟨representative, neighborhood, hopen, horigin, hsupport,
      hanalytic, hgerm⟩ := exists_analyticPolynomialRepresentatives
        (0 : RestrictedBoxSpace p)
        (trace.bottomTimeSpanCoefficientOverGerms family)
  exact ⟨{
    representative := representative
    neighborhood := neighborhood
    neighborhood_open := hopen
    origin_mem := horigin
    support_subset := hsupport
    coefficient_analytic := hanalytic
    germ_eq := hgerm
  }⟩

/-- Analytic-representative form of the numeric bottom seed.  Polynomial
bounds for the finite span coefficients are derived from their analytic
representatives and polynomial bounds for the time coordinates.  The only
remaining compatibility assumption is the eventual evaluated identity. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeLower_of_analytic_spanCoefficientRepresentatives
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (family : PaddedIdealGeneratorFamily
      (MvPolynomial
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0))
      (trace.descent.stageAt 0
        data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal)
    (representatives : trace.BottomTimeSpanCoefficientRepresentatives family)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameterValue : X → RestrictedBoxSpace p)
    (timeValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (familyValue : Fin (family.count + 1) → X → ℝ)
    (hparameter : Tendsto parameterValue l
      (𝓝 (0 : RestrictedBoxSpace p)))
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoordinate : ∀ i,
      HasPolynomialUpperBound l scale (timeValue i))
    (htime : Tendsto (timeValue trace.bottomIndex) l atTop)
    (hidentity : ∀ᶠ x in l,
      trace.bottomPolynomial.eval (timeValue trace.bottomIndex x) =
        ∑ k,
          MvPolynomial.eval (fun i ↦ timeValue i x)
              (representatives.representative k (parameterValue x)) *
            familyValue k x) :
    HasInversePowerLowerBound l scale familyValue := by
  apply trace.bottomTimeLower_of_numeric_identity family timeValue familyValue
    (fun k x ↦ MvPolynomial.eval (fun i ↦ timeValue i x)
      (representatives.representative k (parameterValue x)))
    hscale
  · intro k
    exact analyticMvPolynomialEvaluation_hasPolynomialUpperBound
      (representatives.representative k)
      (trace.bottomTimeSpanCoefficientOverGerms family k).support
      representatives.neighborhood (0 : RestrictedBoxSpace p)
      representatives.origin_mem parameterValue hparameter
      (representatives.support_subset k)
      (fun e _ ↦ representatives.coefficient_analytic k e)
      timeValue hscale hcoordinate
  · exact htime
  · exact hidentity

/-- Fully numeric paper-specific bottom-to-terminal seed.  It composes the
stored bottom-polynomial membership with the displayed terminal localization.
Both residual identities mention only finitely many supplied real-valued
functions. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLastCentralLower_of_numeric_identities
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (coordinateValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (timeGeneratorValue : Fin (localization.time.count + 1) → X → ℝ)
    (bottomCoefficientValue : Fin (localization.time.count + 1) → X → ℝ)
    (terminalValue : Fin (trace.bottomLastDisplayed.central.count + 1) →
      X → ℝ)
    (firstDerivativeValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (localizationCoefficientValue :
      Fin (localization.time.count + 1) →
        Fin (trace.bottomLastDisplayed.central.count + 1) → X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hbottomCoefficient : ∀ k,
      HasPolynomialUpperBound l scale (bottomCoefficientValue k))
    (htime : Tendsto (coordinateValue trace.bottomIndex) l atTop)
    (hbottomIdentity : ∀ᶠ x in l,
      trace.bottomPolynomial.eval (coordinateValue trace.bottomIndex x) =
        ∑ k, bottomCoefficientValue k x * timeGeneratorValue k x)
    (hfirst : ∀ d,
      HasScalarInversePowerLowerBound l scale (firstDerivativeValue d))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (localizationCoefficientValue a j))
    (hlocalizationIdentity :
      ∀ᶠ x in l, ∀ a : Fin (localization.time.count + 1),
        (∏ d, firstDerivativeValue d x) ^
            (trace.descent.stageAt 0
              data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
              timeGeneratorValue a x =
          ∑ j, localizationCoefficientValue a j x * terminalValue j x) :
    HasInversePowerLowerBound l scale terminalValue := by
  have htimeLower : HasInversePowerLowerBound l scale timeGeneratorValue :=
    trace.bottomTimeLower_of_numeric_identity localization.time
      coordinateValue timeGeneratorValue bottomCoefficientValue hscale
      hbottomCoefficient htime hbottomIdentity
  exact trace.bottomLastDisplayed.terminal_lower_of_numeric_time_lower
    localization timeGeneratorValue terminalValue firstDerivativeValue
      localizationCoefficientValue hscale hfirst hlocalizationCoefficient
      hlocalizationIdentity htimeLower

/-- Paper-specific terminal seed with automatically bounded bottom span
coefficients.  Callers provide analytic representatives only for the exact
finite coefficients selected from `bottomEmbedding_mem`, plus the two
eventual evaluated identities. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLastCentralLower_of_analytic_bottomCoefficients
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    (representatives :
      trace.BottomTimeSpanCoefficientRepresentatives localization.time)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameterValue : X → RestrictedBoxSpace p)
    (coordinateValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (timeGeneratorValue : Fin (localization.time.count + 1) → X → ℝ)
    (terminalValue : Fin (trace.bottomLastDisplayed.central.count + 1) →
      X → ℝ)
    (firstDerivativeValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (localizationCoefficientValue :
      Fin (localization.time.count + 1) →
        Fin (trace.bottomLastDisplayed.central.count + 1) → X → ℝ)
    (hparameter : Tendsto parameterValue l
      (𝓝 (0 : RestrictedBoxSpace p)))
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoordinate : ∀ i,
      HasPolynomialUpperBound l scale (coordinateValue i))
    (htime : Tendsto (coordinateValue trace.bottomIndex) l atTop)
    (hbottomIdentity : ∀ᶠ x in l,
      trace.bottomPolynomial.eval (coordinateValue trace.bottomIndex x) =
        ∑ k,
          MvPolynomial.eval (fun i ↦ coordinateValue i x)
              (representatives.representative k (parameterValue x)) *
            timeGeneratorValue k x)
    (hfirst : ∀ d,
      HasScalarInversePowerLowerBound l scale (firstDerivativeValue d))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (localizationCoefficientValue a j))
    (hlocalizationIdentity :
      ∀ᶠ x in l, ∀ a : Fin (localization.time.count + 1),
        (∏ d, firstDerivativeValue d x) ^
            (trace.descent.stageAt 0
              data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
              timeGeneratorValue a x =
          ∑ j, localizationCoefficientValue a j x * terminalValue j x) :
    HasInversePowerLowerBound l scale terminalValue := by
  have htimeLower : HasInversePowerLowerBound l scale timeGeneratorValue :=
    trace.bottomTimeLower_of_analytic_spanCoefficientRepresentatives
      localization.time representatives parameterValue coordinateValue
      timeGeneratorValue hparameter hscale hcoordinate htime hbottomIdentity
  exact trace.bottomLastDisplayed.terminal_lower_of_numeric_time_lower
    localization timeGeneratorValue terminalValue firstDerivativeValue
      localizationCoefficientValue hscale hfirst hlocalizationCoefficient
      hlocalizationIdentity htimeLower

end RepresentativeClusterSubsequence
end AbelFormalization
