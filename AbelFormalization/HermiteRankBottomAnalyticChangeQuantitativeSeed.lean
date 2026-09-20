import AbelFormalization.FiniteAnalyticChangeOfGenerators
import AbelFormalization.HermiteRankBottomNumericQuantitativeSeed

/-!
# Analytic change of generators at the bottom time ideal

The bottom polynomial belongs to the padded time ideal over the zero-prefix
coefficient ring.  After the canonical zero-prefix coefficient equivalence,
that membership is a finite change of generators over real-analytic germs.
`FiniteAnalyticChangeOfGeneratorsData` supplies simultaneous representatives
and makes the evaluated span identity automatic on one common neighborhood.

Consequently the bottom-to-terminal quantitative seed below has only the
terminal-localization evaluation identity as a residual compatibility input.
No evaluation map on the whole analytic-germ ring, and no separately assumed
bottom span identity, is used.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped BigOperators Polynomial Topology

namespace AbelFormalization

universe u

/-- The scalar univariate polynomial over analytic germs is represented by
the literal constant polynomial-valued function. -/
theorem analyticPolynomialGermHom_scalarUnivariateEmbedding
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (x : E) (i : Fin d) (P : ℝ[X]) :
    analyticPolynomialGermHom x
        (scalarUnivariateEmbedding ℝ (AnalyticGermAt x) i P) =
      ((fun _ : E => P.toMvPolynomial i) :
        Germ (𝓝 x) (MvPolynomial (Fin d) ℝ)) := by
  classical
  let Q : MvPolynomial (Fin d) ℝ := P.toMvPolynomial i
  have hinjective : Function.Injective
      (algebraMap ℝ (AnalyticGermAt x)) :=
    FaithfulSMul.algebraMap_injective ℝ (AnalyticGermAt x)
  have hsupport :
      (scalarUnivariateEmbedding ℝ (AnalyticGermAt x) i P).support =
        Q.support := by
    exact MvPolynomial.support_map_of_injective Q hinjective
  have h := analyticPolynomialGermHom_eq_coefficientRepresentative x
    (scalarUnivariateEmbedding ℝ (AnalyticGermAt x) i P)
    (fun e _ => Q.coeff e)
    (fun _ => analyticAt_const) (by
      intro e _he
      change algebraMap ℝ (AnalyticGermAt x) (Q.coeff e) =
        analyticGermOf (fun _ => Q.coeff e) analyticAt_const
      exact analyticGerm_algebraMap x (Q.coeff e))
  rw [h]
  apply Germ.coe_eq.mpr
  filter_upwards [] with y
  rw [polynomialFromCoefficientRepresentatives, hsupport]
  exact MvPolynomial.support_sum_monomial_coeff Q

namespace RepresentativeClusterSubsequence

variable {ι : Type*}

/-- The padded bottom time generators after removing the empty zero-prefix
polynomial layer from their coefficient ring. -/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeGeneratorOverGerms
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
    (family.generator k)

/-- Singleton target family containing the nonzero bottom scalar polynomial,
now regarded as a polynomial over real-analytic germs. -/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomPolynomialTargetOverGerms
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (_ : Fin 1) :
    MvPolynomial
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
      (RealAnalyticGerm p) :=
  scalarUnivariateEmbedding ℝ (RealAnalyticGerm p)
    trace.bottomIndex trace.bottomPolynomial

/-- The stored bottom ideal membership becomes a literal singleton-target
change-of-generators identity over analytic germs. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomPolynomialTargetOverGerms_eq_sum
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
    (b : Fin 1) :
    trace.bottomPolynomialTargetOverGerms b =
      ∑ k, trace.bottomTimeSpanCoefficientOverGerms family k *
        trace.bottomTimeGeneratorOverGerms family k := by
  let e0 := data.orderedClusterPrefixRingZeroAlgEquiv
    (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
  let eR : data.OrderedClusterPrefixRing
      (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 ≃ₐ[ℝ]
        RealAnalyticGerm p := e0.restrictScalars ℝ
  have hcomp : eR.toRingHom.comp
      (algebraMap ℝ (data.OrderedClusterPrefixRing
        (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)) =
      algebraMap ℝ (RealAnalyticGerm p) := by
    apply RingHom.ext
    intro r
    exact eR.commutes r
  have hleft : MvPolynomial.map eR.toRingHom
      (scalarUnivariateEmbedding ℝ
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
        trace.bottomIndex trace.bottomPolynomial) =
      scalarUnivariateEmbedding ℝ (RealAnalyticGerm p)
        trace.bottomIndex trace.bottomPolynomial := by
    simp only [scalarUnivariateEmbedding, RingHom.comp_apply,
      MvPolynomial.map_map, hcomp]
  have h := congrArg (MvPolynomial.map eR.toRingHom)
    (trace.bottomEmbedding_eq_sum_spanCoefficient family)
  rw [hleft] at h
  simpa [bottomPolynomialTargetOverGerms, bottomTimeGeneratorOverGerms,
    bottomTimeSpanCoefficientOverGerms, eR, e0] using h

/-- Span inclusion used by the finite analytic adapter. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomPolynomialTarget_span_le
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
    Ideal.span (Set.range trace.bottomPolynomialTargetOverGerms) ≤
      Ideal.span (Set.range
        (trace.bottomTimeGeneratorOverGerms family)) := by
  apply Ideal.span_le.2
  rintro q ⟨b, rfl⟩
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨trace.bottomTimeSpanCoefficientOverGerms family, ?_⟩
  exact (trace.bottomPolynomialTargetOverGerms_eq_sum family b).symm

/-- Canonical simultaneous representatives for the mapped padded bottom time
family, the singleton scalar-polynomial target, and their coefficient matrix.
-/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeAnalyticChangeData
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
    FiniteAnalyticChangeOfGeneratorsData (0 : RestrictedBoxSpace p)
      (trace.bottomTimeGeneratorOverGerms family)
      trace.bottomPolynomialTargetOverGerms :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan (0 : RestrictedBoxSpace p)
    (trace.bottomTimeGeneratorOverGerms family)
    trace.bottomPolynomialTargetOverGerms
    (trace.bottomPolynomialTarget_span_le family)

/-- The chosen target representative agrees eventually with the literal
constant scalar polynomial.  This is derived from germ equality and is not a
compatibility assumption on callers. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTargetRepresentative_eventually_eq
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
    (b : Fin 1) :
    (trace.bottomTimeAnalyticChangeData family).targetRepresentative b =ᶠ[
        𝓝 (0 : RestrictedBoxSpace p)]
      fun _ => trace.bottomPolynomial.toMvPolynomial trace.bottomIndex := by
  apply analyticPolynomialRepresentatives_eventually_eq
    (0 : RestrictedBoxSpace p)
    ((trace.bottomTimeAnalyticChangeData family).target_germ_eq b)
    (analyticPolynomialGermHom_scalarUnivariateEmbedding
      (0 : RestrictedBoxSpace p) trace.bottomIndex trace.bottomPolynomial)
  rfl

/-- The evaluated singleton target supplied by the analytic adapter inherits
the lower bound of the stored nonzero bottom polynomial. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTargetValue_lower
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
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameterValue : X → RestrictedBoxSpace p)
    (coordinateValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (hparameter : Tendsto parameterValue l
      (𝓝 (0 : RestrictedBoxSpace p)))
    (htime : Tendsto (coordinateValue trace.bottomIndex) l atTop) :
    HasInversePowerLowerBound l scale
      ((trace.bottomTimeAnalyticChangeData family).targetValue
        parameterValue coordinateValue) := by
  let change := trace.bottomTimeAnalyticChangeData family
  have heq : ∀ᶠ n in l, ∀ b : Fin 1,
      change.targetValue parameterValue coordinateValue b n =
        trace.bottomPolynomial.eval
          (coordinateValue trace.bottomIndex n) := by
    have hrepresentative : ∀ᶠ n in l, ∀ b : Fin 1,
        change.targetRepresentative b (parameterValue n) =
          trace.bottomPolynomial.toMvPolynomial trace.bottomIndex := by
      apply Filter.eventually_all.mpr
      intro b
      exact hparameter.eventually
        (trace.bottomTargetRepresentative_eventually_eq family b)
    filter_upwards [hrepresentative] with n hn
    intro b
    rw [FiniteAnalyticChangeOfGeneratorsData.targetValue, hn b]
    exact MvPolynomial.eval_toMvPolynomial
      (fun i => coordinateValue i n) trace.bottomIndex
        trace.bottomPolynomial
  obtain ⟨c, hc, M, hlower⟩ :=
    nonzeroPolynomial_hasInversePowerLowerBound trace.bottomPolynomial
      trace.bottomPolynomial_ne htime scale
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hlower, heq] with n hn heqn
  have habs : c / scale n ^ M ≤
      |trace.bottomPolynomial.eval
        (coordinateValue trace.bottomIndex n)| := by
    simpa [finiteFamilyMaxAbs] using hn
  calc
    c / scale n ^ M ≤
        |trace.bottomPolynomial.eval
          (coordinateValue trace.bottomIndex n)| := habs
    _ = |change.targetValue parameterValue coordinateValue 0 n| := by
      rw [heqn 0]
    _ ≤ finiteFamilyMaxAbs
        (change.targetValue parameterValue coordinateValue) n :=
      abs_le_finiteFamilyMaxAbs _ _ 0

/-- The finite analytic change of generators transports the bottom
polynomial lower bound to the mapped padded time-generator representatives.
The evaluated span identity and coefficient bounds are discharged internally.
-/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeSourceValue_lower
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
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameterValue : X → RestrictedBoxSpace p)
    (coordinateValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (hparameter : Tendsto parameterValue l
      (𝓝 (0 : RestrictedBoxSpace p)))
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hcoordinate : ∀ i,
      HasPolynomialUpperBound l scale (coordinateValue i))
    (htime : Tendsto (coordinateValue trace.bottomIndex) l atTop) :
    HasInversePowerLowerBound l scale
      ((trace.bottomTimeAnalyticChangeData family).sourceValue
        parameterValue coordinateValue) := by
  let change := trace.bottomTimeAnalyticChangeData family
  exact change.sourceValue_lower_of_targetValue_lower parameterValue hparameter
      coordinateValue hscale hcoordinate
      (trace.bottomTargetValue_lower family parameterValue coordinateValue
        hparameter htime)

/-- Bottom-to-terminal seed with the bottom evaluated span identity produced
by the finite analytic adapter.  The displayed `hlocalizationIdentity` is the
only remaining numeric equality: it is the genuinely separate terminal
localization step. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLastCentralLower_of_analyticChange
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameterValue : X → RestrictedBoxSpace p)
    (coordinateValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (terminalValue : Fin (trace.bottomLastDisplayed.central.count + 1) →
      X → ℝ)
    (firstDerivativeValue : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (localizationCoefficientValue :
      Fin (localization.time.count + 1) →
        Fin (trace.bottomLastDisplayed.central.count + 1) → X → ℝ)
    (hparameter : Tendsto parameterValue l
      (𝓝 (0 : RestrictedBoxSpace p)))
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hcoordinate : ∀ i,
      HasPolynomialUpperBound l scale (coordinateValue i))
    (htime : Tendsto (coordinateValue trace.bottomIndex) l atTop)
    (hfirst : ∀ d,
      HasScalarInversePowerLowerBound l scale (firstDerivativeValue d))
    (hlocalizationCoefficient : ∀ a j,
      HasPolynomialUpperBound l scale
        (localizationCoefficientValue a j))
    (hlocalizationIdentity :
      ∀ᶠ n in l, ∀ a : Fin (localization.time.count + 1),
        (∏ d, firstDerivativeValue d n) ^
            (trace.descent.stageAt 0
              data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
              (trace.bottomTimeAnalyticChangeData localization.time).sourceValue
                parameterValue coordinateValue a n =
          ∑ j, localizationCoefficientValue a j n * terminalValue j n) :
    HasInversePowerLowerBound l scale terminalValue := by
  apply trace.bottomLastDisplayed.terminal_lower_of_numeric_time_lower
    localization
    ((trace.bottomTimeAnalyticChangeData localization.time).sourceValue
      parameterValue coordinateValue)
    terminalValue firstDerivativeValue localizationCoefficientValue hscale
      hfirst hlocalizationCoefficient hlocalizationIdentity
  exact trace.bottomTimeSourceValue_lower localization.time parameterValue
    coordinateValue hparameter hscale hcoordinate htime

end RepresentativeClusterSubsequence
end AbelFormalization
