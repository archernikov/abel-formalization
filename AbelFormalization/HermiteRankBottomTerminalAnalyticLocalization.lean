import AbelFormalization.HermiteRankBottomAnalyticChangeQuantitativeSeed
import AbelFormalization.TerminalLocalizationAnalyticAdapter

/-!
# Analytic terminal localization at the bottom Hermite stage

Cluster zero has an empty smaller-prefix block, but its coefficient ring is
still presented as a polynomial ring over analytic germs.  The canonical
zero-prefix equivalence removes this empty layer.  Mapping the fixed
denominator-cleared localization identity through that equivalence produces
a finite polynomial identity directly over analytic germs, to which the
finite analytic representative machinery applies.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open Filter Set
open scoped BigOperators Topology

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

variable {ι : Type*}
variable {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
variable {data : RepresentativeClusterSubsequence time}
variable {S : Finset (ι × ℕ)}
variable {I : Ideal (MvPolynomial
  (PaperRankRetainedSymbols m
    (m * (paperRankHermitePositiveDerivativeCount S + 1)))
  (RealAnalyticGerm p))}

/-- The last central generators of cluster zero after removing the empty
prefix coefficient layer. -/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTerminalGeneratorOverGerms
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (j : Fin (trace.bottomLastDisplayed.central.count + 1)) :
    TerminalMultiblockSourceRing (RealAnalyticGerm p)
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) :=
  let e0 := data.orderedClusterPrefixRingZeroAlgEquiv
    (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
  let eR : data.OrderedClusterPrefixRing
      (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 ≃ₐ[ℝ]
        RealAnalyticGerm p := e0.restrictScalars ℝ
  MvPolynomial.map eR.toRingHom
    (trace.bottomLastDisplayed.central.generator j)

/-- The fixed localization coefficient polynomials after the same
zero-prefix coefficient equivalence. -/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLocalizationCoefficientOverGerms
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    (a : Fin (localization.time.count + 1))
    (j : Fin (trace.bottomLastDisplayed.central.count + 1)) :
    TerminalMultiblockSourceRing (RealAnalyticGerm p)
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) :=
  let e0 := data.orderedClusterPrefixRingZeroAlgEquiv
    (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
  let eR : data.OrderedClusterPrefixRing
      (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 ≃ₐ[ℝ]
        RealAnalyticGerm p := e0.restrictScalars ℝ
  MvPolynomial.map eR.toRingHom (localization.identity.coefficient a j)

/-- The denominator-cleared mapped time generator that forms the target
family of the bottom terminal change of generators. -/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomClearedTimeTargetOverGerms
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    (a : Fin (localization.time.count + 1)) :
    TerminalMultiblockSourceRing (RealAnalyticGerm p)
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) :=
  terminalFirstDerivativeProduct (RealAnalyticGerm p)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S) ^
        (trace.descent.stageAt 0
          data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
    terminalMultiblockRetainedSourceHom (RealAnalyticGerm p)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (trace.bottomTimeGeneratorOverGerms localization.time a)

/-- Mapping the stored localization identity through the zero-prefix
coefficient equivalence preserves its literal denominator-cleared form. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomClearedTimeTargetOverGerms_eq_sum
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    (a : Fin (localization.time.count + 1)) :
    trace.bottomClearedTimeTargetOverGerms localization a =
      ∑ j, trace.bottomLocalizationCoefficientOverGerms localization a j *
        trace.bottomTerminalGeneratorOverGerms j := by
  let e0 := data.orderedClusterPrefixRingZeroAlgEquiv
    (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
  let eR : data.OrderedClusterPrefixRing
      (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 ≃ₐ[ℝ]
        RealAnalyticGerm p := e0.restrictScalars ℝ
  have h := congrArg (MvPolynomial.map eR.toRingHom)
    (localization.identity.identity a)
  simpa [bottomClearedTimeTargetOverGerms,
    bottomLocalizationCoefficientOverGerms,
    bottomTerminalGeneratorOverGerms, bottomTimeGeneratorOverGerms,
    terminalFirstDerivativeProduct_eq_prod,
    terminalMultiblockRetainedSourceHom, MvPolynomial.map_rename,
    eR, e0] using h

/-- The mapped denominator-cleared time targets lie in the span of the
mapped last-central generators. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomClearedTimeTarget_span_le
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData) :
    Ideal.span (Set.range
        (trace.bottomClearedTimeTargetOverGerms localization)) ≤
      Ideal.span (Set.range trace.bottomTerminalGeneratorOverGerms) := by
  apply Ideal.span_le.2
  rintro q ⟨a, rfl⟩
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨trace.bottomLocalizationCoefficientOverGerms localization a, ?_⟩
  exact (trace.bottomClearedTimeTargetOverGerms_eq_sum localization a).symm

/-- Canonical finite analytic change-of-generators data for the mapped
terminal-localization identity. -/
noncomputable def
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTerminalAnalyticChangeData
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData) :
    FiniteAnalyticChangeOfGeneratorsData
      (0 : RestrictedBoxSpace p)
      trace.bottomTerminalGeneratorOverGerms
      (trace.bottomClearedTimeTargetOverGerms localization) :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    trace.bottomTerminalGeneratorOverGerms
    (trace.bottomClearedTimeTargetOverGerms localization)
    (trace.bottomClearedTimeTarget_span_le localization)

/-- The chosen cleared-target representative agrees eventually with the
literal product of the first-derivative variables and the already chosen
bottom time representative. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomClearedTargetRepresentative_eventually_eq
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    (a : Fin (localization.time.count + 1)) :
    (trace.bottomTerminalAnalyticChangeData localization).targetRepresentative a
      =ᶠ[𝓝 (0 : RestrictedBoxSpace p)]
      fun y ↦
        terminalFirstDerivativeProduct ℝ
            (Fin (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
            (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
            (fun _ : Fin (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
                paperRankHermiteHigherCount S) ^
              (trace.descent.stageAt 0
                data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
          MvPolynomial.rename Sum.inr
            ((trace.bottomTimeAnalyticChangeData localization.time).sourceRepresentative
              a y) := by
  let terminalChange := trace.bottomTerminalAnalyticChangeData localization
  let timeChange := trace.bottomTimeAnalyticChangeData localization.time
  let h : ℕ := (data.orderedCluster
    ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
  let higher : Fin h → ℕ := fun _ ↦ paperRankHermiteHigherCount S
  let exponent := (trace.descent.stageAt 0
    data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent
  let explicitRepresentative : RestrictedBoxSpace p →
      TerminalMultiblockSourceRing ℝ h higher (Fin h) := fun y ↦
    terminalFirstDerivativeProduct ℝ (Fin h) h higher ^ exponent *
      MvPolynomial.rename Sum.inr (timeChange.sourceRepresentative a y)
  have hretained :
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (terminalMultiblockRetainedSourceHom (RealAnalyticGerm p) (Fin h)
            h higher (trace.bottomTimeGeneratorOverGerms localization.time a)) =
        ((fun y ↦ MvPolynomial.rename
            (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h))
            (timeChange.sourceRepresentative a y)) :
          Germ (𝓝 (0 : RestrictedBoxSpace p))
            (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
    change analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (MvPolynomial.rename
          (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h))
          (trace.bottomTimeGeneratorOverGerms localization.time a)) = _
    exact analyticPolynomialGermHom_rename_of (0 : RestrictedBoxSpace p)
      (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h))
      (timeChange.source_germ_eq a)
  have hexplicit :
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (trace.bottomClearedTimeTargetOverGerms localization a) =
        (explicitRepresentative : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
    change analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (terminalFirstDerivativeProduct (RealAnalyticGerm p) (Fin h) h higher ^
          exponent * terminalMultiblockRetainedSourceHom
            (RealAnalyticGerm p) (Fin h) h higher
              (trace.bottomTimeGeneratorOverGerms localization.time a)) = _
    rw [map_mul, map_pow,
      analyticPolynomialGermHom_terminalFirstDerivativeProduct, hretained]
    exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun y ↦ rfl)
  exact analyticPolynomialRepresentatives_eventually_eq
    (0 : RestrictedBoxSpace p)
    (terminalChange.target_germ_eq a) hexplicit rfl

/-- Along a convergent parameter family, the chosen cleared target evaluates
to the denominator product times the already chosen bottom time value. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomClearedTargetValue_eventually_eq
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    {X : Type} {l : Filter X}
    (parameter : X → RestrictedBoxSpace p)
    (hparameter : Tendsto parameter l (𝓝 (0 : RestrictedBoxSpace p)))
    (symbolValue : TerminalMultiblockSourceIndex
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) → X → ℝ) :
    ∀ᶠ n in l, ∀ a : Fin (localization.time.count + 1),
      (trace.bottomTerminalAnalyticChangeData localization).targetValue
          parameter symbolValue a n =
        (∏ d : Fin (data.orderedCluster
            ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
          symbolValue
            (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n) ^
            (trace.descent.stageAt 0
              data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
          (trace.bottomTimeAnalyticChangeData localization.time).sourceValue
            parameter (fun i n ↦ symbolValue (Sum.inr i) n) a n := by
  have hrepresentative : ∀ᶠ n in l,
      ∀ a : Fin (localization.time.count + 1),
        (trace.bottomTerminalAnalyticChangeData localization).targetRepresentative a
            (parameter n) =
          terminalFirstDerivativeProduct ℝ
              (Fin (data.orderedCluster
                ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
              (data.orderedCluster
                ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
              (fun _ : Fin (data.orderedCluster
                ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
                  paperRankHermiteHigherCount S) ^
                (trace.descent.stageAt 0
                  data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
            MvPolynomial.rename Sum.inr
              ((trace.bottomTimeAnalyticChangeData localization.time).sourceRepresentative
                a (parameter n)) := by
    apply Filter.eventually_all.mpr
    intro a
    exact hparameter.eventually
      (trace.bottomClearedTargetRepresentative_eventually_eq localization a)
  filter_upwards [hrepresentative] with n hn
  intro a
  simp only [FiniteAnalyticChangeOfGeneratorsData.targetValue, hn a,
    map_mul, map_pow, terminalFirstDerivativeProduct_eq_prod,
    map_prod, MvPolynomial.eval_X, MvPolynomial.eval_rename,
    Function.comp_def,
    FiniteAnalyticChangeOfGeneratorsData.sourceValue]

/-- The bottom nonzero polynomial and the derivative lower bounds give a
lower bound for the chosen cleared target family. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomClearedTargetValue_lower
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameter : X → RestrictedBoxSpace p)
    (symbolValue : TerminalMultiblockSourceIndex
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) → X → ℝ)
    (hparameter : Tendsto parameter l (𝓝 (0 : RestrictedBoxSpace p)))
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hretained : ∀ i,
      HasPolynomialUpperBound l scale (fun n ↦ symbolValue (Sum.inr i) n))
    (htime : Tendsto
      (fun n ↦ symbolValue (Sum.inr trace.bottomIndex) n) l atTop)
    (hfirst : ∀ d : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
      HasScalarInversePowerLowerBound l scale
        (fun n ↦ symbolValue
          (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n)) :
    HasInversePowerLowerBound l scale
      ((trace.bottomTerminalAnalyticChangeData localization).targetValue
        parameter symbolValue) := by
  let timeValue :=
    (trace.bottomTimeAnalyticChangeData localization.time).sourceValue
      parameter (fun i n ↦ symbolValue (Sum.inr i) n)
  have htimeLower : HasInversePowerLowerBound l scale timeValue :=
    trace.bottomTimeSourceValue_lower localization.time parameter
      (fun i n ↦ symbolValue (Sum.inr i) n) hparameter hscale hretained htime
  have hproduct : HasScalarInversePowerLowerBound l scale
      (fun n ↦ ∏ d : Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
        symbolValue
          (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n) := by
    simpa using hasScalarInversePowerLowerBound_finset_prod
      (Finset.univ : Finset (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card))
      (fun d n ↦ symbolValue
        (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n)
      hscale (fun d _hd ↦ hfirst d)
  have hpower := hproduct.pow hscale
    (trace.descent.stageAt 0
      data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent
  have hleft : HasInversePowerLowerBound l scale
      (fun a n ↦
        (∏ d : Fin (data.orderedCluster
            ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
          symbolValue
            (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n) ^
              (trace.descent.stageAt 0
                data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
          timeValue a n) :=
    hpower.mul_family hscale htimeLower
  have heq : ∀ᶠ n in l, ∀ a,
      (fun a n ↦
        (∏ d : Fin (data.orderedCluster
            ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
          symbolValue
            (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n) ^
              (trace.descent.stageAt 0
                data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.denominatorExponent *
          timeValue a n) a n =
        (trace.bottomTerminalAnalyticChangeData localization).targetValue
          parameter symbolValue a n := by
    filter_upwards [trace.bottomClearedTargetValue_eventually_eq localization
      parameter hparameter symbolValue] with n hn
    intro a
    exact (hn a).symm
  exact hleft.congr_of_eventually heq

/-- End-to-end bottom terminal seed using only finite analytic
representatives.  Both the bottom span identity and the terminal localization
identity, as well as all localization coefficient bounds, are discharged
internally. -/
theorem
    PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTerminalSourceValue_lower
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (localization : trace.bottomLastDisplayed.TerminalLocalizationData)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameter : X → RestrictedBoxSpace p)
    (symbolValue : TerminalMultiblockSourceIndex
      (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
      (fun _ : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
          paperRankHermiteHigherCount S)
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card) → X → ℝ)
    (hparameter : Tendsto parameter l (𝓝 (0 : RestrictedBoxSpace p)))
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hsymbol : ∀ z, HasPolynomialUpperBound l scale (symbolValue z))
    (htime : Tendsto
      (fun n ↦ symbolValue (Sum.inr trace.bottomIndex) n) l atTop)
    (hfirst : ∀ d : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
      HasScalarInversePowerLowerBound l scale
        (fun n ↦ symbolValue
          (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩) n)) :
    HasInversePowerLowerBound l scale
      ((trace.bottomTerminalAnalyticChangeData localization).sourceValue
        parameter symbolValue) := by
  exact (trace.bottomTerminalAnalyticChangeData localization).sourceValue_lower_of_targetValue_lower
      parameter hparameter symbolValue
      hscale hsymbol
      (trace.bottomClearedTargetValue_lower localization parameter symbolValue
        hparameter hscale (fun i ↦ hsymbol (Sum.inr i)) htime hfirst)

end RepresentativeClusterSubsequence
end AbelFormalization
