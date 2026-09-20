import AbelFormalization.MaxwellOneSidedClusterCoverage
import AbelFormalization.MaxwellCompactComponentMembership
import AbelFormalization.ComponentZeroFiniteness

/-!
# WS5 extraction of Maxwell's equal-infinity affine chord

This module proves the geometric extraction used in the equal-infinity cases
of the first-order argument.  A family-member graph, WS5, and genuine
fixed-base infinite one-sided quotient limits yield the affine-chord crossing
mechanism consumed by `MaxwellSlopeClusterSmallness`.

The final source record deliberately exposes the remaining analytic gap:
the existing closure-based infinity loci provide moving-base reciprocal
sequences, whereas the chord proof needs fixed-base quotient limits at both
ends of the chord.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

def maxwellAffineChordGraphPoint {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (t : ℝ) :
    RealEuclidean (p + 1) :=
  AffineMap.lineMap
    (realEuclideanAppend a (fun _ : Fin 1 ↦ f a))
    (realEuclideanAppend b (fun _ : Fin 1 ↦ f b)) t

@[simp] theorem takeLeft_maxwellAffineChordGraphPoint {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (t : ℝ) :
    realEuclideanTakeLeft (maxwellAffineChordGraphPoint f a b t) =
      maxwellAffineChordPath a b t := by
  funext j
  simp [maxwellAffineChordGraphPoint, AffineMap.lineMap_apply_module,
    maxwellAffineChordPath, realEuclideanTakeLeft,
    realEuclideanAppend]
  ring

@[simp] theorem takeRight_maxwellAffineChordGraphPoint {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (t : ℝ) :
    realEuclideanTakeRight (maxwellAffineChordGraphPoint f a b t) =
      (fun _ : Fin 1 ↦ maxwellAffineChordValue f a b t) := by
  funext j
  simp [maxwellAffineChordGraphPoint, AffineMap.lineMap_apply_module,
    maxwellAffineChordValue, realEuclideanTakeRight,
    realEuclideanAppend]

theorem maxwellAffineChordGraphPoint_mem_graph_iff {p : ℕ}
    (W : Set (RealEuclidean p)) (f : RealEuclidean p → ℝ)
    (a b : RealEuclidean p) (t : ℝ) :
    maxwellAffineChordGraphPoint f a b t ∈
        maxwellFunctionGraph W (fun x _ ↦ f x) ↔
      maxwellAffineChordPath a b t ∈ W ∧
        maxwellAffineChordError f a b t = 0 := by
  rw [← realEuclideanAppend_takeLeft_takeRight
    (maxwellAffineChordGraphPoint f a b t)]
  rw [realEuclideanAppend_mem_maxwellFunctionGraph_iff]
  simp only [takeLeft_maxwellAffineChordGraphPoint, takeRight_maxwellAffineChordGraphPoint]
  constructor
  · rintro ⟨hW, h⟩
    refine ⟨hW, ?_⟩
    have h0 := congrFun h 0
    exact sub_eq_zero.mpr h0.symm
  · rintro ⟨hW, hzero⟩
    refine ⟨hW, ?_⟩
    funext j
    exact (sub_eq_zero.mp hzero).symm

theorem maxwellAffineChordGraphPoint_injective {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    Function.Injective (maxwellAffineChordGraphPoint f a b) := by
  apply AffineMap.lineMap_injective ℝ
  intro hab
  have hbase := congrArg realEuclideanTakeLeft hab
  simp only [realEuclideanTakeLeft_append] at hbase
  subst b
  have hi := congrFun hbase i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one] at hi
  linarith

def maxwellAffineChordLine {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) :
    AffineSubspace ℝ (RealEuclidean (p + 1)) :=
  affineSpan ℝ
    {realEuclideanAppend a (fun _ : Fin 1 ↦ f a),
      realEuclideanAppend b (fun _ : Fin 1 ↦ f b)}

theorem maxwellAffineChordGraphPoint_mem_line {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (t : ℝ) :
    maxwellAffineChordGraphPoint f a b t ∈ maxwellAffineChordLine f a b := by
  rw [maxwellAffineChordLine, mem_affineSpan_pair_iff_exists_lineMap_eq]
  exact ⟨t, rfl⟩

def MaxwellDirectSameInfinityLimitsOn {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (s : MaxwellSameInfinitySign) (W : Set (RealEuclidean p)) : Prop :=
  ∀ x ∈ W,
    Tendsto (fun t ↦ maxwellRightDifferenceQuotient f i x t)
      (𝓝[>] (0 : ℝ))
      (match s with
        | .positiveInfinity => atTop
        | .negativeInfinity => atBot) ∧
    Tendsto (fun t ↦ maxwellReflectedLeftDifferenceQuotient f i x t)
      (𝓝[>] (0 : ℝ))
      (match s with
        | .positiveInfinity => atTop
        | .negativeInfinity => atBot)

def maxwellAffineChordParameter {p : ℕ} (i : Fin p)
    (a : RealEuclidean p) (step : ℝ)
    (z : RealEuclidean (p + 1)) : ℝ :=
  (z (Fin.castAdd 1 i) - a i) / step

theorem maxwellAffineChordParameter_point {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    (t : ℝ) :
    maxwellAffineChordParameter i a step (maxwellAffineChordGraphPoint f a b t) = t := by
  change
    (realEuclideanTakeLeft (maxwellAffineChordGraphPoint f a b t) i - a i) /
        step = t
  rw [takeLeft_maxwellAffineChordGraphPoint]
  simp only [maxwellAffineChordPath, hb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one]
  field_simp
  ring

theorem continuous_maxwellAffineChordParameter {p : ℕ} (i : Fin p)
    (a : RealEuclidean p) (step : ℝ) :
    Continuous (maxwellAffineChordParameter i a step) := by
  have hcoord : Continuous
      (fun z : RealEuclidean (p + 1) ↦ z (Fin.castAdd 1 i)) :=
    continuous_apply (Fin.castAdd 1 i)
  exact (hcoord.sub continuous_const).div_const step

theorem maxwellAffineChordGraphPoint_parameter_eq_of_mem_line {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    {z : RealEuclidean (p + 1)} (hz : z ∈ maxwellAffineChordLine f a b) :
    maxwellAffineChordGraphPoint f a b (maxwellAffineChordParameter i a step z) = z := by
  rw [maxwellAffineChordLine, mem_affineSpan_pair_iff_exists_lineMap_eq] at hz
  obtain ⟨t, ht⟩ := hz
  rw [← ht]
  change maxwellAffineChordGraphPoint f a b
      (maxwellAffineChordParameter i a step (maxwellAffineChordGraphPoint f a b t)) =
    maxwellAffineChordGraphPoint f a b t
  rw [maxwellAffineChordParameter_point f i a b step hstep hb t]

theorem maxwellAffineChordPath_add_parameterStep {p : ℕ}
    (i : Fin p) (a b : RealEuclidean p) (step r t : ℝ)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    maxwellAffineChordPath a b r +
        ((t - r) * step) • (Pi.single i 1 : RealEuclidean p) =
      maxwellAffineChordPath a b t := by
  subst b
  simp only [maxwellAffineChordPath]
  module

theorem maxwellAffineChordPath_sub_parameterStep {p : ℕ}
    (i : Fin p) (a b : RealEuclidean p) (step r t : ℝ)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    maxwellAffineChordPath a b t -
        ((t - r) * step) • (Pi.single i 1 : RealEuclidean p) =
      maxwellAffineChordPath a b r := by
  rw [← maxwellAffineChordPath_add_parameterStep i a b step r t hb]
  abel

theorem maxwellAffineChordValue_sub {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (r t : ℝ) :
    maxwellAffineChordValue f a b t -
        maxwellAffineChordValue f a b r =
      (t - r) * (f b - f a) := by
  simp only [maxwellAffineChordValue]
  ring

theorem maxwellRightDifferenceQuotient_chord {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step r t : ℝ)
    (hstep : 0 < step) (hrt : r < t)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    (hr : maxwellAffineChordError f a b r = 0)
    (ht : maxwellAffineChordError f a b t = 0) :
    maxwellRightDifferenceQuotient f i
        (maxwellAffineChordPath a b r) ((t - r) * step) =
      (f b - f a) / step := by
  have hdelta : (t - r) * step ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hrt)) (ne_of_gt hstep)
  have htr : t - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hrt)
  rw [maxwellRightDifferenceQuotient,
    maxwellAffineChordPath_add_parameterStep i a b step r t hb]
  have hfr : f (maxwellAffineChordPath a b r) =
      maxwellAffineChordValue f a b r := sub_eq_zero.mp hr
  have hft : f (maxwellAffineChordPath a b t) =
      maxwellAffineChordValue f a b t := sub_eq_zero.mp ht
  rw [hfr, hft, maxwellAffineChordValue_sub]
  field_simp [htr, ne_of_gt hstep]

theorem maxwellReflectedLeftDifferenceQuotient_chord {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step r t : ℝ)
    (hstep : 0 < step) (hrt : r < t)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    (hr : maxwellAffineChordError f a b r = 0)
    (ht : maxwellAffineChordError f a b t = 0) :
    maxwellReflectedLeftDifferenceQuotient f i
        (maxwellAffineChordPath a b t) ((t - r) * step) =
      (f b - f a) / step := by
  have hdelta : (t - r) * step ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hrt)) (ne_of_gt hstep)
  have htr : t - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hrt)
  rw [maxwellReflectedLeftDifferenceQuotient,
    maxwellAffineChordPath_sub_parameterStep i a b step r t hb]
  have hfr : f (maxwellAffineChordPath a b r) =
      maxwellAffineChordValue f a b r := sub_eq_zero.mp hr
  have hft : f (maxwellAffineChordPath a b t) =
      maxwellAffineChordValue f a b t := sub_eq_zero.mp ht
  rw [hfr, hft, maxwellAffineChordValue_sub]
  field_simp [htr, ne_of_gt hstep]
  ring

theorem maxwellRightDifferenceQuotient_sub_chordSlope_eq {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step t : ℝ)
    (hstep : 0 < step) (ht : 0 < t)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    maxwellRightDifferenceQuotient f i a (t * step) -
        (f b - f a) / step =
      maxwellAffineChordError f a b t / (t * step) := by
  have hpath : a + (t * step) • (Pi.single i 1 : RealEuclidean p) =
      maxwellAffineChordPath a b t := by
    simpa [maxwellAffineChordPath] using
      maxwellAffineChordPath_add_parameterStep i a b step 0 t hb
  rw [maxwellRightDifferenceQuotient, hpath]
  simp only [maxwellAffineChordError, maxwellAffineChordValue]
  field_simp [ne_of_gt hstep, ne_of_gt ht]
  ring

theorem maxwellReflectedLeftDifferenceQuotient_sub_chordSlope_eq {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (a b : RealEuclidean p) (step t : ℝ)
    (hstep : 0 < step) (ht : t < 1)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    maxwellReflectedLeftDifferenceQuotient f i b ((1 - t) * step) -
        (f b - f a) / step =
      -maxwellAffineChordError f a b t / ((1 - t) * step) := by
  have hpath : b - ((1 - t) * step) •
        (Pi.single i 1 : RealEuclidean p) =
      maxwellAffineChordPath a b t := by
    simpa [maxwellAffineChordPath] using
      maxwellAffineChordPath_sub_parameterStep i a b step t 1 hb
  rw [maxwellReflectedLeftDifferenceQuotient, hpath]
  simp only [maxwellAffineChordError, maxwellAffineChordValue]
  field_simp [ne_of_gt hstep, ne_of_gt (sub_pos.mpr ht)]
  ring

theorem finite_graph_affineChordSection_of_ws5
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {p : ℕ} {W : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign}
    (hgraph : maxwellFunctionGraph W (fun x _ ↦ f x) ∈ C (p + 1))
    (hlimits : MaxwellDirectSameInfinityLimitsOn f i s W)
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    (maxwellFunctionGraph W (fun x _ ↦ f x) ∩
      (maxwellAffineChordLine f a b : Set (RealEuclidean (p + 1)))).Finite := by
  let G : Set (RealEuclidean (p + 1)) :=
    maxwellFunctionGraph W (fun x _ ↦ f x)
  let L : AffineSubspace ℝ (RealEuclidean (p + 1)) :=
    maxwellAffineChordLine f a b
  let M : Set (RealEuclidean (p + 1)) := G ∩ (L : Set _)
  obtain ⟨N, hN⟩ := hC.ws5_affineSections (by omega) hgraph
  have hcard : ENat.card (ConnectedComponents M) ≤ (N : ℕ∞) := by
    simpa only [M, G, L] using hN L
  have hfiniteComponents : Finite (ConnectedComponents M) := by
    rw [← ENat.card_lt_top]
    exact hcard.trans_lt (WithTop.coe_lt_top N)
  letI : Finite (ConnectedComponents M) := hfiniteComponents
  have hcomponent_lt_false : ∀ (x y : M),
      (x : ConnectedComponents M) = y →
      maxwellAffineChordParameter i a step x < maxwellAffineChordParameter i a step y → False := by
    intro x y hcomponent hxy
    let rx : ℝ := maxwellAffineChordParameter i a step x
    let ry : ℝ := maxwellAffineChordParameter i a step y
    have hxLine : (x : RealEuclidean (p + 1)) ∈ maxwellAffineChordLine f a b := by
      exact x.property.2
    have hyLine : (y : RealEuclidean (p + 1)) ∈ maxwellAffineChordLine f a b := by
      exact y.property.2
    have hxPoint : maxwellAffineChordGraphPoint f a b rx = x := by
      exact maxwellAffineChordGraphPoint_parameter_eq_of_mem_line
        f i a b step hstep hb hxLine
    have hyPoint : maxwellAffineChordGraphPoint f a b ry = y := by
      exact maxwellAffineChordGraphPoint_parameter_eq_of_mem_line
        f i a b step hstep hb hyLine
    have hxGraph : maxwellAffineChordGraphPoint f a b rx ∈ G := by
      rw [hxPoint]
      exact x.property.1
    have hyGraph : maxwellAffineChordGraphPoint f a b ry ∈ G := by
      rw [hyPoint]
      exact y.property.1
    have hxData : maxwellAffineChordPath a b rx ∈ W ∧
        maxwellAffineChordError f a b rx = 0 := by
      exact (maxwellAffineChordGraphPoint_mem_graph_iff W f a b rx).mp hxGraph
    have hyData : maxwellAffineChordPath a b ry ∈ W ∧
        maxwellAffineChordError f a b ry = 0 := by
      exact (maxwellAffineChordGraphPoint_mem_graph_iff W f a b ry).mp hyGraph
    let parameterOnM : M → ℝ := fun z ↦
      maxwellAffineChordParameter i a step z
    have hparameterContinuous : Continuous parameterOnM :=
      (continuous_maxwellAffineChordParameter i a step).comp continuous_subtype_val
    have hyComponent : y ∈ connectedComponent x :=
      (ConnectedComponents.coe_eq_coe').mp hcomponent.symm
    have hintermediate : Set.Icc rx ry ⊆
        parameterOnM '' connectedComponent x := by
      exact isPreconnected_connectedComponent.intermediate_value
        mem_connectedComponent hyComponent
        hparameterContinuous.continuousOn
    let chordSlope : ℝ := (f b - f a) / step
    have hright := (hlimits _ hxData.1).1
    have hseparate : ∀ᶠ h in 𝓝[>] (0 : ℝ),
        maxwellRightDifferenceQuotient f i
          (maxwellAffineChordPath a b rx) h ≠ chordSlope := by
      cases s with
      | positiveInfinity =>
          exact (hright.eventually_gt_atTop chordSlope).mono
            (fun _ hz hEq ↦ (not_lt_of_ge hEq.le) hz)
      | negativeInfinity =>
          exact (hright.eventually_lt_atBot chordSlope).mono
            (fun _ hz hEq ↦ (not_lt_of_ge hEq.ge) hz)
    have hgap : 0 < (ry - rx) * step := mul_pos (sub_pos.mpr hxy) hstep
    have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < (ry - rx) * step := by
      exact Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hgap)
    obtain ⟨h, hne, hhsmall, hhpos⟩ : ∃ h : ℝ,
        maxwellRightDifferenceQuotient f i
            (maxwellAffineChordPath a b rx) h ≠ chordSlope ∧
          h < (ry - rx) * step ∧ 0 < h := by
      have hexists := Filter.Eventually.exists
        (hseparate.and (hsmall.and self_mem_nhdsWithin))
      simpa only [Set.mem_Ioi] using hexists
    let r : ℝ := rx + h / step
    have hrx : rx < r := by
      dsimp only [r]
      exact lt_add_of_pos_right _ (div_pos hhpos hstep)
    have hry : r < ry := by
      dsimp only [r]
      have hdiv : h / step < ry - rx := by
        apply (div_lt_iff₀ hstep).2
        linarith
      linarith
    obtain ⟨z, hzComponent, hzParam⟩ :=
      hintermediate ⟨le_of_lt hrx, le_of_lt hry⟩
    have hzLine : (z : RealEuclidean (p + 1)) ∈ maxwellAffineChordLine f a b :=
      z.property.2
    have hzPoint : maxwellAffineChordGraphPoint f a b r = z := by
      have hcanonical := maxwellAffineChordGraphPoint_parameter_eq_of_mem_line
        f i a b step hstep hb hzLine
      rw [← hzParam]
      exact hcanonical
    have hzGraph : maxwellAffineChordGraphPoint f a b r ∈ G := by
      rw [hzPoint]
      exact z.property.1
    have hzError : maxwellAffineChordError f a b r = 0 :=
      ((maxwellAffineChordGraphPoint_mem_graph_iff W f a b r).mp hzGraph).2
    have hquotient := maxwellRightDifferenceQuotient_chord
      f i a b step rx r hstep hrx hb hxData.2 hzError
    have hactualStep : (r - rx) * step = h := by
      dsimp only [r]
      field_simp [ne_of_gt hstep]
      ring
    rw [hactualStep] at hquotient
    exact hne hquotient
  have hcomponentInjective : Function.Injective
      (ConnectedComponents.mk : M → ConnectedComponents M) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hparamNe : maxwellAffineChordParameter i a step x ≠
        maxwellAffineChordParameter i a step y := by
      intro heq
      have hxLine : (x : RealEuclidean (p + 1)) ∈ maxwellAffineChordLine f a b :=
        x.property.2
      have hyLine : (y : RealEuclidean (p + 1)) ∈ maxwellAffineChordLine f a b :=
        y.property.2
      have hxPoint := maxwellAffineChordGraphPoint_parameter_eq_of_mem_line
        f i a b step hstep hb hxLine
      have hyPoint := maxwellAffineChordGraphPoint_parameter_eq_of_mem_line
        f i a b step hstep hb hyLine
      apply hne
      rw [← hxPoint, ← hyPoint, heq]
    rcases lt_or_gt_of_ne hparamNe with hlt | hgt
    · exact hcomponent_lt_false x y hxy hlt
    · exact hcomponent_lt_false y x hxy.symm hgt
  letI : Finite M := Finite.of_injective ConnectedComponents.mk
    hcomponentInjective
  simpa only [M, G, L] using Set.toFinite M

def maxwellAffineChordZeroSet {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) : Set ℝ :=
  {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ maxwellAffineChordError f a b t = 0}

theorem finite_maxwellAffineChordZeroSet_of_finite_graphSection
    {p : ℕ} {W : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a b t ∈ W)
    (hfinite : (maxwellFunctionGraph W (fun x _ ↦ f x) ∩
      (maxwellAffineChordLine f a b : Set (RealEuclidean (p + 1)))).Finite) :
    (maxwellAffineChordZeroSet f a b).Finite := by
  have himage : (maxwellAffineChordGraphPoint f a b '' maxwellAffineChordZeroSet f a b).Finite := by
    apply hfinite.subset
    rintro z ⟨t, ht, rfl⟩
    refine ⟨?_, maxwellAffineChordGraphPoint_mem_line f a b t⟩
    rw [maxwellAffineChordGraphPoint_mem_graph_iff]
    exact ⟨hsegment t ht.1, ht.2⟩
  exact Set.Finite.of_finite_image himage
    (maxwellAffineChordGraphPoint_injective f i a b step hstep hb).injOn

theorem exists_first_positive_testChordZero
    {p : ℕ} (f : RealEuclidean p → ℝ) (a b : RealEuclidean p)
    (hfinite : (maxwellAffineChordZeroSet f a b).Finite) :
    ∃ v : ℝ, v ∈ maxwellAffineChordZeroSet f a b ∧ 0 < v ∧ v ≤ 1 ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) v,
        maxwellAffineChordError f a b t ≠ 0 := by
  let Zpos : Set ℝ := maxwellAffineChordZeroSet f a b ∩ Set.Ioi 0
  have hZposFinite : Zpos.Finite := hfinite.inter_of_left (Set.Ioi 0)
  have honeZero : (1 : ℝ) ∈ maxwellAffineChordZeroSet f a b := by
    constructor
    · exact ⟨by norm_num, by norm_num⟩
    · simp [maxwellAffineChordError, maxwellAffineChordPath,
        maxwellAffineChordValue]
  have honeZpos : (1 : ℝ) ∈ Zpos := ⟨honeZero, by norm_num⟩
  obtain ⟨v, hvZpos, hvmin⟩ :=
    Set.exists_min_image Zpos id hZposFinite ⟨1, honeZpos⟩
  have hvle : v ≤ 1 := by
    simpa using hvmin 1 honeZpos
  refine ⟨v, hvZpos.1, hvZpos.2, hvle, ?_⟩
  intro t ht hterror
  have htZpos : t ∈ Zpos := by
    refine ⟨⟨⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hvle⟩, hterror⟩,
      ht.1⟩
  have := hvmin t htZpos
  simp only [id_eq] at this
  exact (not_le_of_gt ht.2) this

theorem maxwellAffineChordPath_subchord {p : ℕ}
    (a b : RealEuclidean p) (v t : ℝ) :
    maxwellAffineChordPath a (maxwellAffineChordPath a b v) t =
      maxwellAffineChordPath a b (t * v) := by
  simp only [maxwellAffineChordPath]
  module

theorem maxwellAffineChordValue_subchord {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (v t : ℝ)
    (hv : maxwellAffineChordError f a b v = 0) :
    maxwellAffineChordValue f a (maxwellAffineChordPath a b v) t =
      maxwellAffineChordValue f a b (t * v) := by
  have hvf : f (maxwellAffineChordPath a b v) =
      maxwellAffineChordValue f a b v := sub_eq_zero.mp hv
  simp only [maxwellAffineChordValue]
  rw [hvf]
  simp only [maxwellAffineChordValue]
  ring

theorem maxwellAffineChordError_subchord {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p) (v t : ℝ)
    (hv : maxwellAffineChordError f a b v = 0) :
    maxwellAffineChordError f a (maxwellAffineChordPath a b v) t =
      maxwellAffineChordError f a b (t * v) := by
  simp only [maxwellAffineChordError, maxwellAffineChordPath_subchord]
  rw [maxwellAffineChordValue_subchord f a b v t hv]

theorem maxwellAffineChordPath_eq_add_smul {p : ℕ}
    (i : Fin p) (a b : RealEuclidean p) (step t : ℝ)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p)) :
    maxwellAffineChordPath a b t =
      a + (t * step) • (Pi.single i 1 : RealEuclidean p) := by
  subst b
  simp only [maxwellAffineChordPath]
  module

theorem exists_affineChordCrossingObstruction_of_directLimits
    {p : ℕ} {W : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign}
    (hlimits : MaxwellDirectSameInfinityLimitsOn f i s W)
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    (haW : a ∈ W) (hbW : b ∈ W)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a b t ∈ W)
    (hisolated : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      maxwellAffineChordError f a b t ≠ 0) :
    Nonempty (MaxwellAffineChordCrossingObstruction f i s W) := by
  let chordSlope : ℝ := (f b - f a) / step
  have hright := (hlimits a haW).1
  have hleft := (hlimits b hbW).2
  have horientedRight : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      maxwellInfinityChordOrientation s *
        (maxwellRightDifferenceQuotient f i a h - chordSlope) < 0 := by
    cases s with
    | positiveInfinity =>
        filter_upwards [hright.eventually_gt_atTop chordSlope] with h hh
        simp only [maxwellInfinityChordOrientation]
        linarith
    | negativeInfinity =>
        filter_upwards [hright.eventually_lt_atBot chordSlope] with h hh
        simp only [maxwellInfinityChordOrientation, one_mul]
        linarith
  have horientedLeft : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      maxwellInfinityChordOrientation s *
        (maxwellReflectedLeftDifferenceQuotient f i b h - chordSlope) < 0 := by
    cases s with
    | positiveInfinity =>
        filter_upwards [hleft.eventually_gt_atTop chordSlope] with h hh
        simp only [maxwellInfinityChordOrientation]
        linarith
    | negativeInfinity =>
        filter_upwards [hleft.eventually_lt_atBot chordSlope] with h hh
        simp only [maxwellInfinityChordOrientation, one_mul]
        linarith
  have hhalf : 0 < step / 2 := half_pos hstep
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < step / 2 :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hhalf)
  obtain ⟨hR, hhRorient, hhRsmall, hhRpos⟩ : ∃ h : ℝ,
      maxwellInfinityChordOrientation s *
          (maxwellRightDifferenceQuotient f i a h - chordSlope) < 0 ∧
        h < step / 2 ∧ 0 < h := by
    have hexists := Filter.Eventually.exists
      (horientedRight.and (hsmall.and self_mem_nhdsWithin))
    simpa only [Set.mem_Ioi] using hexists
  obtain ⟨hL, hhLorient, hhLsmall, hhLpos⟩ : ∃ h : ℝ,
      maxwellInfinityChordOrientation s *
          (maxwellReflectedLeftDifferenceQuotient f i b h - chordSlope) < 0 ∧
        h < step / 2 ∧ 0 < h := by
    have hexists := Filter.Eventually.exists
      (horientedLeft.and (hsmall.and self_mem_nhdsWithin))
    simpa only [Set.mem_Ioi] using hexists
  let u : ℝ := hR / step
  let v : ℝ := 1 - hL / step
  have hu : 0 < u := div_pos hhRpos hstep
  have huHalf : u < 1 / 2 := by
    dsimp only [u]
    apply (div_lt_iff₀ hstep).2
    nlinarith
  have hvHalf : 1 / 2 < v := by
    dsimp only [v]
    have hdiv : hL / step < 1 / 2 := by
      apply (div_lt_iff₀ hstep).2
      nlinarith
    linarith
  have hvOne : v < 1 := by
    dsimp only [v]
    exact sub_lt_self _ (div_pos hhLpos hstep)
  have huv : u < v := lt_trans huHalf hvHalf
  have huStep : u * step = hR := by
    dsimp only [u]
    field_simp [ne_of_gt hstep]
  have hvStep : (1 - v) * step = hL := by
    dsimp only [v]
    field_simp [ne_of_gt hstep]
    ring
  have hrightEq := maxwellRightDifferenceQuotient_sub_chordSlope_eq
    f i a b step u hstep hu hb
  have hrightDen : 0 < u * step := mul_pos hu hstep
  have hhRorient' : maxwellInfinityChordOrientation s *
      (maxwellRightDifferenceQuotient f i a (u * step) -
        (f b - f a) / step) < 0 := by
    rw [huStep]
    simpa only [chordSlope] using hhRorient
  have hrightError : maxwellAffineChordError f a b u =
      (maxwellRightDifferenceQuotient f i a (u * step) -
        (f b - f a) / step) *
        (u * step) := by
    exact ((eq_div_iff (ne_of_gt hrightDen)).mp hrightEq).symm
  have horientedRightError :
      maxwellInfinityChordOrientation s *
          maxwellAffineChordError f a b u < 0 := by
    rw [hrightError]
    have hneg := mul_neg_of_neg_of_pos hhRorient' hrightDen
    simpa only [mul_assoc] using hneg
  have hleftEq := maxwellReflectedLeftDifferenceQuotient_sub_chordSlope_eq
    f i a b step v hstep hvOne hb
  have hleftDen : 0 < (1 - v) * step :=
    mul_pos (sub_pos.mpr hvOne) hstep
  have hhLorient' : maxwellInfinityChordOrientation s *
      (maxwellReflectedLeftDifferenceQuotient f i b ((1 - v) * step) -
        (f b - f a) / step) < 0 := by
    rw [hvStep]
    simpa only [chordSlope] using hhLorient
  have hleftError : maxwellAffineChordError f a b v =
      -(maxwellReflectedLeftDifferenceQuotient f i b ((1 - v) * step) -
          (f b - f a) / step) *
        ((1 - v) * step) := by
    have hneg :
        -(maxwellReflectedLeftDifferenceQuotient f i b ((1 - v) * step) -
            (f b - f a) / step) =
          maxwellAffineChordError f a b v / ((1 - v) * step) := by
      have hneg := congrArg Neg.neg hleftEq
      simpa only [neg_div, neg_neg] using hneg
    exact ((eq_div_iff (ne_of_gt hleftDen)).mp hneg).symm
  have horientedLeftError :
      0 < maxwellInfinityChordOrientation s *
          maxwellAffineChordError f a b v := by
    rw [hleftError]
    calc
      maxwellInfinityChordOrientation s *
          (-(maxwellReflectedLeftDifferenceQuotient f i b ((1 - v) * step) -
              (f b - f a) / step) *
            ((1 - v) * step)) =
          (-(maxwellInfinityChordOrientation s *
            (maxwellReflectedLeftDifferenceQuotient f i b ((1 - v) * step) -
              (f b - f a) / step))) *
              ((1 - v) * step) := by ring
      _ > 0 := mul_pos (neg_pos.mpr hhLorient') hleftDen
  exact ⟨{
    a := a
    b := b
    step := step
    step_pos := hstep
    b_eq := hb
    a_mem := haW
    b_mem := hbW
    segment_mem := hsegment
    u := u
    v := v
    u_pos := hu
    u_lt_v := huv
    v_lt_one := hvOne
    oriented_left_neg := horientedRightError
    oriented_right_pos := horientedLeftError
    isolated := hisolated }⟩

theorem exists_affineChordCrossingObstruction_of_ws5_graph
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {p : ℕ} {D W : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign}
    (hgraph : maxwellFunctionGraph D (fun x _ ↦ f x) ∈ C (p + 1))
    (hlimits : MaxwellDirectSameInfinityLimitsOn f i s D)
    (hWD : W ⊆ D)
    (a b : RealEuclidean p) (step : ℝ)
    (hstep : 0 < step)
    (hb : b = a + step • (Pi.single i 1 : RealEuclidean p))
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a b t ∈ W) :
    Nonempty (MaxwellAffineChordCrossingObstruction f i s W) := by
  have hsegmentD : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a b t ∈ D := by
    intro t ht
    exact hWD (hsegment t ht)
  have hfiniteSection := finite_graph_affineChordSection_of_ws5
    hC hgraph hlimits a b step hstep hb
  have hfiniteZero := finite_maxwellAffineChordZeroSet_of_finite_graphSection
    a b step hstep hb hsegmentD hfiniteSection
  obtain ⟨v₀, hv₀ZeroSet, hv₀pos, hv₀le, hv₀first⟩ :=
    exists_first_positive_testChordZero f a b hfiniteZero
  let c : RealEuclidean p := maxwellAffineChordPath a b v₀
  let shortStep : ℝ := v₀ * step
  have hshortStep : 0 < shortStep := mul_pos hv₀pos hstep
  have hc : c = a + shortStep • (Pi.single i 1 : RealEuclidean p) := by
    dsimp only [c, shortStep]
    exact maxwellAffineChordPath_eq_add_smul i a b step v₀ hb
  have haW : a ∈ W := by
    simpa [maxwellAffineChordPath] using
      hsegment 0 ⟨by norm_num, by norm_num⟩
  have hcW : c ∈ W := by
    exact hsegment v₀ hv₀ZeroSet.1
  have hshortSegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a c t ∈ W := by
    intro t ht
    rw [show c = maxwellAffineChordPath a b v₀ by rfl,
      maxwellAffineChordPath_subchord]
    apply hsegment (t * v₀)
    constructor
    · exact mul_nonneg ht.1 (le_of_lt hv₀pos)
    · calc
        t * v₀ ≤ 1 * v₀ := mul_le_mul_of_nonneg_right ht.2 (le_of_lt hv₀pos)
        _ = v₀ := one_mul v₀
        _ ≤ 1 := hv₀le
  have hshortIsolated : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      maxwellAffineChordError f a c t ≠ 0 := by
    intro t ht
    rw [show c = maxwellAffineChordPath a b v₀ by rfl,
      maxwellAffineChordError_subchord f a b v₀ t hv₀ZeroSet.2]
    apply hv₀first (t * v₀)
    constructor
    · exact mul_pos ht.1 hv₀pos
    · simpa only [one_mul] using
        mul_lt_mul_of_pos_right ht.2 hv₀pos
  have hlimitsW : MaxwellDirectSameInfinityLimitsOn f i s W := by
    intro x hx
    exact hlimits x (hWD hx)
  exact exists_affineChordCrossingObstruction_of_directLimits
    hlimitsW a c shortStep hshortStep hc haW hcW hshortSegment hshortIsolated

/-- A family-member graph and the genuine fixed-base two-sided infinite
quotient limits are sufficient for the affine-chord mechanism. -/
theorem maxwellWS5AffineChordCrossingMechanism_of_graph_and_directLimits
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {p : ℕ} {A : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign}
    (hgraph : maxwellFunctionGraph A (fun x _ ↦ f x) ∈ C (p + 1))
    (hlimits : MaxwellDirectSameInfinityLimitsOn f i s A) :
    MaxwellWS5AffineChordCrossingMechanism f i s A := by
  intro V hVopen hVnonempty hVA
  obtain ⟨a, haV⟩ := hVnonempty
  obtain ⟨ε, hεpos, hball⟩ := (Metric.isOpen_iff.mp hVopen) a haV
  let step : ℝ := ε / 2
  let b : RealEuclidean p :=
    a + step • (Pi.single i 1 : RealEuclidean p)
  have hstep : 0 < step := half_pos hεpos
  have hb : b = a + step • (Pi.single i 1 : RealEuclidean p) := rfl
  have hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a b t ∈ V := by
    intro t ht
    apply hball
    rw [Metric.mem_ball,
      maxwellAffineChordPath_eq_add_smul i a b step t hb,
      dist_self_add_left, norm_smul, Pi.norm_single]
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    rw [abs_of_nonneg (mul_nonneg ht.1 (le_of_lt hstep))]
    have hle : t * step ≤ 1 * step :=
      mul_le_mul_of_nonneg_right ht.2 (le_of_lt hstep)
    dsimp only [step] at hle ⊢
    nlinarith
  exact exists_affineChordCrossingObstruction_of_ws5_graph
    hC hgraph hlimits hVA a b step hstep hb hsegment

def MaxwellAffineChordCrossingObstruction.mono
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign} {W V : Set (RealEuclidean p)}
    (h : MaxwellAffineChordCrossingObstruction f i s W)
    (hWV : W ⊆ V) :
    MaxwellAffineChordCrossingObstruction f i s V :=
  { a := h.a
    b := h.b
    step := h.step
    step_pos := h.step_pos
    b_eq := h.b_eq
    a_mem := hWV h.a_mem
    b_mem := hWV h.b_mem
    segment_mem := fun t ht ↦ hWV (h.segment_mem t ht)
    u := h.u
    v := h.v
    u_pos := h.u_pos
    u_lt_v := h.u_lt_v
    v_lt_one := h.v_lt_one
    oriented_left_neg := h.oriented_left_neg
    oriented_right_pos := h.oriented_right_pos
    isolated := h.isolated }

/-- For a scalar pseudofunction, the graph-membership input above is not a
residual premise.  Every hypothetical open subset can be shrunk to a ball
away from the closed multivalued locus; on that ball the relation restriction
is exactly the graph of the chosen value.  Thus only the fixed-base infinite
limits remain as analytic input. -/
theorem maxwellWS5AffineChordCrossingMechanism_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U A : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {s : MaxwellSameInfinitySign}
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R)
    (hUopen : IsOpen U)
    (hAclosure : A ⊆ closure U)
    (hlimits : MaxwellDirectSameInfinityLimitsOn
      (maxwellChosenScalarValue R) i s A) :
    MaxwellWS5AffineChordCrossingMechanism
      (maxwellChosenScalarValue R) i s A := by
  have hmultiMem : maxwellMultivaluedLocus R ∈
      charbonnelClosure S p :=
    maxwellMultivaluedLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hRmem
  have hmultiClosureEmpty :
      interior (closure (maxwellMultivaluedLocus R)) = ∅ :=
    (h21 hp hmultiMem).2.1.mp hR.multivalued_null
  intro V hVopen hVnonempty hVA
  obtain ⟨xV, hxV⟩ := hVnonempty
  have hVU_nonempty : (V ∩ U).Nonempty :=
    (mem_closure_iff_nhds.mp (hAclosure (hVA hxV))) V
      (hVopen.mem_nhds hxV)
  have hVU_open : IsOpen (V ∩ U) := hVopen.inter hUopen
  obtain ⟨x₀, ε, hε, hball⟩ :=
    exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
      hVU_open hVU_nonempty isClosed_closure hmultiClosureEmpty
  let B : Set (RealEuclidean p) := Metric.ball x₀ ε
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBnonempty : B.Nonempty := ⟨x₀, Metric.mem_ball_self hε⟩
  have hBV : B ⊆ V := fun _ hx ↦ (hball hx).1.1
  have hBU : B ⊆ U := fun _ hx ↦ (hball hx).1.2
  have hBA : B ⊆ A := fun x hx ↦ hVA (hBV hx)
  have hBgood : B ⊆ U \ maxwellMultivaluedLocus R := by
    intro x hx
    refine ⟨hBU hx, ?_⟩
    intro hxMulti
    exact (hball hx).2 (subset_closure hxMulti)
  let fvec : RealEuclidean p → RealEuclidean 1 :=
    fun x _ ↦ maxwellChosenScalarValue R x
  have hgraphEq : maxwellRelationRestrict R B =
      maxwellFunctionGraph B fvec := by
    ext z
    rw [← realEuclideanAppend_takeLeft_takeRight z]
    rw [realEuclideanAppend_mem_maxwellRelationRestrict_iff,
      realEuclideanAppend_mem_maxwellFunctionGraph_iff]
    constructor
    · rintro ⟨hzR, hxB⟩
      refine ⟨hxB, ?_⟩
      dsimp only [fvec]
      rw [← maxwellChosenValue_eq_scalar R (realEuclideanTakeLeft z)]
      exact eq_maxwellChosenValue_of_not_mem_multivaluedLocus
        (hBgood hxB).2 hzR
    · rintro ⟨hxB, hy⟩
      refine ⟨?_, hxB⟩
      dsimp only [fvec] at hy ⊢
      rw [hy, ← maxwellChosenValue_eq_scalar R (realEuclideanTakeLeft z)]
      exact hR.full_fibers.maxwellChosenValue_mem (hBgood hxB).1
  have hBmem : B ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp (polynomialSignConstructible_ball x₀ hε)
  have hgraphMem : maxwellFunctionGraph B fvec ∈
      charbonnelClosure S (p + 1) := by
    rw [← hgraphEq]
    exact maxwellRelationRestrict_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hRmem
  have hlimitsB : MaxwellDirectSameInfinityLimitsOn
      (maxwellChosenScalarValue R) i s B := by
    intro x hx
    exact hlimits x (hBA hx)
  have hmechanismB : MaxwellWS5AffineChordCrossingMechanism
      (maxwellChosenScalarValue R) i s B := by
    exact maxwellWS5AffineChordCrossingMechanism_of_graph_and_directLimits
      hC hgraphMem hlimitsB
  obtain ⟨hB⟩ := hmechanismB B hBopen hBnonempty Subset.rfl
  exact ⟨hB.mono hBV⟩

theorem maxwellOneSidedInfinityBase_subset_closure_domain_for_affineChord
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) :
    maxwellOneSidedInfinityBase U R i side infinity ⊆ closure U := by
  intro x hx
  obtain ⟨happroach⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side infinity x).mp hx
  let hdivergent := happroach.toDivergentSlopeApproach
  have hsourceU : ∀ n, (hdivergent.source n).1 ∈ U := by
    intro n
    have hn := hdivergent.point_mem n
    rw [mem_maxwellStepLastDifferenceQuotientRelation_append_iff,
      realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff]
      at hn
    exact hn.1
  have hsourceLimit :
      Tendsto (fun n ↦ (hdivergent.source n).1) atTop (nhds x) := by
    have h := continuous_fst.tendsto (x, 0) |>.comp
      hdivergent.source_tendsto
    simpa only [Function.comp_def] using h
  exact mem_closure_iff_seq_limit.mpr
    ⟨fun n ↦ (hdivergent.source n).1, hsourceU, hsourceLimit⟩

theorem maxwellSamePositiveInfinityLocus_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellSamePositiveInfinityLocus U R i ⊆ closure U := by
  intro x hx
  exact maxwellOneSidedInfinityBase_subset_closure_domain_for_affineChord
    U R i .positive .positive hx.1

theorem maxwellSameNegativeInfinityLocus_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellSameNegativeInfinityLocus U R i ⊆ closure U := by
  intro x hx
  exact maxwellOneSidedInfinityBase_subset_closure_domain_for_affineChord
    U R i .positive .negative hx.1

/-- The exact residual source for both equal-infinity chord fields.  The
closure-based slope cluster definitions currently supply moving-base
sequences; these fields record the stronger fixed-base limits used by the
source chord argument.  The chosen graph required by WS5 is derived locally
from pseudofunction uniqueness. -/
structure MaxwellEqualInfinityAffineChordSourceData
    {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  positive_directLimits : MaxwellDirectSameInfinityLimitsOn
    (maxwellChosenScalarValue R) i .positiveInfinity
      (maxwellSamePositiveInfinityLocus U R i)
  negative_directLimits : MaxwellDirectSameInfinityLimitsOn
    (maxwellChosenScalarValue R) i .negativeInfinity
      (maxwellSameNegativeInfinityLocus U R i)

theorem MaxwellEqualInfinityAffineChordSourceData.mechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} (hp : 0 < p)
    (hUopen : IsOpen U)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R)
    (hsource : MaxwellEqualInfinityAffineChordSourceData U R i) :
    MaxwellWS5AffineChordCrossingMechanism
        (maxwellChosenScalarValue R) i .positiveInfinity
          (maxwellSamePositiveInfinityLocus U R i) ∧
      MaxwellWS5AffineChordCrossingMechanism
        (maxwellChosenScalarValue R) i .negativeInfinity
          (maxwellSameNegativeInfinityLocus U R i) := by
  constructor
  · exact maxwellWS5AffineChordCrossingMechanism_of_pseudofunction
      hC h21 hp hRmem hR hUopen
        (maxwellSamePositiveInfinityLocus_subset_closure_domain U R i)
        hsource.positive_directLimits
  · exact maxwellWS5AffineChordCrossingMechanism_of_pseudofunction
      hC h21 hp hRmem hR hUopen
        (maxwellSameNegativeInfinityLocus_subset_closure_domain U R i)
        hsource.negative_directLimits

end AbelFormalization
