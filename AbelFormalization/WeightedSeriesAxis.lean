import AbelFormalization.WeightedSeriesDivision
import AbelFormalization.WeightedSeriesEvaluation
import AbelFormalization.WeightedSeriesGerm
import AbelFormalization.AnalyticRegularDirection
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order

/-! # Pure-axis coefficients of convergent series

Restriction to a coordinate axis is the scalar power series formed from the
pure powers of that coordinate. A nonzero axis germ therefore has a first
nonzero coefficient, which can be normalized to one by a nonzero scalar.
-/

noncomputable section

open Filter
open scoped Topology NNReal ENNReal

namespace AbelFormalization

variable {σ : Type*} [DecidableEq σ]

/-- The coefficients of the pure powers of a distinguished variable. -/
def weightedSeriesAxisCoeff (f : MvPowerSeries σ ℝ) (i : σ) (n : ℕ) : ℝ :=
  MvPowerSeries.coeff (Finsupp.single i n) f

/-- Any monomial involving another coordinate vanishes on the given axis. -/
theorem multiRadiusWeight_axis_eq_zero (i : σ) (t : ℝ) (d : σ →₀ ℕ)
    (hd : d ∉ Set.range (Finsupp.single i : ℕ → σ →₀ ℕ)) :
    multiRadiusWeight (Pi.single i t) d = 0 := by
  classical
  have hex : ∃ j, j ≠ i ∧ d j ≠ 0 := by
    by_contra! hz
    apply hd
    refine ⟨d i, ?_⟩
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne hj, hz j hj]
  obtain ⟨j, hji, hdj⟩ := hex
  unfold multiRadiusWeight Finsupp.prod
  apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdj)
  simp [Pi.single_eq_of_ne hji, hdj]

/-- Exact axis evaluation, including points outside the convergence disk.
Outside that disk both sides retain the same totalized infinite-sum meaning. -/
theorem weightedSeriesEval_axis (f : MvPowerSeries σ ℝ) (i : σ) (t : ℝ) :
    weightedSeriesEval f (Pi.single i t) =
      ∑' n, weightedSeriesAxisCoeff f i n * t ^ n := by
  have hsupp : Function.support
      (fun d => MvPowerSeries.coeff d f * multiRadiusWeight (Pi.single i t) d) ⊆
        Set.range (Finsupp.single i : ℕ → σ →₀ ℕ) := by
    intro d hd
    by_contra hnot
    apply hd
    change MvPowerSeries.coeff d f * multiRadiusWeight (Pi.single i t) d = 0
    rw [multiRadiusWeight_axis_eq_zero i t d hnot, mul_zero]
  have he := (Finsupp.single_injective i).tsum_eq hsupp
  simpa only [weightedSeriesEval, weightedSeriesAxisCoeff, multiRadiusWeight_single,
    Pi.single_eq_same] using he.symm

omit [DecidableEq σ] in
/-- The scalar coefficients are summable with the distinguished radius weight. -/
theorem weightedSeriesAxisCoeff_summable {ρ : σ → ℝ} {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ) :
    Summable (fun n => ‖weightedSeriesAxisCoeff f i n‖ * ρ i ^ n) := by
  simpa only [Function.comp_def, weightedSeriesAxisCoeff, multiRadiusWeight_single] using
    hf.comp_injective (Finsupp.single_injective i)

/-- The formal scalar expansion of the actual axis restriction. -/
theorem weightedSeriesEval_axis_hasFPowerSeriesAt (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ) :
    HasFPowerSeriesAt (fun t : ℝ => weightedSeriesEval f (Pi.single i t))
      (FormalMultilinearSeries.ofScalars ℝ (weightedSeriesAxisCoeff f i)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hρ i)] with t ht
  have hti : |t| < ρ i := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have hx : ∀ j, |(Pi.single i t : σ → ℝ) j| ≤ ρ j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hti.le
    · simpa only [Pi.single_eq_of_ne hj, abs_zero] using (hρ j).le
  have hs := (weightedSeriesEval_summable hx hf).comp_injective (Finsupp.single_injective i)
  have hs' : Summable (fun n => t ^ n * weightedSeriesAxisCoeff f i n) := by
    simpa only [Function.comp_def, weightedSeriesAxisCoeff, multiRadiusWeight_single, Pi.single_eq_same,
      mul_comm] using hs
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add,
    weightedSeriesEval_axis, mul_comm] using hs'.hasSum

/-- The axis restriction is an actual scalar analytic function near zero. -/
theorem analyticAt_weightedSeriesEval_axis (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) (i : σ) :
    AnalyticAt ℝ (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) 0 :=
  (weightedSeriesEval_axis_hasFPowerSeriesAt ρ hρ hf i).analyticAt

/-- The pure-axis coefficient is the usual factorial-normalized derivative
of the actual analytic axis restriction. -/
theorem weightedSeriesAxisCoeff_eq_iteratedDeriv_div (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ) (n : ℕ) :
    weightedSeriesAxisCoeff f i n =
      iteratedDeriv n (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) 0 / n.factorial := by
  have hp := weightedSeriesEval_axis_hasFPowerSeriesAt ρ hρ hf i
  have he := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun P : FormalMultilinearSeries ℝ ℝ ℝ => P.coeff n) he
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc

/-- Exact agreement between analytic vanishing order and the first nonzero
pure-axis coefficient. -/
theorem weightedSeriesEval_axis_order_eq_nat_iff (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ) (n : ℕ) :
    analyticOrderAt (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) 0 = n ↔
      (∀ k < n, weightedSeriesAxisCoeff f i k = 0) ∧ weightedSeriesAxisCoeff f i n ≠ 0 := by
  have hz (k : ℕ) : weightedSeriesAxisCoeff f i k = 0 ↔
      iteratedDeriv k (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) 0 = 0 := by
    rw [weightedSeriesAxisCoeff_eq_iteratedDeriv_div ρ hρ hf i k]
    simp [Nat.factorial_ne_zero]
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticAt_weightedSeriesEval_axis ρ hρ hf i)]
  simp only [ne_eq, ← hz]

/-- Scalar-series uniqueness identifies local vanishing with vanishing of all
pure-axis coefficients. -/
theorem weightedSeriesEval_axis_eventually_zero_iff (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ) :
    (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) =ᶠ[𝓝 0] 0 ↔
      ∀ n, weightedSeriesAxisCoeff f i n = 0 := by
  constructor
  · intro he n
    have hp := (weightedSeriesEval_axis_hasFPowerSeriesAt ρ hρ hf i).eq_zero_of_eventually he
    have hn := congrArg (fun P : FormalMultilinearSeries ℝ ℝ ℝ => P n) hp
    exact (FormalMultilinearSeries.ofScalars_eq_zero ℝ n).mp hn
  · intro hz
    exact Eventually.of_forall fun t => by simp [weightedSeriesEval_axis, hz]

/-- Finite analytic order is equivalent to a nonzero pure-axis coefficient. -/
theorem weightedSeriesEval_axis_order_ne_top_iff (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ) :
    analyticOrderAt (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) 0 ≠ ⊤ ↔
      ∃ n, weightedSeriesAxisCoeff f i n ≠ 0 := by
  rw [ne_eq, analyticOrderAt_eq_top]
  change (¬ (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) =ᶠ[𝓝 0] 0) ↔ _
  rw [weightedSeriesEval_axis_eventually_zero_iff ρ hρ hf i]
  simp only [not_forall]

/-- A nonzero actual axis germ has a first nonzero pure-axis coefficient. -/
theorem weightedSeriesAxisCoeff_exists_first (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) (i : σ)
    (hne : ¬ (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) =ᶠ[𝓝 0] 0) :
    ∃ n, (∀ k < n, weightedSeriesAxisCoeff f i k = 0) ∧
      weightedSeriesAxisCoeff f i n ≠ 0 := by
  classical
  have hex : ∃ n, weightedSeriesAxisCoeff f i n ≠ 0 := by
    by_contra! hz
    exact hne ((weightedSeriesEval_axis_eventually_zero_iff ρ hρ hf i).mpr hz)
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  intro k hk
  exact not_ne_iff.mp (Nat.find_min hex hk)

/-- Vanishing at the origin makes the first nonzero axis order positive. -/
theorem weightedSeriesAxisCoeff_exists_first_positive (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) (i : σ)
    (hne : ¬ (fun t : ℝ => weightedSeriesEval f (Pi.single i t)) =ᶠ[𝓝 0] 0)
    (hzero : weightedSeriesEval f 0 = 0) :
    ∃ n, 0 < n ∧ (∀ k < n, weightedSeriesAxisCoeff f i k = 0) ∧
      weightedSeriesAxisCoeff f i n ≠ 0 := by
  obtain ⟨n, hn, hc⟩ := weightedSeriesAxisCoeff_exists_first ρ hρ hf i hne
  have h0 : weightedSeriesAxisCoeff f i 0 = 0 := by
    rw [weightedSeriesAxisCoeff_eq_iteratedDeriv_div ρ hρ hf i 0]
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      Pi.single_zero] using hzero
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    exact hc h0
  exact ⟨n, Nat.pos_of_ne_zero hn0, hn, hc⟩

/-- Normalize the first nonzero axis coefficient while preserving every lower
vanishing coefficient, inside the same weighted Banach algebra. -/
theorem weightedSeriesAxisCoeff_exists_normalization (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) (S : WeightedSeries ρ hρ) (i : σ)
    (hne : ¬ (fun t : ℝ => weightedSeriesEval S.val (Pi.single i t)) =ᶠ[𝓝 0] 0) :
    ∃ n, ∃ c : ℝ, c ≠ 0 ∧
      (∀ k < n, weightedSeriesAxisCoeff (c • S).val i k = 0) ∧
        weightedSeriesAxisCoeff (c • S).val i n = 1 := by
  obtain ⟨n, hn, hc⟩ := weightedSeriesAxisCoeff_exists_first ρ hρ S.property i hne
  refine ⟨n, (weightedSeriesAxisCoeff S.val i n)⁻¹, inv_ne_zero hc, ?_, ?_⟩
  · intro k hk
    change MvPowerSeries.coeff (Finsupp.single i k)
      ((weightedSeriesAxisCoeff S.val i n)⁻¹ • S.val) = 0
    rw [MvPowerSeries.coeff_smul]
    change (weightedSeriesAxisCoeff S.val i n)⁻¹ * weightedSeriesAxisCoeff S.val i k = 0
    rw [hn k hk, mul_zero]
  · change MvPowerSeries.coeff (Finsupp.single i n)
      ((weightedSeriesAxisCoeff S.val i n)⁻¹ • S.val) = 1
    rw [MvPowerSeries.coeff_smul]
    exact inv_mul_cancel₀ hc

section ActualGerms

variable [Fintype σ]

/-- The coordinate-axis pullback of the actual germ is represented by the
scalar evaluation function used in the coefficient formulas above. -/
theorem analyticGermAlong_weightedSeriesGerm (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (S : WeightedSeries ρ hρ) (i : σ) :
    analyticGermAlong (Pi.single i 1) (weightedSeriesGerm ρ hρ S) =
      analyticGermOf (fun t : ℝ => weightedSeriesEval S.val (Pi.single i t))
        (analyticAt_weightedSeriesEval_axis ρ hρ S.property i) := by
  rw [weightedSeriesGerm, analyticGermAlong_of]
  apply (analyticGermOf_eq_iff
    (analyticAt_comp_direction
      (analyticAt_weightedSeriesEval_polyradius ρ hρ S.property) (Pi.single i 1))
    (analyticAt_weightedSeriesEval_axis ρ hρ S.property i)).mpr
  exact Eventually.of_forall fun t => by
    change weightedSeriesEval S.val (t • Pi.single i 1) =
      weightedSeriesEval S.val (Pi.single i t)
    rw [← Pi.single_smul]
    simp only [smul_eq_mul, mul_one]

/-- Equality to zero of the actual pulled-back germ has its literal
neighborhood-equality interpretation. -/
theorem analyticGermAlong_weightedSeriesGerm_eq_zero_iff (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) (S : WeightedSeries ρ hρ) (i : σ) :
    analyticGermAlong (Pi.single i 1) (weightedSeriesGerm ρ hρ S) = 0 ↔
      (fun t : ℝ => weightedSeriesEval S.val (Pi.single i t)) =ᶠ[𝓝 0] 0 := by
  rw [analyticGermAlong_weightedSeriesGerm, analyticGermOf_eq_zero_iff]

/-- Apply regularity of an actual analytic-germ pullback directly to the
weighted representative's pure-axis coefficients. -/
theorem weightedSeriesAxisCoeff_exists_first_of_germ (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) (S : WeightedSeries ρ hρ) (i : σ)
    (hne : analyticGermAlong (Pi.single i 1) (weightedSeriesGerm ρ hρ S) ≠ 0) :
    ∃ n, (∀ k < n, weightedSeriesAxisCoeff S.val i k = 0) ∧
      weightedSeriesAxisCoeff S.val i n ≠ 0 :=
  weightedSeriesAxisCoeff_exists_first ρ hρ S.property i
    (fun he => hne ((analyticGermAlong_weightedSeriesGerm_eq_zero_iff ρ hρ S i).mpr he))

/-- A regular nonunit actual germ has a positive first nonzero axis order. -/
theorem weightedSeriesAxisCoeff_exists_first_positive_of_germ (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) (S : WeightedSeries ρ hρ) (i : σ)
    (hne : analyticGermAlong (Pi.single i 1) (weightedSeriesGerm ρ hρ S) ≠ 0)
    (hunit : ¬ IsUnit (weightedSeriesGerm ρ hρ S)) :
    ∃ n, 0 < n ∧ (∀ k < n, weightedSeriesAxisCoeff S.val i k = 0) ∧
      weightedSeriesAxisCoeff S.val i n ≠ 0 := by
  apply weightedSeriesAxisCoeff_exists_first_positive ρ hρ S.property i
    (fun he => hne ((analyticGermAlong_weightedSeriesGerm_eq_zero_iff ρ hρ S i).mpr he))
  have hval : analyticGermValue (0 : σ → ℝ) (weightedSeriesGerm ρ hρ S) = 0 := by
    by_contra hneval
    exact hunit ((isUnit_analyticGerm_iff _).mpr hneval)
  exact hval

/-- The direct input to regular weighted division: a nonzero actual axis
germ supplies a nonzero normalizing scalar and the exact coefficient conditions. -/
theorem weightedSeriesAxisCoeff_exists_normalization_of_germ (ρ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) (S : WeightedSeries ρ hρ) (i : σ)
    (hne : analyticGermAlong (Pi.single i 1) (weightedSeriesGerm ρ hρ S) ≠ 0) :
    ∃ n, ∃ c : ℝ, c ≠ 0 ∧
      (∀ k < n, weightedSeriesAxisCoeff (c • S).val i k = 0) ∧
        weightedSeriesAxisCoeff (c • S).val i n = 1 :=
  weightedSeriesAxisCoeff_exists_normalization ρ hρ S i
    (fun he => hne ((analyticGermAlong_weightedSeriesGerm_eq_zero_iff ρ hρ S i).mpr he))

end ActualGerms

end AbelFormalization
