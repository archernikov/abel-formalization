import AbelFormalization.WeightedSeriesEvaluationMap
import Mathlib.Data.Finsupp.Option

/-! # Coefficient slices in one distinguished variable

The coordinate `none` is distinguished and `some i` denotes a parameter
coordinate. Each fixed-degree coefficient slice of a weighted summable series
is weighted summable in the parameter coordinates. Its norm is bounded by the
original norm divided by the distinguished radius to that degree.

Actual pointwise evaluation is reconstructed by summing these slices. If the
coefficients above a fixed distinguished degree vanish, this is a finite sum.
-/

noncomputable section

namespace AbelFormalization

variable {ι : Type*}

/-- Attach a distinguished coordinate of radius `τ` to parameter radii `ρ`. -/
def optionRadius (ρ : ι → ℝ) (τ : ℝ) : Option ι → ℝ := fun i => i.elim τ ρ

@[simp] theorem optionRadius_none (ρ : ι → ℝ) (τ : ℝ) :
    optionRadius ρ τ none = τ := rfl

@[simp] theorem optionRadius_some (ρ : ι → ℝ) (τ : ℝ) (i : ι) :
    optionRadius ρ τ (some i) = ρ i := rfl

theorem optionRadius_pos {ρ : ι → ℝ} {τ : ℝ} (hρ : ∀ i, 0 < ρ i) (hτ : 0 < τ) :
    ∀ i, 0 < optionRadius ρ τ i := by
  intro i
  cases i with
  | none => exact hτ
  | some i => exact hρ i

theorem optionRadius_nonneg {ρ : ι → ℝ} {τ : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hτ : 0 ≤ τ) :
    ∀ i, 0 ≤ optionRadius ρ τ i := by
  intro i
  cases i with
  | none => exact hτ
  | some i => exact hρ i

/-- The monomial weight separates into distinguished and parameter factors. -/
theorem multiRadiusWeight_optionElim (ρ : ι → ℝ) (τ : ℝ) (d : ι →₀ ℕ) (k : ℕ) :
    multiRadiusWeight (optionRadius ρ τ) (d.optionElim k) =
      τ ^ k * multiRadiusWeight ρ d := by
  unfold multiRadiusWeight
  rw [Finsupp.prod_option_index _ _ (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
    optionRadius_none, optionRadius_some]

theorem finsupp_optionElim_injective (k : ℕ) :
    Function.Injective (fun d : ι →₀ ℕ => d.optionElim k) := by
  intro d e h
  simpa only [Finsupp.some_optionElim] using congrArg Finsupp.some h

/-- The coefficient series at a fixed degree in the distinguished variable. -/
def mvPowerSeriesCoefficientSlice (k : ℕ) :
    MvPowerSeries (Option ι) ℝ →ₗ[ℝ] MvPowerSeries ι ℝ where
  toFun f := fun d => MvPowerSeries.coeff (d.optionElim k) f
  map_add' f g := by
    apply MvPowerSeries.ext
    intro d
    exact map_add (MvPowerSeries.coeff (d.optionElim k)) f g
  map_smul' c f := by
    apply MvPowerSeries.ext
    intro d
    exact MvPowerSeries.coeff_smul f (d.optionElim k) c

@[simp]
theorem coeff_mvPowerSeriesCoefficientSlice (k : ℕ) (d : ι →₀ ℕ)
    (f : MvPowerSeries (Option ι) ℝ) :
    MvPowerSeries.coeff d (mvPowerSeriesCoefficientSlice k f) =
      MvPowerSeries.coeff (d.optionElim k) f := rfl

theorem weightedCoeff_slice_identity (ρ : ι → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (k : ℕ) (d : ι →₀ ℕ) (f : MvPowerSeries (Option ι) ℝ) :
    ‖MvPowerSeries.coeff d (mvPowerSeriesCoefficientSlice k f)‖ * multiRadiusWeight ρ d =
      (‖MvPowerSeries.coeff (d.optionElim k) f‖ *
        multiRadiusWeight (optionRadius ρ τ) (d.optionElim k)) / τ ^ k := by
  rw [coeff_mvPowerSeriesCoefficientSlice, multiRadiusWeight_optionElim]
  field_simp [ne_of_gt hτ]

/-- Fixing a distinguished degree selects a summable subfamily. -/
theorem weightedCoeffSummable_slice {ρ : ι → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (k : ℕ) {f : MvPowerSeries (Option ι) ℝ}
    (hf : WeightedCoeffSummable (optionRadius ρ τ) f) :
    WeightedCoeffSummable ρ (mvPowerSeriesCoefficientSlice k f) := by
  have hs := hf.comp_injective (finsupp_optionElim_injective (ι := ι) k)
  apply (hs.div_const (τ ^ k)).congr
  intro d
  exact (weightedCoeff_slice_identity ρ hτ k d f).symm

/-- The exact radius loss for a fixed-degree coefficient slice. -/
theorem weightedCoeffNorm_slice_le {ρ : ι → ℝ} {τ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hτ : 0 < τ) (k : ℕ)
    {f : MvPowerSeries (Option ι) ℝ}
    (hf : WeightedCoeffSummable (optionRadius ρ τ) f) :
    weightedCoeffNorm ρ (mvPowerSeriesCoefficientSlice k f) ≤
      weightedCoeffNorm (optionRadius ρ τ) f / τ ^ k := by
  unfold weightedCoeffNorm
  simp_rw [weightedCoeff_slice_identity ρ hτ k]
  rw [tsum_div_const]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hτ.le k)
  exact tsum_comp_le_tsum_of_inj hf
    (fun d => mul_nonneg (norm_nonneg _)
      (multiRadiusWeight_nonneg (optionRadius_nonneg hρ hτ.le) d))
    (finsupp_optionElim_injective k)

/-- A coefficient slice as a bounded linear map between the actual Banach spaces. -/
def weightedSeriesSliceLinear (ρ : ι → ℝ) (τ : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hτ : 0 < τ) (k : ℕ) :
    WeightedSeries (optionRadius ρ τ) (optionRadius_pos hρ hτ) →ₗ[ℝ]
      WeightedSeries ρ hρ where
  toFun f := ⟨mvPowerSeriesCoefficientSlice k f.val,
    weightedCoeffSummable_slice hτ k f.property⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (mvPowerSeriesCoefficientSlice k) f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (mvPowerSeriesCoefficientSlice k) c f.val

def weightedSeriesSliceCLM (ρ : ι → ℝ) (τ : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hτ : 0 < τ) (k : ℕ) :
    WeightedSeries (optionRadius ρ τ) (optionRadius_pos hρ hτ) →L[ℝ]
      WeightedSeries ρ hρ :=
  (weightedSeriesSliceLinear ρ τ hρ hτ k).mkContinuous (1 / τ ^ k) fun f => by
    rw [weightedSeries_norm_eq, weightedSeries_norm_eq]
    calc
      _ ≤ weightedCoeffNorm (optionRadius ρ τ) f.val / τ ^ k :=
        weightedCoeffNorm_slice_le (fun i => (hρ i).le) hτ k f.property
      _ = _ := by ring

@[simp]
theorem weightedSeriesSliceCLM_val (ρ : ι → ℝ) (τ : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hτ : 0 < τ) (k : ℕ)
    (f : WeightedSeries (optionRadius ρ τ) (optionRadius_pos hρ hτ)) :
    (weightedSeriesSliceCLM ρ τ hρ hτ k f).val =
      mvPowerSeriesCoefficientSlice k f.val := rfl

theorem weightedSeriesSliceCLM_norm_le (ρ : ι → ℝ) (τ : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hτ : 0 < τ) (k : ℕ) :
    ‖weightedSeriesSliceCLM ρ τ hρ hτ k‖ ≤ 1 / τ ^ k :=
  LinearMap.mkContinuous_norm_le _ (div_nonneg zero_le_one (pow_nonneg hτ.le k)) _

/-- A coefficient cutoff makes every later distinguished slice vanish. -/
theorem mvPowerSeriesCoefficientSlice_eq_zero_of_cutoff
    {f : MvPowerSeries (Option ι) ℝ} {n k : ℕ}
    (hf : ∀ d, n ≤ d none → MvPowerSeries.coeff d f = 0) (hk : n ≤ k) :
    mvPowerSeriesCoefficientSlice k f = 0 := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_mvPowerSeriesCoefficientSlice, map_zero]
  exact hf _ (by simpa only [Finsupp.optionElim_apply_none] using hk)

/-- Absolute convergence permits regrouping by the distinguished degree. -/
theorem weightedSeriesEval_eq_tsum_slices {ρ x : ι → ℝ} {τ t : ℝ}
    (hx : ∀ i, |x i| ≤ ρ i) (ht : |t| ≤ τ)
    {f : MvPowerSeries (Option ι) ℝ}
    (hf : WeightedCoeffSummable (optionRadius ρ τ) f) :
    weightedSeriesEval f (optionRadius x t) =
      ∑' k : ℕ, weightedSeriesEval (mvPowerSeriesCoefficientSlice k f) x * t ^ k := by
  have hxt : ∀ i, |optionRadius x t i| ≤ optionRadius ρ τ i := by
    intro i
    cases i with
    | none => exact ht
    | some i => exact hx i
  let F : ℕ × (ι →₀ ℕ) → ℝ := fun p =>
    MvPowerSeries.coeff (p.2.optionElim p.1) f *
      multiRadiusWeight (optionRadius x t) (p.2.optionElim p.1)
  have hs : Summable F :=
    (weightedSeriesEval_summable hxt hf).comp_injective Finsupp.optionEquiv.symm.injective
  calc
    weightedSeriesEval f (optionRadius x t) = ∑' p, F p := by
      exact (Finsupp.optionEquiv.symm.tsum_eq
        (fun d => MvPowerSeries.coeff d f * multiRadiusWeight (optionRadius x t) d)).symm
    _ = ∑' k : ℕ, ∑' d : ι →₀ ℕ, F (k, d) := hs.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro k
      simp only [F, multiRadiusWeight_optionElim, weightedSeriesEval,
        coeff_mvPowerSeriesCoefficientSlice]
      rw [← tsum_mul_right]
      apply tsum_congr
      intro d
      ring

/-- A remainder supported below degree `n` is a polynomial in the distinguished
variable, with weighted summable parameter-series coefficients. -/
theorem weightedSeriesEval_eq_sum_slices {ρ x : ι → ℝ} {τ t : ℝ}
    (hx : ∀ i, |x i| ≤ ρ i) (ht : |t| ≤ τ)
    {f : MvPowerSeries (Option ι) ℝ}
    (hf : WeightedCoeffSummable (optionRadius ρ τ) f) (n : ℕ)
    (hcut : ∀ d, n ≤ d none → MvPowerSeries.coeff d f = 0) :
    weightedSeriesEval f (optionRadius x t) =
      ∑ k ∈ Finset.range n, weightedSeriesEval (mvPowerSeriesCoefficientSlice k f) x * t ^ k := by
  rw [weightedSeriesEval_eq_tsum_slices hx ht hf]
  apply tsum_eq_sum
  intro k hk
  have hnk : n ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  rw [mvPowerSeriesCoefficientSlice_eq_zero_of_cutoff hcut hnk,
    weightedSeriesEval_zero, zero_mul]

end AbelFormalization
