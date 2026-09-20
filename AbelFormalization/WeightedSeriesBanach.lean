import AbelFormalization.WeightedSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # The Banach algebra of weighted summable power series

Positive coordinate radii identify weighted absolutely summable coefficient
series with an actual ℓ¹ space. The induced norm is exactly the weighted
coefficient sum, and the Cauchy-product estimate makes the inherited formal
series multiplication continuous. Completeness is proved by the ℓ¹ isometry.
This constructs the coefficient algebra for convergent division; no claim of
analytic-germ Noetherianity is made here.
-/

noncomputable section

open scoped ENNReal

namespace AbelFormalization

variable {σ : Type*}

/-- The real subalgebra of formal series with weighted summable coefficients. -/
def weightedSeriesSubalgebra (ρ : σ → ℝ) (hρ : ∀ i, 0 ≤ ρ i) :
    Subalgebra ℝ (MvPowerSeries σ ℝ) where
  carrier := {f | WeightedCoeffSummable ρ f}
  zero_mem' := weightedCoeffSummable_zero ρ
  one_mem' := weightedCoeffSummable_one ρ
  add_mem' := weightedCoeffSummable_add hρ
  mul_mem' := weightedCoeffSummable_mul hρ
  algebraMap_mem' c := weightedCoeffSummable_C ρ c

/-- Strictly positive radii give a genuine norm, rather than a seminorm. -/
abbrev WeightedSeries (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :=
  weightedSeriesSubalgebra ρ (fun i => (hρ i).le)

/-- Multiplying each coefficient by its positive monomial weight identifies
the weighted coefficient algebra linearly with ℓ¹. -/
def weightedSeriesLpEquiv (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    WeightedSeries ρ hρ ≃ₗ[ℝ] lp (fun _ : σ →₀ ℕ => ℝ) 1 where
  toFun f := ⟨fun d => MvPowerSeries.coeff d f.val * multiRadiusWeight ρ d, by
    have hf : WeightedCoeffSummable ρ f.val := f.property
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    simpa only [WeightedCoeffSummable, ENNReal.toReal_one, Real.rpow_one, norm_mul,
      Real.norm_of_nonneg (multiRadiusWeight_nonneg (fun i => (hρ i).le) _)] using hf⟩
  invFun a := ⟨fun d => a d / multiRadiusWeight ρ d, by
    have ha := (lp.memℓp a).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_one, Real.rpow_one] at ha
    apply ha.congr
    intro d
    change ‖a d‖ = ‖a d / multiRadiusWeight ρ d‖ * multiRadiusWeight ρ d
    rw [norm_div, Real.norm_of_nonneg (multiRadiusWeight_pos hρ d).le,
      div_mul_cancel₀ _ (multiRadiusWeight_pos hρ d).ne']⟩
  left_inv f := by
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro d
    change (MvPowerSeries.coeff d f.val * multiRadiusWeight ρ d) /
      multiRadiusWeight ρ d = MvPowerSeries.coeff d f.val
    exact mul_div_cancel_right₀ _ (multiRadiusWeight_pos hρ d).ne'
  right_inv a := by
    apply Subtype.ext
    funext d
    change (a d / multiRadiusWeight ρ d) * multiRadiusWeight ρ d = a d
    exact div_mul_cancel₀ _ (multiRadiusWeight_pos hρ d).ne'
  map_add' f g := by
    apply Subtype.ext
    funext d
    change (MvPowerSeries.coeff d (f.val + g.val)) * multiRadiusWeight ρ d =
      MvPowerSeries.coeff d f.val * multiRadiusWeight ρ d +
        MvPowerSeries.coeff d g.val * multiRadiusWeight ρ d
    simp [map_add, add_mul]
  map_smul' c f := by
    apply Subtype.ext
    funext d
    change MvPowerSeries.coeff d (c • f.val) * multiRadiusWeight ρ d = _
    simp [mul_assoc]

@[simp]
theorem weightedSeriesLpEquiv_apply (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (f : WeightedSeries ρ hρ) (d : σ →₀ ℕ) :
    weightedSeriesLpEquiv ρ hρ f d =
      MvPowerSeries.coeff d f.val * multiRadiusWeight ρ d := rfl

instance weightedSeriesNormedAddCommGroup (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    NormedAddCommGroup (WeightedSeries ρ hρ) :=
  NormedAddCommGroup.induced _ _ (weightedSeriesLpEquiv ρ hρ)
    (weightedSeriesLpEquiv ρ hρ).injective

instance weightedSeriesNormedSpace (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    NormedSpace ℝ (WeightedSeries ρ hρ) :=
  NormedSpace.induced ℝ _ _ (weightedSeriesLpEquiv ρ hρ)

/-- The transported norm is the actual sum of weighted absolute coefficients. -/
theorem weightedSeries_norm_eq (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (f : WeightedSeries ρ hρ) : ‖f‖ = weightedCoeffNorm ρ f.val := by
  change ‖weightedSeriesLpEquiv ρ hρ f‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
  apply tsum_congr
  intro d
  rw [weightedSeriesLpEquiv_apply, norm_mul,
    Real.norm_of_nonneg (multiRadiusWeight_pos hρ d).le]

instance weightedSeriesNormedCommRing (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    NormedCommRing (WeightedSeries ρ hρ) where
  __ := (inferInstance : CommRing (WeightedSeries ρ hρ))
  __ := weightedSeriesNormedAddCommGroup ρ hρ
  norm_mul_le f g := by
    simp only [weightedSeries_norm_eq]
    exact weightedCoeffNorm_mul_le (fun i => (hρ i).le) f.property g.property

instance weightedSeriesNormedAlgebra (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    NormedAlgebra ℝ (WeightedSeries ρ hρ) where
  __ := (inferInstance : Algebra ℝ (WeightedSeries ρ hρ))
  norm_smul_le c f := by
    simp only [weightedSeries_norm_eq]
    exact le_of_eq (weightedCoeffNorm_smul ρ c f.val)

instance weightedSeriesNormOneClass (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    NormOneClass (WeightedSeries ρ hρ) where
  norm_one := by rw [weightedSeries_norm_eq]; exact weightedCoeffNorm_one ρ

/-- The coefficient identification is an isometry for the constructed norm. -/
def weightedSeriesLpIsometryEquiv (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    WeightedSeries ρ hρ ≃ₗᵢ[ℝ] lp (fun _ : σ →₀ ℕ => ℝ) 1 :=
  { weightedSeriesLpEquiv ρ hρ with norm_map' _ := rfl }

instance weightedSeriesCompleteSpace (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    CompleteSpace (WeightedSeries ρ hρ) :=
  (weightedSeriesLpIsometryEquiv ρ hρ).toIsometryEquiv.completeSpace

/-- Each weighted coefficient is bounded by the coefficient-sum norm. -/
theorem weightedSeries_coeff_weight_le_norm (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (f : WeightedSeries ρ hρ) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d f.val‖ * multiRadiusWeight ρ d ≤ ‖f‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (weightedSeriesLpEquiv ρ hρ f) d
  change _ ≤ ‖weightedSeriesLpEquiv ρ hρ f‖
  simpa only [weightedSeriesLpEquiv_apply, norm_mul,
    Real.norm_of_nonneg (multiRadiusWeight_pos hρ d).le] using h

/-- Coefficient extraction is a bounded real-linear map on the Banach algebra. -/
def weightedSeriesCoeffCLM (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    WeightedSeries ρ hρ →L[ℝ] ℝ :=
  ((MvPowerSeries.coeff d).comp (weightedSeriesSubalgebra ρ
    (fun i => (hρ i).le)).toSubmodule.subtype).mkContinuous
    (1 / multiRadiusWeight ρ d) fun f => by
      change ‖MvPowerSeries.coeff d f.val‖ ≤ (1 / multiRadiusWeight ρ d) * ‖f‖
      calc
        _ ≤ ‖f‖ / multiRadiusWeight ρ d :=
          (le_div_iff₀ (multiRadiusWeight_pos hρ d)).mpr
            (weightedSeries_coeff_weight_le_norm ρ hρ f d)
        _ = _ := by ring

@[simp]
theorem weightedSeriesCoeffCLM_apply (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) (f : WeightedSeries ρ hρ) :
    weightedSeriesCoeffCLM ρ hρ d f = MvPowerSeries.coeff d f.val := rfl

end AbelFormalization
