import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Field.Basic

/-! # Weighted absolute coefficient sums

Nonnegative polyradii define multiplicative weights on multiindices. The
corresponding absolutely summable coefficient series are closed under the
formal Cauchy product, with the expected submultiplicative bound.
-/

noncomputable section

namespace AbelFormalization

open Finset

variable {σ : Type*}

/-- The monomial weight associated with a family of real radii. -/
def multiRadiusWeight (ρ : σ → ℝ) (d : σ →₀ ℕ) : ℝ :=
  d.prod (fun i n => ρ i ^ n)

@[simp]
theorem multiRadiusWeight_zero (ρ : σ → ℝ) : multiRadiusWeight ρ 0 = 1 :=
  Finsupp.prod_zero_index

theorem multiRadiusWeight_add (ρ : σ → ℝ) (d e : σ →₀ ℕ) :
    multiRadiusWeight ρ (d + e) = multiRadiusWeight ρ d * multiRadiusWeight ρ e :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem multiRadiusWeight_nonneg {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (d : σ →₀ ℕ) :
    0 ≤ multiRadiusWeight ρ d :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (hρ i) _)

theorem multiRadiusWeight_pos {ρ : σ → ℝ} (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    0 < multiRadiusWeight ρ d :=
  Finset.prod_pos (fun i _ => pow_pos (hρ i) _)

/-- Absolute summability of the coefficients with the specified monomial weights. -/
def WeightedCoeffSummable (ρ : σ → ℝ) (f : MvPowerSeries σ ℝ) : Prop :=
  Summable (fun d => ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d)

/-- The weighted absolute coefficient sum. It is a norm on the summable
subspace when all radii are positive. -/
def weightedCoeffNorm (ρ : σ → ℝ) (f : MvPowerSeries σ ℝ) : ℝ :=
  ∑' d, ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d

theorem weightedCoeffNorm_nonneg {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (f : MvPowerSeries σ ℝ) : 0 ≤ weightedCoeffNorm ρ f :=
  tsum_nonneg (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))

@[simp]
theorem weightedCoeffSummable_zero (ρ : σ → ℝ) :
    WeightedCoeffSummable ρ (0 : MvPowerSeries σ ℝ) := by
  simp [WeightedCoeffSummable]

@[simp]
theorem weightedCoeffNorm_zero (ρ : σ → ℝ) :
    weightedCoeffNorm ρ (0 : MvPowerSeries σ ℝ) = 0 := by
  simp [weightedCoeffNorm]

theorem weightedCoeffSummable_one (ρ : σ → ℝ) :
    WeightedCoeffSummable ρ (1 : MvPowerSeries σ ℝ) := by
  classical
  apply summable_of_ne_finset_zero (s := {0})
  intro d hd
  have hd' : d ≠ 0 := by simpa only [mem_singleton] using hd
  simp [MvPowerSeries.coeff_one, hd']

@[simp]
theorem weightedCoeffNorm_one (ρ : σ → ℝ) :
    weightedCoeffNorm ρ (1 : MvPowerSeries σ ℝ) = 1 := by
  classical
  unfold weightedCoeffNorm
  rw [tsum_eq_single 0 (fun d hd => by simp [MvPowerSeries.coeff_one, hd])]
  simp [MvPowerSeries.coeff_one]

theorem weightedCoeffSummable_neg {ρ : σ → ℝ} {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) : WeightedCoeffSummable ρ (-f) := by
  simpa only [WeightedCoeffSummable, map_neg, norm_neg] using hf

@[simp]
theorem weightedCoeffNorm_neg (ρ : σ → ℝ) (f : MvPowerSeries σ ℝ) :
    weightedCoeffNorm ρ (-f) = weightedCoeffNorm ρ f := by
  simp only [weightedCoeffNorm, map_neg, norm_neg]

theorem weightedCoeffSummable_smul {ρ : σ → ℝ} {f : MvPowerSeries σ ℝ}
    (c : ℝ) (hf : WeightedCoeffSummable ρ f) : WeightedCoeffSummable ρ (c • f) := by
  simpa only [WeightedCoeffSummable, MvPowerSeries.coeff_smul, norm_mul, mul_assoc]
    using hf.mul_left ‖c‖

@[simp]
theorem weightedCoeffNorm_smul (ρ : σ → ℝ) (c : ℝ) (f : MvPowerSeries σ ℝ) :
    weightedCoeffNorm ρ (c • f) = ‖c‖ * weightedCoeffNorm ρ f := by
  simp only [weightedCoeffNorm, MvPowerSeries.coeff_smul, norm_mul, mul_assoc, tsum_mul_left]

theorem weightedCoeffSummable_C (ρ : σ → ℝ) (c : ℝ) :
    WeightedCoeffSummable ρ (MvPowerSeries.C c) := by
  simpa only [MvPowerSeries.smul_eq_C_mul, mul_one] using
    weightedCoeffSummable_smul c (weightedCoeffSummable_one ρ)

@[simp]
theorem weightedCoeffNorm_C (ρ : σ → ℝ) (c : ℝ) :
    weightedCoeffNorm ρ (MvPowerSeries.C c) = ‖c‖ := by
  simpa only [MvPowerSeries.smul_eq_C_mul, mul_one, weightedCoeffNorm_one] using
    weightedCoeffNorm_smul ρ c (1 : MvPowerSeries σ ℝ)

theorem weightedCoeffSummable_add {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) : WeightedCoeffSummable ρ (f + g) := by
  apply (hf.add hg).of_nonneg_of_le
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
  intro d
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (multiRadiusWeight_nonneg hρ d)

theorem weightedCoeffNorm_add_le {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    weightedCoeffNorm ρ (f + g) ≤ weightedCoeffNorm ρ f + weightedCoeffNorm ρ g := by
  rw [weightedCoeffNorm, weightedCoeffNorm, weightedCoeffNorm, ← hf.tsum_add hg]
  apply Summable.tsum_le_tsum _ (weightedCoeffSummable_add hρ hf hg) (hf.add hg)
  intro d
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (multiRadiusWeight_nonneg hρ d)

/-- The coefficientwise weighted Cauchy-product bound. -/
theorem weightedCoeff_mul_le [DecidableEq σ] {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (f g : MvPowerSeries σ ℝ) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (f * g)‖ * multiRadiusWeight ρ d ≤
      ∑ e ∈ antidiagonal d,
        (‖MvPowerSeries.coeff e.1 f‖ * multiRadiusWeight ρ e.1) *
        (‖MvPowerSeries.coeff e.2 g‖ * multiRadiusWeight ρ e.2) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  calc
    _ ≤ (∑ e ∈ antidiagonal d,
        ‖MvPowerSeries.coeff e.1 f * MvPowerSeries.coeff e.2 g‖) * multiRadiusWeight ρ d :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (multiRadiusWeight_nonneg hρ d)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [← mem_antidiagonal.mp he, multiRadiusWeight_add, norm_mul]
      ring

private theorem weightedCoeff_product_summable {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    Summable (fun e : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      (‖MvPowerSeries.coeff e.1 f‖ * multiRadiusWeight ρ e.1) *
      (‖MvPowerSeries.coeff e.2 g‖ * multiRadiusWeight ρ e.2)) :=
  hf.mul_of_nonneg hg
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))

private theorem weightedCoeff_antidiagonal_summable [DecidableEq σ]
    {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    Summable (fun d : σ →₀ ℕ => ∑ e ∈ antidiagonal d,
      (‖MvPowerSeries.coeff e.1 f‖ * multiRadiusWeight ρ e.1) *
      (‖MvPowerSeries.coeff e.2 g‖ * multiRadiusWeight ρ e.2)) :=
  summable_sum_mul_antidiagonal_of_summable_mul
    (f := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d)
    (g := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d g‖ * multiRadiusWeight ρ d)
    (weightedCoeff_product_summable hρ hf hg)

/-- Weighted absolute summability is preserved by the formal Cauchy product. -/
theorem weightedCoeffSummable_mul {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) : WeightedCoeffSummable ρ (f * g) := by
  classical
  exact (weightedCoeff_antidiagonal_summable hρ hf hg).of_nonneg_of_le
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
    (weightedCoeff_mul_le hρ f g)

/-- The weighted absolute coefficient norm is submultiplicative. -/
theorem weightedCoeffNorm_mul_le {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    weightedCoeffNorm ρ (f * g) ≤ weightedCoeffNorm ρ f * weightedCoeffNorm ρ g := by
  classical
  have hprod := weightedCoeff_product_summable hρ hf hg
  have he := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (f := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d)
    (g := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d g‖ * multiRadiusWeight ρ d)
    hf hg hprod
  rw [weightedCoeffNorm, weightedCoeffNorm, weightedCoeffNorm, he]
  exact Summable.tsum_le_tsum (weightedCoeff_mul_le hρ f g)
    (weightedCoeffSummable_mul hρ hf hg)
    (weightedCoeff_antidiagonal_summable hρ hf hg)

end AbelFormalization
