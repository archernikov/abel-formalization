import AbelFormalization.WeightedSeries

/-! # Convergent pointwise evaluation of weighted series

A weighted absolutely summable formal series evaluates absolutely at every
point bounded by its polyradii. Evaluation obeys the algebra laws and is
bounded by the coefficient norm. These are pointwise convergence statements;
they do not yet assert that the evaluated function is analytic.
-/

noncomputable section

namespace AbelFormalization

open Finset

variable {σ : Type*}

/-- A monomial evaluated inside a polydisk is bounded by its radius weight. -/
theorem norm_multiRadiusWeight_le {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    (d : σ →₀ ℕ) : ‖multiRadiusWeight x d‖ ≤ multiRadiusWeight ρ d := by
  simp only [multiRadiusWeight, Finsupp.prod, norm_prod, norm_pow, Real.norm_eq_abs]
  exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg (x i)) _)
    (fun i _ => pow_le_pow_left₀ (abs_nonneg (x i)) (hx i) _)

/-- Actual evaluation by summing the monomials. On the weighted summability
domain, the series is absolutely convergent by `weightedSeriesEval_norm_summable`. -/
def weightedSeriesEval (f : MvPowerSeries σ ℝ) (x : σ → ℝ) : ℝ :=
  ∑' d, MvPowerSeries.coeff d f * multiRadiusWeight x d

theorem weightedSeriesEval_term_norm_le {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    (f : MvPowerSeries σ ℝ) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d f * multiRadiusWeight x d‖ ≤
      ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_multiRadiusWeight_le hx d) (norm_nonneg _)

/-- Absolute convergence of the actual monomial evaluations. -/
theorem weightedSeriesEval_norm_summable {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    Summable (fun d => ‖MvPowerSeries.coeff d f * multiRadiusWeight x d‖) :=
  hf.of_nonneg_of_le (fun _ => norm_nonneg _) (weightedSeriesEval_term_norm_le hx f)

theorem weightedSeriesEval_summable {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    Summable (fun d => MvPowerSeries.coeff d f * multiRadiusWeight x d) :=
  (weightedSeriesEval_norm_summable hx hf).of_norm

/-- Evaluation has operator bound one with respect to the weighted coefficient sum. -/
theorem norm_weightedSeriesEval_le {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    ‖weightedSeriesEval f x‖ ≤ weightedCoeffNorm ρ f :=
  tsum_of_norm_bounded hf.hasSum (weightedSeriesEval_term_norm_le hx f)

theorem abs_weightedSeriesEval_le {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    |weightedSeriesEval f x| ≤ weightedCoeffNorm ρ f :=
  norm_weightedSeriesEval_le hx hf

@[simp]
theorem weightedSeriesEval_zero (x : σ → ℝ) :
    weightedSeriesEval (0 : MvPowerSeries σ ℝ) x = 0 := by
  simp [weightedSeriesEval]

@[simp]
theorem weightedSeriesEval_neg (f : MvPowerSeries σ ℝ) (x : σ → ℝ) :
    weightedSeriesEval (-f) x = -weightedSeriesEval f x := by
  simp only [weightedSeriesEval, map_neg, neg_mul, tsum_neg]

@[simp]
theorem weightedSeriesEval_smul (c : ℝ) (f : MvPowerSeries σ ℝ) (x : σ → ℝ) :
    weightedSeriesEval (c • f) x = c * weightedSeriesEval f x := by
  simp only [weightedSeriesEval, MvPowerSeries.coeff_smul, mul_assoc, tsum_mul_left]

theorem weightedSeriesEval_add {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    weightedSeriesEval (f + g) x = weightedSeriesEval f x + weightedSeriesEval g x := by
  simp only [weightedSeriesEval, map_add, add_mul]
  exact (weightedSeriesEval_summable hx hf).tsum_add (weightedSeriesEval_summable hx hg)

/-- Evaluation commutes with the Cauchy product, by absolute convergence. -/
theorem weightedSeriesEval_mul {ρ x : σ → ℝ} (hx : ∀ i, |x i| ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    weightedSeriesEval (f * g) x = weightedSeriesEval f x * weightedSeriesEval g x := by
  classical
  have hfabs := weightedSeriesEval_norm_summable hx hf
  have hgabs := weightedSeriesEval_norm_summable hx hg
  have hprod := summable_mul_of_summable_norm hfabs hgabs
  have he := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (f := fun d : σ →₀ ℕ => MvPowerSeries.coeff d f * multiRadiusWeight x d)
    (g := fun d : σ →₀ ℕ => MvPowerSeries.coeff d g * multiRadiusWeight x d)
    (weightedSeriesEval_summable hx hf) (weightedSeriesEval_summable hx hg) hprod
  unfold weightedSeriesEval
  rw [he]
  apply tsum_congr
  intro d
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [← mem_antidiagonal.mp he, multiRadiusWeight_add]
  ring

@[simp]
theorem weightedSeriesEval_monomial (d : σ →₀ ℕ) (c : ℝ) (x : σ → ℝ) :
    weightedSeriesEval (MvPowerSeries.monomial d c) x = c * multiRadiusWeight x d := by
  classical
  unfold weightedSeriesEval
  rw [tsum_eq_single d (fun e he => by rw [MvPowerSeries.coeff_monomial_ne he, zero_mul])]
  rw [MvPowerSeries.coeff_monomial_same]

@[simp]
theorem weightedSeriesEval_C (c : ℝ) (x : σ → ℝ) :
    weightedSeriesEval (MvPowerSeries.C c) x = c := by
  change weightedSeriesEval (MvPowerSeries.monomial 0 c) x = c
  rw [weightedSeriesEval_monomial, multiRadiusWeight_zero, mul_one]

@[simp]
theorem weightedSeriesEval_one (x : σ → ℝ) :
    weightedSeriesEval (1 : MvPowerSeries σ ℝ) x = 1 := by
  simpa only [map_one] using weightedSeriesEval_C 1 x

@[simp]
theorem weightedSeriesEval_X (i : σ) (x : σ → ℝ) :
    weightedSeriesEval (MvPowerSeries.X i) x = x i := by
  rw [MvPowerSeries.X, weightedSeriesEval_monomial, one_mul]
  change (Finsupp.single i 1).prod (fun j n => x j ^ n) = x i
  rw [Finsupp.prod_single_index (h := fun j n => x j ^ n) (pow_zero _), pow_one]

end AbelFormalization
