import AbelFormalization.WeightedSeriesDivision
import AbelFormalization.WeightedSeriesRestriction

/-! # Anisotropic smallness of a regular weighted series

A series whose distinguished-axis coefficients vanish below degree `n`, and
whose degree-`n` axis coefficient is one, becomes close to `X i ^ n` in a
smaller weighted norm. The distinguished radius is multiplied by `t`, while
all other radii are multiplied by `t ^ (n + 1)`. Every surviving error term
then has scaling degree at least `n + 1`. This gives a quantitative estimate
and proves the strict smallness hypothesis needed for Banach division.

This is a theorem about actual summable weighted coefficient series. Passing
between these series and analytic germs is handled separately.
-/

noncomputable section

namespace AbelFormalization

variable {σ : Type*}

/-- Scaling exponent one on the distinguished coordinate, and `n + 1` elsewhere. -/
def regularScalingExponent (i : σ) (n : ℕ) (j : σ) : ℕ := by
  classical
  exact if j = i then 1 else n + 1

@[simp]
theorem regularScalingExponent_self (i : σ) (n : ℕ) :
    regularScalingExponent i n i = 1 := by
  simp [regularScalingExponent]

theorem regularScalingExponent_pos (i : σ) (n : ℕ) (j : σ) :
    0 < regularScalingExponent i n j := by
  classical
  simp only [regularScalingExponent]
  split_ifs <;> omega

/-- The degree of a monomial under the anisotropic scaling. -/
def regularScalingDegree (i : σ) (n : ℕ) (d : σ →₀ ℕ) : ℕ :=
  d.sum (fun j k => regularScalingExponent i n j * k)

theorem regularScalingDegree_term_le (i : σ) (n : ℕ) (d : σ →₀ ℕ) (j : σ) :
    regularScalingExponent i n j * d j ≤ regularScalingDegree i n d := by
  classical
  by_cases hj : d j = 0
  · simp [hj]
  · change regularScalingExponent i n j * d j ≤
      ∑ k ∈ d.support, regularScalingExponent i n k * d k
    exact Finset.single_le_sum (f := fun k => regularScalingExponent i n k * d k)
      (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hj)

/-- Scaling degree at most `n` forces a monomial onto the distinguished axis. -/
theorem regularScalingDegree_le_imp_axis (i : σ) (n : ℕ) (d : σ →₀ ℕ)
    (hd : regularScalingDegree i n d ≤ n) :
    d = Finsupp.single i (d i) ∧ d i ≤ n := by
  classical
  have hi : d i ≤ n := by
    simpa only [regularScalingExponent_self, one_mul] using
      (regularScalingDegree_term_le i n d i).trans hd
  refine ⟨?_, hi⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · have hj := (regularScalingDegree_term_le i n d j).trans hd
    simp only [regularScalingExponent, ite_eq_right hji] at hj
    have hdj : d j = 0 := by
      by_contra hj0
      have hj1 : 1 ≤ d j := Nat.one_le_iff_ne_zero.mpr hj0
      have hlow : n + 1 ≤ (n + 1) * d j := by
        simpa only [mul_one] using Nat.mul_le_mul_left (n + 1) hj1
      omega
    rw [hdj, Finsupp.single_eq_of_ne hji]

/-- The smaller radii used in regular division. -/
def regularScaledRadius (ρ : σ → ℝ) (i : σ) (n : ℕ) (t : ℝ) (j : σ) : ℝ :=
  ρ j * t ^ regularScalingExponent i n j

@[simp]
theorem regularScaledRadius_self (ρ : σ → ℝ) (i : σ) (n : ℕ) (t : ℝ) :
    regularScaledRadius ρ i n t i = ρ i * t := by
  simp [regularScaledRadius]

theorem regularScaledRadius_pos {ρ : σ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (i : σ) (n : ℕ) {t : ℝ} (ht : 0 < t) (j : σ) :
    0 < regularScaledRadius ρ i n t j :=
  mul_pos (hρ j) (pow_pos ht _)

theorem regularScaledRadius_le {ρ : σ → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (i : σ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (j : σ) :
    regularScaledRadius ρ i n t j ≤ ρ j := by
  exact mul_le_of_le_one_right (hρ j) (pow_le_one₀ ht ht1)

theorem regularScaledRadius_lt {ρ : σ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (i : σ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (j : σ) :
    regularScaledRadius ρ i n t j < ρ j := by
  exact mul_lt_of_lt_one_right (hρ j)
    (pow_lt_one₀ ht ht1 (regularScalingExponent_pos i n j).ne')

/-- Every monomial acquires exactly its anisotropic scaling degree. -/
theorem multiRadiusWeight_regularScaledRadius (ρ : σ → ℝ) (i : σ) (n : ℕ)
    (t : ℝ) (d : σ →₀ ℕ) :
    multiRadiusWeight (regularScaledRadius ρ i n t) d =
      multiRadiusWeight ρ d * t ^ regularScalingDegree i n d := by
  classical
  simp only [multiRadiusWeight, regularScaledRadius, Finsupp.prod, mul_pow,
    ← pow_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    regularScalingDegree, Finsupp.sum]

/-- Normalized regularity eliminates all error coefficients of scaling degree
at most `n`. -/
theorem regular_error_coeff_eq_zero (i : σ) (n : ℕ) (f : MvPowerSeries σ ℝ)
    (hvanish : ∀ k < n, MvPowerSeries.coeff (Finsupp.single i k) f = 0)
    (hnormalized : MvPowerSeries.coeff (Finsupp.single i n) f = 1)
    (d : σ →₀ ℕ) (hd : regularScalingDegree i n d ≤ n) :
    MvPowerSeries.coeff d (MvPowerSeries.X i ^ n - f) = 0 := by
  classical
  obtain ⟨heq, hle⟩ := regularScalingDegree_le_imp_axis i n d hd
  rw [heq, map_sub, MvPowerSeries.X_pow_eq]
  rcases hle.eq_or_lt with h | h
  · simp [h, hnormalized]
  · have hne : Finsupp.single i (d i) ≠ Finsupp.single i n := by
      intro he
      have := congrArg (fun a : σ →₀ ℕ => a i) he
      simp only [Finsupp.single_eq_same] at this
      omega
    rw [MvPowerSeries.coeff_monomial_ne hne, hvanish _ h, sub_self]

/-- A weighted coefficient estimate valid for every `0 ≤ t ≤ 1`. -/
theorem weightedCoeffNorm_regularScaling_le {ρ : σ → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (i : σ) (n : ℕ) (f : MvPowerSeries σ ℝ) (hf : WeightedCoeffSummable ρ f)
    (hdegree : ∀ d, regularScalingDegree i n d ≤ n → MvPowerSeries.coeff d f = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    weightedCoeffNorm (regularScaledRadius ρ i n t) f ≤
      t ^ (n + 1) * weightedCoeffNorm ρ f := by
  have hs : WeightedCoeffSummable (regularScaledRadius ρ i n t) f :=
    weightedCoeffSummable_of_radius_le
      (fun j => mul_nonneg (hρ j) (pow_nonneg ht _))
      (regularScaledRadius_le hρ i n ht ht1) hf
  rw [weightedCoeffNorm, weightedCoeffNorm, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hs (hf.mul_left _)
  intro d
  by_cases hd : regularScalingDegree i n d ≤ n
  · simp [hdegree d hd]
  · have hdeg : n + 1 ≤ regularScalingDegree i n d := by omega
    have hpow := pow_le_pow_of_le_one ht ht1 hdeg
    rw [multiRadiusWeight_regularScaledRadius]
    calc
      _ = (‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d) *
          t ^ regularScalingDegree i n d := by ring
      _ ≤ (‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d) * t ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
      _ = _ := by ring

/-- The error norm has an extra factor of `t` beyond the leading monomial. -/
theorem weightedCoeffNorm_regular_error_le {ρ : σ → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (i : σ) (n : ℕ) (f : MvPowerSeries σ ℝ) (hf : WeightedCoeffSummable ρ f)
    (hvanish : ∀ k < n, MvPowerSeries.coeff (Finsupp.single i k) f = 0)
    (hnormalized : MvPowerSeries.coeff (Finsupp.single i n) f = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    weightedCoeffNorm (regularScaledRadius ρ i n t) (MvPowerSeries.X i ^ n - f) ≤
      t ^ (n + 1) * weightedCoeffNorm ρ (MvPowerSeries.X i ^ n - f) := by
  apply weightedCoeffNorm_regularScaling_le hρ i n _ _
    (regular_error_coeff_eq_zero i n f hvanish hnormalized) ht ht1
  simpa only [sub_eq_add_neg, MvPowerSeries.X_pow_eq] using
    weightedCoeffSummable_add hρ (weightedCoeffSummable_monomial ρ _ 1)
      (weightedCoeffSummable_neg hf)

/-- Normalized distinguished-axis regularity implies the strict weighted norm
bound for division at some strictly smaller positive polyradii. -/
theorem exists_regular_radius_smallness {ρ : σ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (i : σ) (n : ℕ) (f : MvPowerSeries σ ℝ) (hf : WeightedCoeffSummable ρ f)
    (hvanish : ∀ k < n, MvPowerSeries.coeff (Finsupp.single i k) f = 0)
    (hnormalized : MvPowerSeries.coeff (Finsupp.single i n) f = 1) :
    ∃ τ : σ → ℝ, (∀ j, 0 < τ j) ∧ (∀ j, τ j < ρ j) ∧
      WeightedCoeffSummable τ f ∧
      weightedCoeffNorm τ (MvPowerSeries.X i ^ n - f) < τ i ^ n := by
  let C := weightedCoeffNorm ρ (MvPowerSeries.X i ^ n - f)
  have hC : 0 ≤ C := weightedCoeffNorm_nonneg (fun j => (hρ j).le) _
  obtain ⟨c, hc, hcsmall⟩ := exists_pos_mul_lt (pow_pos (hρ i) n) C
  let t : ℝ := min c (1 / 2)
  have ht : 0 < t := lt_min hc (by norm_num)
  have ht1 : t < 1 := (min_le_right c (1 / 2)).trans_lt (by norm_num)
  have hsmall : t * C < ρ i ^ n := by
    calc
      t * C ≤ c * C := mul_le_mul_of_nonneg_right (min_le_left _ _) hC
      _ < ρ i ^ n := by simpa only [mul_comm] using hcsmall
  refine ⟨regularScaledRadius ρ i n t, regularScaledRadius_pos hρ i n ht,
    regularScaledRadius_lt hρ i n ht.le ht1,
    weightedCoeffSummable_of_radius_le
      (fun j => (regularScaledRadius_pos hρ i n ht j).le)
      (regularScaledRadius_le (fun j => (hρ j).le) i n ht.le ht1.le) hf, ?_⟩
  calc
    _ ≤ t ^ (n + 1) * C :=
      weightedCoeffNorm_regular_error_le (fun j => (hρ j).le) i n f hf
        hvanish hnormalized ht.le ht1.le
    _ = t ^ n * (t * C) := by rw [pow_succ]; ring
    _ < t ^ n * (ρ i ^ n) := mul_lt_mul_of_pos_left hsmall (pow_pos ht n)
    _ = _ := by rw [regularScaledRadius_self, mul_pow]; ring

/-- After shrinking the radii, every summable dividend has a unique summable
quotient whose remainder has distinguished-coordinate degree less than `n`.
The contraction bound is a conclusion of normalized regularity, not an
additional assumption. -/
theorem exists_regular_weighted_division {ρ : σ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (i : σ) (n : ℕ) (f : MvPowerSeries σ ℝ) (hf : WeightedCoeffSummable ρ f)
    (hvanish : ∀ k < n, MvPowerSeries.coeff (Finsupp.single i k) f = 0)
    (hnormalized : MvPowerSeries.coeff (Finsupp.single i n) f = 1) :
    ∃ τ : σ → ℝ, (∀ j, 0 < τ j) ∧ (∀ j, τ j < ρ j) ∧
      WeightedCoeffSummable τ f ∧
      ∀ g : MvPowerSeries σ ℝ, WeightedCoeffSummable τ g →
        ∃! q : MvPowerSeries σ ℝ, WeightedCoeffSummable τ q ∧
          ∀ k : σ →₀ ℕ, n ≤ k i → MvPowerSeries.coeff k (g - f * q) = 0 := by
  obtain ⟨τ, hτ, hτρ, hfτ, hsmall⟩ :=
    exists_regular_radius_smallness hρ i n f hf hvanish hnormalized
  refine ⟨τ, hτ, hτρ, hfτ, ?_⟩
  intro g hg
  let F : WeightedSeries τ hτ := ⟨f, hfτ⟩
  let G : WeightedSeries τ hτ := ⟨g, hg⟩
  obtain ⟨q, hq, huniq⟩ :=
    weightedSeries_coordinate_division_existsUnique τ hτ i n F G hsmall
  refine ⟨q.val, ⟨q.property, hq⟩, ?_⟩
  intro q' hq'
  exact congrArg Subtype.val (huniq ⟨q', hq'.1⟩ hq'.2)

end AbelFormalization
