import AbelFormalization.WeightedSeriesBanach
import AbelFormalization.BanachDivision
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Convergent coefficient-tail division

Coefficient tails preserve weighted absolute summability and are bounded
linear operators on the actual weighted-series Banach algebra. They divide
the corresponding coordinate monomials exactly. Neumann division therefore
applies to series whose weighted coefficient distance from that monomial is
small enough. The remainder has no coefficients of sufficiently high degree
in the selected coordinate.

The conclusions concern weighted convergent coefficient series. Identifying
these series with analytic germs and obtaining the required smallness from
analytic regularity are separate obligations.
-/

noncomputable section

namespace AbelFormalization

variable {σ : Type*}

@[simp]
theorem multiRadiusWeight_single (ρ : σ → ℝ) (i : σ) (n : ℕ) :
    multiRadiusWeight ρ (Finsupp.single i n) = ρ i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

/-- Every monomial has finite weighted coefficient support. -/
theorem weightedCoeffSummable_monomial (ρ : σ → ℝ) (d : σ →₀ ℕ) (c : ℝ) :
    WeightedCoeffSummable ρ (MvPowerSeries.monomial d c) := by
  classical
  apply summable_of_ne_finset_zero (s := {d})
  intro k hk
  have hkd : k ≠ d := by simpa only [Finset.mem_singleton] using hk
  simp [MvPowerSeries.coeff_monomial, hkd]

@[simp]
theorem weightedCoeffNorm_monomial (ρ : σ → ℝ) (d : σ →₀ ℕ) (c : ℝ) :
    weightedCoeffNorm ρ (MvPowerSeries.monomial d c) = ‖c‖ * multiRadiusWeight ρ d := by
  classical
  unfold weightedCoeffNorm
  rw [tsum_eq_single d (fun k hk => by simp [MvPowerSeries.coeff_monomial, hk])]
  simp [MvPowerSeries.coeff_monomial_same]

/-- The formal coefficient tail by an arbitrary multiindex. -/
def mvPowerSeriesTail (d : σ →₀ ℕ) : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ where
  toFun f := fun k => MvPowerSeries.coeff (k + d) f
  map_add' f g := by
    apply MvPowerSeries.ext
    intro k
    exact map_add (MvPowerSeries.coeff (k + d)) f g
  map_smul' c f := by
    apply MvPowerSeries.ext
    intro k
    exact MvPowerSeries.coeff_smul f (k + d) c

@[simp]
theorem coeff_mvPowerSeriesTail (d k : σ →₀ ℕ) (f : MvPowerSeries σ ℝ) :
    MvPowerSeries.coeff k (mvPowerSeriesTail d f) = MvPowerSeries.coeff (k + d) f := rfl

/-- Shifting the coefficient index removes exactly the monomial's weight. -/
theorem weightedCoeff_tail_identity (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d k : σ →₀ ℕ) (f : MvPowerSeries σ ℝ) :
    ‖MvPowerSeries.coeff k (mvPowerSeriesTail d f)‖ * multiRadiusWeight ρ k =
      (‖MvPowerSeries.coeff (k + d) f‖ * multiRadiusWeight ρ (k + d)) /
        multiRadiusWeight ρ d := by
  rw [coeff_mvPowerSeriesTail, multiRadiusWeight_add, ← mul_assoc,
    mul_div_cancel_right₀ _ (multiRadiusWeight_pos hρ d).ne']

/-- Absolute summability of a coefficient tail follows by injectively
reindexing the original absolutely summable family. -/
theorem weightedCoeffSummable_tail (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    WeightedCoeffSummable ρ (mvPowerSeriesTail d f) := by
  have ht := hf.comp_injective (add_left_injective d)
  have hd := ht.div_const (multiRadiusWeight ρ d)
  apply hd.congr
  intro k
  exact (weightedCoeff_tail_identity ρ hρ d k f).symm

/-- The coefficient-tail bound, before passage to the Banach algebra. -/
theorem weightedCoeffNorm_tail_le (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    weightedCoeffNorm ρ (mvPowerSeriesTail d f) ≤
      weightedCoeffNorm ρ f / multiRadiusWeight ρ d := by
  unfold weightedCoeffNorm
  simp_rw [weightedCoeff_tail_identity ρ hρ d]
  rw [tsum_div_const]
  apply div_le_div_of_nonneg_right _ (multiRadiusWeight_pos hρ d).le
  exact tsum_comp_le_tsum_of_inj hf
    (fun k => mul_nonneg (norm_nonneg _) (multiRadiusWeight_pos hρ k).le)
    (add_left_injective d)

/-- The coefficient tail as a linear operator on weighted summable series. -/
def weightedSeriesTailLinear (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    WeightedSeries ρ hρ →ₗ[ℝ] WeightedSeries ρ hρ where
  toFun f := ⟨mvPowerSeriesTail d f.val, weightedCoeffSummable_tail ρ hρ d f.property⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (mvPowerSeriesTail d) f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (mvPowerSeriesTail d) c f.val

/-- Division by a monomial on coefficient tails is a bounded real-linear map. -/
def weightedSeriesTailCLM (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    WeightedSeries ρ hρ →L[ℝ] WeightedSeries ρ hρ :=
  (weightedSeriesTailLinear ρ hρ d).mkContinuous (1 / multiRadiusWeight ρ d) fun f => by
    rw [weightedSeries_norm_eq, weightedSeries_norm_eq]
    calc
      _ ≤ weightedCoeffNorm ρ f.val / multiRadiusWeight ρ d :=
        weightedCoeffNorm_tail_le ρ hρ d f.property
      _ = _ := by ring

@[simp]
theorem weightedSeriesTailCLM_coeff (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d k : σ →₀ ℕ) (f : WeightedSeries ρ hρ) :
    MvPowerSeries.coeff k (weightedSeriesTailCLM ρ hρ d f).val =
      MvPowerSeries.coeff (k + d) f.val := rfl

theorem weightedSeriesTailCLM_opNorm_le (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    ‖weightedSeriesTailCLM ρ hρ d‖ ≤ 1 / multiRadiusWeight ρ d :=
  LinearMap.mkContinuous_norm_le _
    (div_nonneg zero_le_one (multiRadiusWeight_pos hρ d).le) _

/-- The expected inverse-power norm bound for a tail in one coordinate. -/
theorem weightedSeriesTailCLM_coordinate_opNorm_le (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (i : σ) (n : ℕ) :
    ‖weightedSeriesTailCLM ρ hρ (Finsupp.single i n)‖ ≤ (ρ i ^ n)⁻¹ := by
  simpa only [multiRadiusWeight_single, one_div] using
    weightedSeriesTailCLM_opNorm_le ρ hρ (Finsupp.single i n)

/-- A monomial as an element of the actual Banach algebra. -/
def weightedSeriesMonomial (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) (c : ℝ) :
    WeightedSeries ρ hρ :=
  ⟨MvPowerSeries.monomial d c, weightedCoeffSummable_monomial ρ d c⟩

@[simp]
theorem weightedSeriesMonomial_norm (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) (c : ℝ) :
    ‖weightedSeriesMonomial ρ hρ d c‖ = ‖c‖ * multiRadiusWeight ρ d := by
  rw [weightedSeries_norm_eq]
  exact weightedCoeffNorm_monomial ρ d c

/-- The coordinate variable as a weighted summable power series. -/
def weightedSeriesX (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (i : σ) : WeightedSeries ρ hρ :=
  weightedSeriesMonomial ρ hρ (Finsupp.single i 1) 1

@[simp]
theorem weightedSeriesX_val (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (i : σ) :
    (weightedSeriesX ρ hρ i).val = MvPowerSeries.X i := rfl

theorem weightedSeriesX_pow (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (i : σ) (n : ℕ) :
    weightedSeriesX ρ hρ i ^ n = weightedSeriesMonomial ρ hρ (Finsupp.single i n) 1 := by
  apply Subtype.ext
  exact MvPowerSeries.X_pow_eq i n

/-- Coefficient-tail division is a left inverse to multiplication by its
monomial. No smallness assumption is used in this exact identity. -/
theorem weightedSeriesTailCLM_monomial_mul (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) (f : WeightedSeries ρ hρ) :
    weightedSeriesTailCLM ρ hρ d (weightedSeriesMonomial ρ hρ d 1 * f) = f := by
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro k
  change MvPowerSeries.coeff (k + d) (MvPowerSeries.monomial d 1 * f.val) =
    MvPowerSeries.coeff k f.val
  rw [add_comm k d, MvPowerSeries.coeff_add_monomial_mul, one_mul]

theorem weightedSeriesTailCLM_X_pow_mul (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (i : σ) (n : ℕ) (f : WeightedSeries ρ hρ) :
    weightedSeriesTailCLM ρ hρ (Finsupp.single i n) (weightedSeriesX ρ hρ i ^ n * f) = f := by
  rw [weightedSeriesX_pow]
  exact weightedSeriesTailCLM_monomial_mul ρ hρ _ f

/-- The tail bound is sharp, as witnessed by its monomial divisor. -/
theorem weightedSeriesTailCLM_opNorm (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    ‖weightedSeriesTailCLM ρ hρ d‖ = 1 / multiRadiusWeight ρ d := by
  apply le_antisymm (weightedSeriesTailCLM_opNorm_le ρ hρ d)
  have he : weightedSeriesTailCLM ρ hρ d (weightedSeriesMonomial ρ hρ d 1) = 1 := by
    simpa only [mul_one] using weightedSeriesTailCLM_monomial_mul ρ hρ d 1
  have hn := (weightedSeriesTailCLM ρ hρ d).le_opNorm (weightedSeriesMonomial ρ hρ d 1)
  rw [he, norm_one, weightedSeriesMonomial_norm, norm_one, one_mul] at hn
  exact (div_le_iff₀ (multiRadiusWeight_pos hρ d)).mpr hn

theorem weightedSeriesTailCLM_eq_zero_iff (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) (f : WeightedSeries ρ hρ) :
    weightedSeriesTailCLM ρ hρ d f = 0 ↔
      ∀ k, MvPowerSeries.coeff (k + d) f.val = 0 := by
  constructor
  · intro hf k
    have he := congrArg (fun a : WeightedSeries ρ hρ => MvPowerSeries.coeff k a.val) hf
    simpa only [weightedSeriesTailCLM_coeff, ZeroMemClass.coe_zero, map_zero] using he
  · intro hf
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro k
    exact hf k

/-- Vanishing of a coordinate tail is exactly the absence of coefficients
whose degree in that coordinate is at least `n`. -/
theorem weightedSeriesTailCLM_coordinate_eq_zero_iff (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (i : σ) (n : ℕ) (f : WeightedSeries ρ hρ) :
    weightedSeriesTailCLM ρ hρ (Finsupp.single i n) f = 0 ↔
      ∀ k : σ →₀ ℕ, n ≤ k i → MvPowerSeries.coeff k f.val = 0 := by
  rw [weightedSeriesTailCLM_eq_zero_iff]
  constructor
  · intro hf k hk
    have hd : Finsupp.single i n ≤ k := Finsupp.single_le_iff.mpr hk
    simpa only [tsub_add_cancel_of_le hd] using hf (k - Finsupp.single i n)
  · intro hf k
    apply hf
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_left _ _

/-- A genuinely small weighted coefficient perturbation gives the strict
operator contraction needed by Neumann division. -/
theorem weightedSeriesDivision_contraction (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) (f : WeightedSeries ρ hρ)
    (hsmall : weightedCoeffNorm ρ ((weightedSeriesMonomial ρ hρ d 1).val - f.val) <
      multiRadiusWeight ρ d) :
    ‖divisionPerturbation (weightedSeriesTailCLM ρ hρ d)
      (weightedSeriesMonomial ρ hρ d 1) f‖ < 1 := by
  have hn : ‖weightedSeriesMonomial ρ hρ d 1 - f‖ < multiRadiusWeight ρ d := by
    rwa [weightedSeries_norm_eq]
  apply (norm_divisionPerturbation_le _ _ _).trans_lt
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (weightedSeriesTailCLM_opNorm_le ρ hρ d) (norm_nonneg _))
  have hd := (div_lt_one (multiRadiusWeight_pos hρ d)).mpr hn
  convert hd using 1
  ring

/-- Division by a sufficiently close perturbation of a monomial, entirely
inside the weighted summable coefficient algebra. -/
theorem weightedSeriesDivision_existsUnique (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) (f g : WeightedSeries ρ hρ)
    (hsmall : weightedCoeffNorm ρ ((weightedSeriesMonomial ρ hρ d 1).val - f.val) <
      multiRadiusWeight ρ d) :
    ∃! q : WeightedSeries ρ hρ, weightedSeriesTailCLM ρ hρ d (g - f * q) = 0 :=
  banachDivision_existsUnique (weightedSeriesTailCLM ρ hρ d) (weightedSeriesMonomial ρ hρ d 1) f
    (weightedSeriesTailCLM_monomial_mul ρ hρ d)
    (weightedSeriesDivision_contraction ρ hρ d f hsmall) g

/-- Coordinate division with the precise coefficient condition on its actual
remainder. For `n = 0` this is division by a small perturbation of one. -/
theorem weightedSeries_coordinate_division_existsUnique (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (i : σ) (n : ℕ) (f g : WeightedSeries ρ hρ)
    (hsmall : weightedCoeffNorm ρ (MvPowerSeries.X i ^ n - f.val) < ρ i ^ n) :
    ∃! q : WeightedSeries ρ hρ,
      ∀ k : σ →₀ ℕ, n ≤ k i → MvPowerSeries.coeff k (g.val - f.val * q.val) = 0 := by
  have hs : weightedCoeffNorm ρ
      ((weightedSeriesMonomial ρ hρ (Finsupp.single i n) 1).val - f.val) <
        multiRadiusWeight ρ (Finsupp.single i n) := by
    simpa only [MvPowerSeries.X_pow_eq, multiRadiusWeight_single, weightedSeriesMonomial] using hsmall
  obtain ⟨q, hq, huniq⟩ := weightedSeriesDivision_existsUnique ρ hρ (Finsupp.single i n) f g hs
  refine ⟨q, (weightedSeriesTailCLM_coordinate_eq_zero_iff ρ hρ i n _).mp hq, ?_⟩
  intro q' hq'
  exact huniq q' ((weightedSeriesTailCLM_coordinate_eq_zero_iff ρ hρ i n _).mpr hq')

end AbelFormalization
