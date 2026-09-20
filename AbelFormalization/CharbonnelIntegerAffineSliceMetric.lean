import AbelFormalization.CharbonnelCompactIntersectionThickening
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Metric control of an integer-affine hyperplane slice

For a nonzero integer coefficient row, correcting one coordinate sends a
point exactly to the hyperplane at distance at most the absolute value of
its affine linear form. Thus a sufficiently small squared-level band is
inside any prescribed metric thickening of the hyperplane. A zero row is
classified separately as either the whole space or the empty set.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- Every nonzero integer, viewed in the reals, has absolute value at
least one. -/
theorem one_le_abs_real_of_int_ne_zero (z : ℤ) (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hInt : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have hReal : (1 : ℝ) ≤ (|z| : ℝ) := by exact_mod_cast hInt
  simpa only [Int.cast_abs] using hReal

/-- The nonzero integer row has real product-space norm at least one. -/
theorem integerAffineSliceCoefficientNorm_one_le
    {n : ℕ} (coeff : Fin n → ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0) :
    (1 : ℝ) ≤ ‖(fun j : Fin n ↦ (coeff j : ℝ))‖ := by
  obtain ⟨j, hj⟩ := hnonzero
  have hcoordinate :
      (1 : ℝ) ≤ ‖(coeff j : ℝ)‖ := by
    simpa only [Real.norm_eq_abs] using
      one_le_abs_real_of_int_ne_zero (coeff j) hj
  exact hcoordinate.trans
    (norm_le_pi_norm (fun k : Fin n ↦ (coeff k : ℝ)) j)

/-- Every integer-affine displayed hyperplane is closed, including the
whole-space and empty degenerate carriers. -/
theorem isClosed_integerAffineSliceHyperplane
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) :
    IsClosed (integerAffineSliceHyperplane coeff constant) := by
  have hcontinuous :
      Continuous (integerAffineSliceLinearForm coeff constant) := by
    unfold integerAffineSliceLinearForm
    fun_prop
  change IsClosed
    ((integerAffineSliceLinearForm coeff constant) ⁻¹' ({0} : Set ℝ))
  exact isClosed_singleton.preimage hcontinuous

/-- If every linear coefficient vanishes, the affine form is constant. -/
theorem integerAffineSliceLinearForm_eq_constant_of_coeff_zero
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (x : RealEuclidean n) :
    integerAffineSliceLinearForm coeff constant x =
      (constant : ℝ) := by
  simp [integerAffineSliceLinearForm, hzero]

theorem integerAffineSliceHyperplane_eq_univ_of_coeff_zero
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (hconstant : constant = 0) :
    integerAffineSliceHyperplane coeff constant = Set.univ := by
  ext x
  change integerAffineSliceLinearForm coeff constant x = 0 ↔ True
  rw [integerAffineSliceLinearForm_eq_constant_of_coeff_zero
    coeff constant hzero x]
  simp [hconstant]

theorem integerAffineSliceHyperplane_eq_empty_of_coeff_zero
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (hconstant : constant ≠ 0) :
    integerAffineSliceHyperplane coeff constant = ∅ := by
  have hconstantReal : (constant : ℝ) ≠ 0 := by exact_mod_cast hconstant
  ext x
  simp [integerAffineSliceHyperplane,
    integerAffineSliceLinearForm_eq_constant_of_coeff_zero
      coeff constant hzero x, hconstantReal]

/-- In the zero-row, zero-constant case the hyperplane is all of space,
so metric proximity is automatic. -/
theorem integerAffineSlice_mem_thickening_of_coeff_zero_constant_zero
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (hconstant : constant = 0)
    {delta : ℝ} (hdelta : 0 < delta) (x : RealEuclidean n) :
    x ∈ Metric.thickening delta
      (integerAffineSliceHyperplane coeff constant) := by
  apply Metric.mem_thickening_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · rw [integerAffineSliceHyperplane_eq_univ_of_coeff_zero
      coeff constant hzero hconstant]
    exact Set.mem_univ x
  · simpa only [dist_self] using hdelta

/-- For an empty zero-row carrier, no point can satisfy a sufficiently
small squared-level bound. -/
theorem no_small_integerAffineSliceLevel_of_coeff_zero_constant_ne
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (hconstant : constant ≠ 0)
    {epsilon : ℝ} (hepsilon : epsilon < 1)
    (x : RealEuclidean n) :
    ¬ (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ epsilon := by
  have hconstantAbs : (1 : ℝ) ≤ |(constant : ℝ)| :=
    one_le_abs_real_of_int_ne_zero constant hconstant
  have hconstantSq : (1 : ℝ) ≤ (constant : ℝ) ^ 2 :=
    (one_le_sq_iff_one_le_abs (constant : ℝ)).mpr hconstantAbs
  rw [integerAffineSliceLinearForm_eq_constant_of_coeff_zero
    coeff constant hzero x]
  linarith

/-- The coordinate correction used for a nonzero affine row. -/
def integerAffineSliceCorrectAt
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (j : Fin n) (x : RealEuclidean n) : RealEuclidean n :=
  fun i ↦ if i = j then
    x i - integerAffineSliceLinearForm coeff constant x /
      (coeff j : ℝ)
  else x i

/-- Correcting a coordinate with nonzero coefficient solves the affine
equation exactly. -/
theorem integerAffineSliceCorrectAt_mem
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (j : Fin n) (hj : coeff j ≠ 0) (x : RealEuclidean n) :
    integerAffineSliceCorrectAt coeff constant j x ∈
      integerAffineSliceHyperplane coeff constant := by
  let t := integerAffineSliceLinearForm coeff constant x /
    (coeff j : ℝ)
  have hjReal : (coeff j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hsum :
      (∑ i : Fin n,
        (coeff i : ℝ) * integerAffineSliceCorrectAt coeff constant j x i) =
        (∑ i : Fin n, (coeff i : ℝ) * x i) -
          (coeff j : ℝ) * t := by
    calc
      _ = ∑ i : Fin n,
          ((coeff i : ℝ) * x i -
            (if i = j then (coeff j : ℝ) * t else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hij : i = j
            · subst i
              simp [integerAffineSliceCorrectAt, t, mul_sub]
            · simp [integerAffineSliceCorrectAt, hij]
      _ = (∑ i : Fin n, (coeff i : ℝ) * x i) -
          ∑ i : Fin n, (if i = j then (coeff j : ℝ) * t else 0) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin n, (coeff i : ℝ) * x i) -
          (coeff j : ℝ) * t := by
            simp [Fintype.sum_ite_eq]
  have hcancel : (coeff j : ℝ) * t =
      integerAffineSliceLinearForm coeff constant x := by
    dsimp only [t]
    exact mul_div_cancel₀ _ hjReal
  change integerAffineSliceLinearForm coeff constant
      (integerAffineSliceCorrectAt coeff constant j x) = 0
  change (∑ i : Fin n,
      (coeff i : ℝ) * integerAffineSliceCorrectAt coeff constant j x i) +
        (constant : ℝ) = 0
  rw [hsum, hcancel]
  change (∑ i : Fin n, (coeff i : ℝ) * x i) -
      ((∑ i : Fin n, (coeff i : ℝ) * x i) + (constant : ℝ)) +
        (constant : ℝ) = 0
  ring

/-- The correction distance is at most the magnitude of the original
affine form; the integer coefficient lower bound is used here. -/
theorem dist_integerAffineSliceCorrectAt_le_abs
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (j : Fin n) (hj : coeff j ≠ 0) (x : RealEuclidean n) :
    dist x (integerAffineSliceCorrectAt coeff constant j x) ≤
      |integerAffineSliceLinearForm coeff constant x| := by
  let t := integerAffineSliceLinearForm coeff constant x /
    (coeff j : ℝ)
  have hjReal : (coeff j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hcoeffAbs : (1 : ℝ) ≤ |(coeff j : ℝ)| :=
    one_le_abs_real_of_int_ne_zero (coeff j) hj
  have hcoeffPos : 0 < |(coeff j : ℝ)| := abs_pos.mpr hjReal
  have htBound : |t| ≤
      |integerAffineSliceLinearForm coeff constant x| := by
    dsimp only [t]
    rw [abs_div]
    apply (div_le_iff₀ hcoeffPos).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hcoeffAbs
        (abs_nonneg (integerAffineSliceLinearForm coeff constant x))
  have hdist :
      dist x (integerAffineSliceCorrectAt coeff constant j x) ≤
        |t| := by
    apply (dist_pi_le_iff (abs_nonneg t)).mpr
    intro i
    by_cases hij : i = j
    · subst i
      simp [integerAffineSliceCorrectAt, t, Real.dist_eq, abs_div]
    · simp [integerAffineSliceCorrectAt, hij, abs_nonneg]
  exact hdist.trans htBound

/-- A nonzero integer row turns a small absolute affine value into
proximity to its actual hyperplane. -/
theorem integerAffineSlice_mem_thickening_of_abs_lt
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (x : RealEuclidean n)
    (hlevel : |integerAffineSliceLinearForm coeff constant x| < delta) :
    x ∈ Metric.thickening delta
      (integerAffineSliceHyperplane coeff constant) := by
  obtain ⟨j, hj⟩ := hnonzero
  apply Metric.mem_thickening_iff.mpr
  refine ⟨integerAffineSliceCorrectAt coeff constant j x,
    integerAffineSliceCorrectAt_mem coeff constant j hj x, ?_⟩
  exact lt_of_le_of_lt
    (dist_integerAffineSliceCorrectAt_le_abs coeff constant j hj x)
    hlevel

/-- A squared-level band below `delta²` lies in the `delta`-metric
thickening of the hyperplane. -/
theorem integerAffineSlice_mem_thickening_of_sq_le
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    {delta epsilon : ℝ} (hdelta : 0 < delta)
    (hepsilon : epsilon < delta ^ 2)
    (x : RealEuclidean n)
    (hlevel : (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤
      epsilon) :
    x ∈ Metric.thickening delta
      (integerAffineSliceHyperplane coeff constant) := by
  have habs : |integerAffineSliceLinearForm coeff constant x| < delta := by
    have hsq :
        |integerAffineSliceLinearForm coeff constant x| ^ 2 <
          delta ^ 2 := by
      simpa only [sq_abs] using lt_of_le_of_lt hlevel hepsilon
    nlinarith [abs_nonneg (integerAffineSliceLinearForm coeff constant x)]
  exact integerAffineSlice_mem_thickening_of_abs_lt
    coeff constant hnonzero hdelta x habs

/-- A positive small squared-level scale can be chosen for any positive
metric tolerance. -/
theorem exists_integerAffineSlice_sqLevel_thickening_scale
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ x : RealEuclidean n,
        (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ epsilon →
          x ∈ Metric.thickening delta
            (integerAffineSliceHyperplane coeff constant) := by
  refine ⟨delta ^ 2 / 2, by positivity, ?_⟩
  intro x hx
  apply integerAffineSlice_mem_thickening_of_sq_le
    coeff constant hnonzero hdelta (by nlinarith [sq_pos_of_pos hdelta])
    x hx

end AbelFormalization
