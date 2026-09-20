import AbelFormalization.ComplexLog
import Mathlib.Analysis.Complex.Exponential

/-!
# Quantitative bounds for logarithmic orbits

Elementary rational bounds for `log (1 + x)` give a uniform reciprocal
decay estimate for its real iterates.  The lower bound also makes the disks
of relative radius `1 / 2` invariant under the principal complex logarithm.
-/

noncomputable section

namespace AbelFormalization

open Set Function

/-- A convenient global lower bound for `log (1 + x)`. -/
theorem two_mul_div_le_L {x : ℝ} (hx : 0 ≤ x) :
    2 * x / (2 + x) ≤ L x := by
  simpa only [L, add_comm] using Real.le_log_one_add_of_nonneg hx

/-- On `[0, 1]`, `log (1 + x)` lies below a rational function whose
reciprocal increases by exactly `1 / 4`. -/
theorem L_le_div_one_add_quarter {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    L x ≤ x / (1 + x / 4) := by
  have hden : 0 < 1 + x / 4 := by positivity
  have ht : 0 ≤ x / (1 + x / 4) := div_nonneg hx hden.le
  rw [L, Real.log_le_iff_le_exp (by linarith : 0 < 1 + x)]
  calc
    1 + x ≤ ∑ m ∈ Finset.range 3,
        (x / (1 + x / 4)) ^ m / m.factorial := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
        Nat.factorial_one, Nat.factorial_two, Nat.cast_ofNat]
      field_simp [ne_of_gt hden]
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 4 - x)]
    _ ≤ Real.exp (x / (1 + x / 4)) := Real.sum_le_exp_of_nonneg ht 3

theorem L_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : L x ≤ x := by
  simpa only [L, add_sub_cancel_left] using
    Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)

theorem L_iterate_le_self {x : ℝ} (hx : 0 < x) (n : ℕ) :
    L^[n] x ≤ x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply']
      exact (L_le_self_of_nonneg (L_iterate_pos hx n).le).trans ih

private theorem div_one_add_quarter_mono {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (1 + a / 4) ≤ b / (1 + b / 4) := by
  have hb : 0 ≤ b := ha.trans hab
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + a / 4)
    (by positivity : 0 < 1 + b / 4)).2
  nlinarith

/-- A reciprocal upper bound for every logarithmic iterate starting in
`(0, 1]`. -/
theorem L_iterate_le_inv_add_quarter {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) :
    L^[n] x ≤ (1 / x + (n : ℝ) / 4)⁻¹ := by
  induction n with
  | zero =>
      simp only [iterate_zero, id_eq, Nat.cast_zero, zero_div, add_zero]
      field_simp
      norm_num
  | succ n ih =>
      let q : ℝ := 1 / x + (n : ℝ) / 4
      have hq : 0 < q := by
        dsimp [q]
        positivity
      have hy : 0 ≤ L^[n] x := (L_iterate_pos hx n).le
      have hy1 : L^[n] x ≤ 1 := (L_iterate_le_self hx n).trans hx1
      rw [iterate_succ_apply']
      calc
        L (L^[n] x) ≤ L^[n] x / (1 + L^[n] x / 4) :=
          L_le_div_one_add_quarter hy hy1
        _ ≤ q⁻¹ / (1 + q⁻¹ / 4) :=
          div_one_add_quarter_mono hy (by simpa only [q] using ih)
        _ = (q + 1 / 4)⁻¹ := by
          field_simp [ne_of_gt hq]
        _ = (1 / x + ((n + 1 : ℕ) : ℝ) / 4)⁻¹ := by
          congr 1
          dsimp [q]
          push_cast
          ring

/-- A simpler consequence of `L_iterate_le_inv_add_quarter`, convenient for
summability estimates. -/
theorem L_iterate_le_four_div {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) :
    L^[n] x ≤ 4 / ((n : ℝ) + 1) := by
  refine (L_iterate_le_inv_add_quarter hx hx1 n).trans ?_
  have hinvx : 1 ≤ 1 / x := by
    apply (le_div_iff₀ hx).2
    simpa using hx1
  have hq : 0 < 1 / x + (n : ℝ) / 4 := by positivity
  have hn : 0 < ((n : ℝ) + 1) / 4 := by positivity
  have hden : ((n : ℝ) + 1) / 4 ≤ 1 / x + (n : ℝ) / 4 := by
    linarith
  have hi := (inv_le_inv₀ hq hn).2 hden
  calc
    (1 / x + (n : ℝ) / 4)⁻¹ ≤ (((n : ℝ) + 1) / 4)⁻¹ := hi
    _ = 4 / ((n : ℝ) + 1) := by
      field_simp

/-- One logarithm maps the disk of radius half its positive center into
the corresponding half-radius disk at the next real center. -/
theorem complexL_mapsTo_half_ball {x : ℝ} (hx : 0 < x) :
    MapsTo complexL (Metric.ball (x : ℂ) (x / 2))
      (Metric.ball (L x : ℂ) (L x / 2)) := by
  have hm := complexL_mapsTo_ball (c := x) (r := x / 2)
    (by positivity) (by linarith)
  rw [complexL_ofReal (by linarith : 0 ≤ 1 + x)] at hm
  apply hm.mono_right
  apply Metric.ball_subset_ball
  have hl := two_mul_div_le_L hx.le
  have hradius : (x / 2) / (1 + x - x / 2) = x / (2 + x) := by
    rw [div_div]
    congr 1
    ring
  rw [hradius]
  calc
    x / (2 + x) = (2 * x / (2 + x)) / 2 := by ring
    _ ≤ L x / 2 := div_le_div_of_nonneg_right hl (by norm_num)

/-- Every complex logarithmic iterate preserves the relative half-radius
disk along a positive real logarithmic orbit. -/
theorem complexL_iterate_mapsTo_half_ball {x : ℝ} (hx : 0 < x) (n : ℕ) :
    MapsTo (complexL^[n]) (Metric.ball (x : ℂ) (x / 2))
      (Metric.ball (L^[n] x : ℂ) (L^[n] x / 2)) := by
  induction n generalizing x with
  | zero => exact mapsTo_id _
  | succ n ih =>
      have hm := complexL_mapsTo_half_ball hx
      have hi := ih (L_pos hx)
      simpa only [iterate_succ, Function.comp_apply] using hi.comp hm

/-- The complex logarithmic iterate is analytic on every relative
half-radius disk along a positive real orbit. -/
theorem complexL_iterate_analyticOnNhd_half_ball {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    AnalyticOnNhd ℂ (complexL^[n]) (Metric.ball (x : ℂ) (x / 2)) := by
  induction n generalizing x with
  | zero => exact analyticOnNhd_id
  | succ n ih =>
      have hm := complexL_mapsTo_half_ball hx
      have ha := complexL_analyticOnNhd_ball (c := x) (r := x / 2) (by linarith)
      have hi := ih (L_pos hx)
      simpa only [iterate_succ] using hi.comp ha hm

/-- Combined analytic and mapping form used by the local density
construction. -/
theorem complexL_iterate_half_disk {x : ℝ} (hx : 0 < x) (n : ℕ) :
    AnalyticOnNhd ℂ (complexL^[n]) (Metric.ball (x : ℂ) (x / 2)) ∧
      MapsTo (complexL^[n]) (Metric.ball (x : ℂ) (x / 2))
        (Metric.ball (L^[n] x : ℂ) (L^[n] x / 2)) :=
  ⟨complexL_iterate_analyticOnNhd_half_ball hx n,
    complexL_iterate_mapsTo_half_ball hx n⟩

end AbelFormalization
