import AbelFormalization.DerivativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A logarithmic bound for the Abel function

The limit `x A'(x) → 0` gives an eventual derivative bound by `1/x`.
The mean value theorem then bounds `A - log` above on a tail.
-/

namespace AbelFormalization.IsAbel

open Set Filter Asymptotics
open scoped Topology

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem eventually_deriv_le_inv :
    ∀ᶠ x : ℝ in atTop, deriv A x ≤ x⁻¹ := by
  have he := hA.tendsto_mul_deriv_atTop.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hp
  have hm : deriv A x * x ≤ 1 := by nlinarith
  simpa only [one_div] using (le_div_iff₀ hp).mpr hm

theorem exists_log_upper_bound :
    ∃ R C : ℝ, 1 < R ∧ ∀ x : ℝ, R ≤ x → A x ≤ Real.log x + C := by
  obtain ⟨b, hb⟩ := eventually_atTop.1 hA.eventually_deriv_le_inv
  let R : ℝ := max b 2
  have hR : 1 < R := lt_of_lt_of_le (by norm_num) (le_max_right b 2)
  have hp : ∀ x ∈ Ici R, 0 < x := fun x hx =>
    lt_trans zero_lt_one (hR.trans_le hx)
  have hd : ∀ x ∈ Ici R,
      HasDerivAt (fun y => A y - Real.log y) (deriv A x - x⁻¹) x := by
    intro x hx
    exact (hA.differentiableAt (hp x hx)).hasDerivAt.sub
      (Real.hasDerivAt_log (ne_of_gt (hp x hx)))
  have hanti : AntitoneOn (fun x => A x - Real.log x) (Ici R) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici R)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hRx : R ≤ x := interior_subset hx
    exact sub_nonpos.mpr (hb x ((le_max_left b 2).trans hRx))
  refine ⟨R, A R - Real.log R, hR, ?_⟩
  intro x hx
  have h := hanti (show R ∈ Ici R from by simp) hx hx
  linarith

/-- The logarithmic estimate in the paper's analytic input. -/
theorem isBigO_log_atTop : A =O[atTop] Real.log := by
  obtain ⟨R, C, hR, hbound⟩ := hA.exists_log_upper_bound
  apply Asymptotics.IsBigO.of_bound (1 + |C|)
  have hl : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop R, hl] with x hx hlog
  have hApos := hA.nonneg_of_one_le (hR.le.trans hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hApos,
    abs_of_nonneg (by linarith : 0 ≤ Real.log x)]
  have hb := hbound x hx
  have hc := mul_nonneg (abs_nonneg C) (sub_nonneg.mpr hlog)
  nlinarith [le_abs_self C]

end AbelFormalization.IsAbel
