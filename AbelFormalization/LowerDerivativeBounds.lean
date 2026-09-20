import AbelFormalization.DerivativeBounds
import AbelFormalization.InverseRegularity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Lower bounds for the first derivative at infinity -/

noncomputable section

open Set Function Filter
open scoped Topology

namespace AbelFormalization

theorem tendsto_E_div_exp :
    Tendsto (fun u : ℝ => E u / Real.exp u) atTop (𝓝 1) := by
  have h : Tendsto (fun u : ℝ => 1 - (Real.exp u)⁻¹) atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub Real.tendsto_exp_atTop.inv_tendsto_atTop
  have he : (fun u : ℝ => E u / Real.exp u) =
      (fun u : ℝ => 1 - (Real.exp u)⁻¹) := by
    funext u
    dsimp [E]
    rw [sub_div, div_self (Real.exp_ne_zero _), one_div]
  rw [he]
  simpa using h

theorem tendsto_deriv_growth_ratio :
    Tendsto (fun u : ℝ => (E u) ^ (3 / 2 : ℝ) /
      (Real.exp u * u ^ (3 / 2 : ℝ))) atTop atTop := by
  have hb : Tendsto (fun u : ℝ => (E u / Real.exp u) ^ (3 / 2 : ℝ))
      atTop (𝓝 1) := by
    simpa using tendsto_E_div_exp.rpow_const (p := (3 / 2 : ℝ)) (Or.inl one_ne_zero)
  have hg := tendsto_exp_mul_div_rpow_atTop (3 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num)
  apply (hb.pos_mul_atTop (by norm_num) hg).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [Real.div_rpow (E_pos hu).le (Real.exp_pos _).le, ← Real.exp_mul]
  have he : Real.exp (u * (3 / 2 : ℝ)) =
      Real.exp u * Real.exp ((1 / 2 : ℝ) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem exists_scaled_deriv_expansion : ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ u →
    2 * (u ^ (3 / 2 : ℝ) * deriv A u) ≤
      (E u) ^ (3 / 2 : ℝ) * deriv A (E u) := by
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (tendsto_deriv_growth_ratio.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  have hup : 0 < u := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hu)
  have hr := hR u ((le_max_right _ _).trans hu)
  have hd := hA.deriv_pos (E u) (E_pos hup)
  have hden : 0 < Real.exp u * u ^ (3 / 2 : ℝ) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hup _)
  have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mp hr) hd.le
  calc
    2 * (u ^ (3 / 2 : ℝ) * deriv A u)
        = (2 * (Real.exp u * u ^ (3 / 2 : ℝ))) * deriv A (E u) := by
      rw [← hA.deriv_abel hup]
      ring
    _ ≤ (E u) ^ (3 / 2 : ℝ) * deriv A (E u) := hmul

omit hA in
theorem scaled_deriv_iterate_lower {U : ℝ} (hU : 0 < U)
    (hstep : ∀ u : ℝ, U ≤ u → 2 * (u ^ (3 / 2 : ℝ) * deriv A u) ≤
      (E u) ^ (3 / 2 : ℝ) * deriv A (E u))
    {u : ℝ} (hu : U ≤ u) (n : ℕ) :
    (2 : ℝ) ^ n * (u ^ (3 / 2 : ℝ) * deriv A u) ≤
      (E^[n] u) ^ (3 / 2 : ℝ) * deriv A (E^[n] u) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hi := (E_iterate_strictMono (hU.trans_le hu)).monotone (Nat.zero_le n)
      have hui : u ≤ E^[n] u := by simpa using hi
      rw [Function.iterate_succ_apply', pow_succ]
      calc
        (2 : ℝ) ^ n * 2 * (u ^ (3 / 2 : ℝ) * deriv A u)
            = 2 * ((2 : ℝ) ^ n * (u ^ (3 / 2 : ℝ) * deriv A u)) := by ring
        _ ≤ 2 * ((E^[n] u) ^ (3 / 2 : ℝ) * deriv A (E^[n] u)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ (E (E^[n] u)) ^ (3 / 2 : ℝ) * deriv A (E (E^[n] u)) :=
          hstep _ (hu.trans hui)

theorem exists_scaled_deriv_orbit_lower_bound : ∃ U c : ℝ, 0 < U ∧ 0 < c ∧
    ∀ x : ℝ, U ≤ x →
      (2 : ℝ) ^ orbitIndex A U x * c ≤ x ^ (3 / 2 : ℝ) * deriv A x := by
  obtain ⟨U, hU, hstep⟩ := hA.exists_scaled_deriv_expansion
  have hc : ContinuousOn (fun x : ℝ => x ^ (3 / 2 : ℝ) * deriv A x)
      (Icc U (E U)) := by
    apply (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousOn.mul
    apply hA.analytic.deriv.continuousOn.mono
    intro x hx
    exact hU.trans_le hx.1
  obtain ⟨v, hv, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (lt_E hU).le) hc
  have hvp : 0 < v := hU.trans_le hv.1
  refine ⟨U, v ^ (3 / 2 : ℝ) * deriv A v, hU,
    mul_pos (Real.rpow_pos_of_pos hvp _) (hA.deriv_pos v hvp), ?_⟩
  intro x hx
  have hu := hA.orbitBase_mem hU hx
  have hb := hmin ⟨hu.1, hu.2.le⟩
  have hi := scaled_deriv_iterate_lower hU hstep hu.1 (orbitIndex A U x)
  rw [hA.iterate_orbitBase (hU.trans_le hx)] at hi
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans hi

theorem tendsto_rpow_three_halves_mul_deriv_atTop :
    Tendsto (fun x : ℝ => x ^ (3 / 2 : ℝ) * deriv A x) atTop atTop := by
  obtain ⟨U, c, hU, hc, hbound⟩ := hA.exists_scaled_deriv_orbit_lower_bound
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim := (hp.comp (hA.orbitIndex_tendsto_atTop U)).atTop_mul_const hc
  exact tendsto_atTop_mono' _ ((eventually_ge_atTop U).mono fun x hx => hbound x hx) hlim

/-- The inverse-square lower bound used when clearing derivative denominators. -/
theorem eventually_deriv_ge_rpow_neg_two :
    ∀ᶠ x : ℝ in atTop, x ^ (-2 : ℝ) ≤ deriv A x := by
  have he : ∀ᶠ x : ℝ in atTop, 1 ≤ x ^ (3 / 2 : ℝ) * deriv A x :=
    hA.tendsto_rpow_three_halves_mul_deriv_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hp : x ^ (3 / 2 : ℝ) ≤ x ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hp (hA.deriv_pos x hxp).le
  have hprod : 1 ≤ x ^ (2 : ℝ) * deriv A x := hx.trans hm
  have hb : 1 / x ^ (2 : ℝ) ≤ deriv A x :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hxp _)).mpr (by simpa [mul_comm] using hprod)
  rw [Real.rpow_neg hxp.le]
  simpa only [one_div] using hb

/-- The upper inverse-derivative estimate stated in the paper. -/
theorem eventually_inverse_deriv_le_rpow_three_halves :
    ∀ᶠ s : ℝ in atTop, deriv (inverse A) s ≤ (inverse A s) ^ (3 / 2 : ℝ) := by
  have hlim := hA.tendsto_rpow_three_halves_mul_deriv_atTop.comp hA.inverse_tendsto_atTop
  have he : ∀ᶠ s : ℝ in atTop,
      1 ≤ (inverse A s) ^ (3 / 2 : ℝ) * deriv A (inverse A s) :=
    hlim.eventually (eventually_ge_atTop 1)
  filter_upwards [he] with s hs
  rw [hA.inverse_deriv]
  simpa only [one_div] using
    (div_le_iff₀ (hA.deriv_pos _ (hA.inverse_pos s))).mpr hs

end IsAbel
end AbelFormalization
