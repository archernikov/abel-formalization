import AbelFormalization.Analytic
import AbelFormalization.Orbit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

/-!
# The first derivative estimate at infinity

This proves the first limit in the paper's analytic estimates:
`x * A'(x) → 0`. The proof contracts this quantity by a factor of at least
two at each exponential step, starting on a compact fundamental interval.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace AbelFormalization.IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem scaled_deriv_step {u : ℝ} (hu : 2 ≤ u) :
    E u * deriv A (E u) ≤ (1 / 2 : ℝ) * (u * deriv A u) := by
  have hup : 0 < u := by linarith
  have hp := hA.deriv_pos (E u) (E_pos hup)
  have hd := hA.deriv_pos u hup
  have hr := hA.deriv_abel hup
  have hfirst : E u * deriv A (E u) ≤ deriv A u := by
    change (Real.exp u - 1) * deriv A (E u) ≤ deriv A u
    nlinarith
  have hprod : 2 * deriv A u ≤ u * deriv A u :=
    mul_le_mul_of_nonneg_right hu hd.le
  linarith

theorem scaled_deriv_iterate {u : ℝ} (hu : 2 ≤ u) (n : ℕ) :
    E^[n] u * deriv A (E^[n] u) ≤
      (1 / 2 : ℝ) ^ n * (u * deriv A u) := by
  have hup : 0 < u := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
      have hge : 2 ≤ E^[n] u := by
        have hi := (E_iterate_strictMono hup).monotone (Nat.zero_le n)
        have hui : u ≤ E^[n] u := by simpa using hi
        exact hu.trans hui
      rw [Function.iterate_succ_apply']
      calc
        E (E^[n] u) * deriv A (E (E^[n] u))
            ≤ (1 / 2 : ℝ) * (E^[n] u * deriv A (E^[n] u)) :=
          hA.scaled_deriv_step hge
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * (u * deriv A u)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) * (u * deriv A u) := by
          rw [pow_succ]
          ring

theorem scaled_deriv_orbit_bound : ∃ M : ℝ, ∀ x : ℝ, 2 ≤ x →
    x * deriv A x ≤ (1 / 2 : ℝ) ^ orbitIndex A 2 x * M := by
  have hc : ContinuousOn (fun x : ℝ => x * deriv A x) (Icc 2 (E 2)) := by
    apply continuousOn_id.mul
    apply hA.analytic.deriv.continuousOn.mono
    intro x hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx.1
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨M, fun x hx => ?_⟩
  have hu := hA.orbitBase_mem (by norm_num : (0 : ℝ) < 2) hx
  have hb : orbitBase A 2 x * deriv A (orbitBase A 2 x) ≤ M :=
    hM ⟨orbitBase A 2 x, ⟨hu.1, hu.2.le⟩, rfl⟩
  have hi := hA.scaled_deriv_iterate hu.1 (orbitIndex A 2 x)
  rw [hA.iterate_orbitBase (by linarith : 0 < x)] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hb (by positivity))

theorem tendsto_mul_deriv_atTop :
    Tendsto (fun x : ℝ => x * deriv A x) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hA.scaled_deriv_orbit_bound
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun x : ℝ => (1 / 2 : ℝ) ^ orbitIndex A 2 x * M)
      atTop (𝓝 0) := by
    simpa using (hp.comp (hA.orbitIndex_tendsto_atTop 2)).mul_const M
  apply squeeze_zero' ?_ ?_ hlim
  · exact (eventually_ge_atTop (2 : ℝ)).mono fun x hx =>
      mul_nonneg (by linarith) (hA.deriv_pos x (by linarith)).le
  · exact (eventually_ge_atTop (2 : ℝ)).mono fun x hx => hM x hx

end AbelFormalization.IsAbel
