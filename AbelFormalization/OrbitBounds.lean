import AbelFormalization.Orbit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

/-!
# Uniform bounds transported along exponential orbits

A contraction on every exponential step, together with a compact fundamental
interval, gives decay on the entire positive tail. This packages the argument
needed for the finite collection of higher derivatives in the manuscript.
-/

namespace AbelFormalization.IsAbel

open Set Filter Function
open scoped Topology

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

omit hA in
theorem orbit_contraction_iterate {g : ℝ → ℝ} {q U u : ℝ}
    (hU : 0 < U) (hq : 0 ≤ q) (hu : U ≤ u)
    (hstep : ∀ x : ℝ, U ≤ x → g (E x) ≤ q * g x) (n : ℕ) :
    g (E^[n] u) ≤ q ^ n * g u := by
  have hup := hU.trans_le hu
  induction n with
  | zero => simp
  | succ n ih =>
      have hui : u ≤ E^[n] u := by
        simpa using (E_iterate_strictMono hup).monotone (Nat.zero_le n)
      rw [Function.iterate_succ_apply']
      calc
        g (E (E^[n] u)) ≤ q * g (E^[n] u) := hstep _ (hu.trans hui)
        _ ≤ q * (q ^ n * g u) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * g u := by rw [pow_succ]; ring

theorem orbit_contraction_bound {g : ℝ → ℝ} {q U : ℝ}
    (hU : 0 < U) (hq : 0 ≤ q)
    (hc : ContinuousOn g (Icc U (E U)))
    (hstep : ∀ x : ℝ, U ≤ x → g (E x) ≤ q * g x) :
    ∃ M : ℝ, ∀ x : ℝ, U ≤ x → g x ≤ q ^ orbitIndex A U x * M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨M, fun x hx => ?_⟩
  have hu := hA.orbitBase_mem hU hx
  have hb : g (orbitBase A U x) ≤ M :=
    hM ⟨orbitBase A U x, ⟨hu.1, hu.2.le⟩, rfl⟩
  have hi := orbit_contraction_iterate hU hq hu.1 hstep (orbitIndex A U x)
  rw [hA.iterate_orbitBase (hU.trans_le hx)] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hb (pow_nonneg hq _))

/-- Decay on the whole tail from geometric contraction on exponential steps. -/
theorem tendsto_zero_of_orbit_contraction {g : ℝ → ℝ} {q U : ℝ}
    (hU : 0 < U) (hq : 0 ≤ q) (hq1 : q < 1)
    (hc : ContinuousOn g (Icc U (E U)))
    (hpos : ∀ x : ℝ, U ≤ x → 0 ≤ g x)
    (hstep : ∀ x : ℝ, U ≤ x → g (E x) ≤ q * g x) :
    Tendsto g atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hA.orbit_contraction_bound hU hq hc hstep
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have hlim : Tendsto (fun x : ℝ => q ^ orbitIndex A U x * M) atTop (𝓝 0) := by
    simpa using (hpow.comp (hA.orbitIndex_tendsto_atTop U)).mul_const M
  apply squeeze_zero' ?_ ?_ hlim
  · exact (eventually_ge_atTop U).mono fun x hx => hpos x hx
  · exact (eventually_ge_atTop U).mono fun x hx => hM x hx

end AbelFormalization.IsAbel
