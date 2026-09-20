import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

/-!
# Analytic Abel functions for `exp x - 1`

This file states the paper's assumptions on the positive real axis and proves
their elementary consequences. A Lean function is total; its values outside the
positive real axis are immaterial to `IsAbel`.
-/

open Set Filter Function
open scoped Topology

namespace AbelFormalization

noncomputable section

/-- The self-map of the positive real axis used in the Abel equation. -/
def E (x : ℝ) : ℝ := Real.exp x - 1

/-- Exactly the analyticity, derivative, normalization and Abel-equation
assumptions in equation (1) of the paper. -/
structure IsAbel (A : ℝ → ℝ) : Prop where
  analytic : AnalyticOnNhd ℝ A (Ioi 0)
  deriv_pos : ∀ x > 0, 0 < deriv A x
  normalized : A 1 = 0
  abel : ∀ x > 0, A (E x) = A x + 1

theorem E_pos {x : ℝ} (hx : 0 < x) : 0 < E x := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)

theorem lt_E {x : ℝ} (hx : 0 < x) : x < E x := by
  have h := Real.add_one_lt_exp (ne_of_gt hx)
  dsimp [E]
  linarith

theorem E_strictMono : StrictMono E := by
  intro x y hxy
  exact sub_lt_sub_right (Real.exp_strictMono hxy) 1

theorem E_continuous : Continuous E := Real.continuous_exp.sub continuous_const

theorem E_iterate_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < E^[n] x := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using E_pos ih

theorem E_iterate_strictMono {x : ℝ} (hx : 0 < x) :
    StrictMono (fun n : ℕ => E^[n] x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simpa only [Function.iterate_succ_apply'] using lt_E (E_iterate_pos hx n)

theorem E_iterate_tendsto_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => E^[n] x) atTop atTop := by
  have hm := (E_iterate_strictMono hx).monotone
  rcases tendsto_atTop_of_monotone hm with h | ⟨l, hl⟩
  · exact h
  · have hxl : x ≤ l := by
      apply ge_of_tendsto hl
      exact Filter.Eventually.of_forall (fun n => by simpa using hm (Nat.zero_le n))
    have hfix := isFixedPt_of_tendsto_iterate hl E_continuous.continuousAt
    have hlt := lt_E (lt_of_lt_of_le hx hxl)
    exact False.elim ((ne_of_gt hlt) hfix)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem continuousOn : ContinuousOn A (Ioi 0) := hA.analytic.continuousOn

theorem strictMonoOn : StrictMonoOn A (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hA.continuousOn
  intro x hx
  exact hA.deriv_pos x (interior_subset hx)

theorem injectiveOn : Set.InjOn A (Ioi 0) := hA.strictMonoOn.injOn

theorem abel_iterate {x : ℝ} (hx : 0 < x) (n : ℕ) :
    A (E^[n] x) = A x + (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', hA.abel _ (E_iterate_pos hx n), ih]
      simp only [Nat.cast_succ]
      linarith

theorem abel_iterate_one (n : ℕ) : A (E^[n] 1) = (n : ℝ) := by
  simpa [hA.normalized] using hA.abel_iterate (show (0 : ℝ) < 1 from zero_lt_one) n

theorem nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ A x := by
  have hp : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  simpa [hA.normalized] using
    hA.strictMonoOn.monotoneOn (show (0 : ℝ) < 1 from zero_lt_one) hp hx

theorem pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < A x := by
  have hp : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simpa [hA.normalized] using
    hA.strictMonoOn (show (0 : ℝ) < 1 from zero_lt_one) hp hx

theorem exists_pos_value_gt (b : ℝ) : ∃ x > 0, b < A x := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  refine ⟨E^[n] 1, E_iterate_pos zero_lt_one n, ?_⟩
  simpa only [hA.abel_iterate_one] using hn

theorem tendsto_atTop : Tendsto A atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨x, hx, hb⟩ := hA.exists_pos_value_gt b
  exact (eventually_ge_atTop x).mono fun y hy =>
    hb.le.trans (hA.strictMonoOn.monotoneOn hx (hx.trans_le hy) hy)

end IsAbel
end
end AbelFormalization
