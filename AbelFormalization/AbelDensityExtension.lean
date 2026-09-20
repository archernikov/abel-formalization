import AbelFormalization.ComplexLogIterates
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Extending an invariant Abel density from the origin

The inverse iterates of `exp x - 1` enter every positive neighbourhood of zero.
This permits the analytic invariant density used in the existence construction
to be extended from a small positive interval to the whole positive half-line.
-/

noncomputable section

namespace AbelFormalization

open Set Filter Function
open scoped Topology

theorem E_iterate_L_iterate {x : ℝ} (hx : 0 < x) (n : ℕ) :
    E^[n] (L^[n] x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply' L, Function.iterate_succ_apply E,
        E_L (L_iterate_pos hx n), ih]

theorem L_iterate_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => L^[n] x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans (L_iterate_pos hx n)
  · intro b hb
    filter_upwards [(E_iterate_tendsto_atTop hb).eventually (eventually_gt_atTop x)]
      with n hn
    by_contra h
    have hm := (E_strictMono.iterate n).monotone (le_of_not_gt h)
    rw [E_iterate_L_iterate hx] at hm
    exact (not_le_of_gt hn) hm

theorem exists_L_iterate_lt {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    ∃ n : ℕ, L^[n] x < ε :=
  ((L_iterate_tendsto_zero hx).eventually (gt_mem_nhds hε)).exists

theorem L_lt_self {x : ℝ} (hx : 0 < x) : L x < x := by
  have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + x)
    (by linarith : 1 + x ≠ 1)
  simpa [L] using h

theorem L_iterate_antitone {x : ℝ} (hx : 0 < x) :
    Antitone (fun n : ℕ => L^[n] x) := by
  apply antitone_nat_of_succ_le
  intro n
  simpa only [Function.iterate_succ_apply'] using (L_lt_self (L_iterate_pos hx n)).le

theorem analyticAt_L {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ L x := by
  exact (analyticAt_log (by linarith : 0 < 1 + x)).comp
    (analyticAt_const.add analyticAt_id)

theorem analyticAt_L_iterate {x : ℝ} (hx : 0 < x) (n : ℕ) :
    AnalyticAt ℝ L^[n] x := by
  induction n with
  | zero => exact analyticAt_id
  | succ n ih =>
      simpa only [Function.iterate_succ'] using
        (analyticAt_L (L_iterate_pos hx n)).comp ih

/-- The positive Jacobian of the `n`-th logarithmic iterate. -/
def logIterateWeight (n : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + L^[k] x)⁻¹

theorem logIterateWeight_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 < logIterateWeight n x := by
  apply Finset.prod_pos
  intro k _
  exact inv_pos.mpr (by have := L_iterate_pos hx k; linarith)

theorem logIterateWeight_succ (n : ℕ) (x : ℝ) :
    logIterateWeight (n + 1) x = logIterateWeight n x * (1 + L^[n] x)⁻¹ := by
  exact Finset.prod_range_succ _ _

theorem logIterateWeight_succ' (n : ℕ) (x : ℝ) :
    logIterateWeight (n + 1) x = logIterateWeight n (L x) * (1 + x)⁻¹ := by
  simp only [logIterateWeight, Finset.prod_range_succ',
    Function.iterate_succ_apply, Function.iterate_zero, id_eq]

theorem analyticAt_logIterateWeight {x : ℝ} (hx : 0 < x) (n : ℕ) :
    AnalyticAt ℝ (logIterateWeight n) x := by
  apply Finset.analyticAt_fun_prod
  intro k _
  exact (analyticAt_const.add (analyticAt_L_iterate hx k)).inv
    (by change 1 + L^[k] x ≠ 0; have := L_iterate_pos hx k; linarith)

/-- Pulling back a density by a finite logarithmic iterate. -/
def pullbackLogDensity (b : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  b (L^[n] x) * logIterateWeight n x

theorem pullbackLogDensity_succ' (b : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    pullbackLogDensity b (n + 1) x = pullbackLogDensity b n (L x) / (1 + x) := by
  simp only [pullbackLogDensity, Function.iterate_succ_apply, logIterateWeight_succ',
    div_eq_mul_inv, mul_assoc]

theorem pullbackLogDensity_stable {b : ℝ → ℝ} {ε x : ℝ} (hx : 0 < x)
    (hinv : ∀ y ∈ Ioo 0 ε, b (L y) / (1 + y) = b y)
    {n m : ℕ} (hn : L^[n] x < ε) (hnm : n ≤ m) :
    pullbackLogDensity b m x = pullbackLogDensity b n x := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      have hm : L^[m] x ∈ Ioo 0 ε :=
        ⟨L_iterate_pos hx m, (L_iterate_antitone hx hnm).trans_lt hn⟩
      rw [pullbackLogDensity, Function.iterate_succ_apply', logIterateWeight_succ]
      calc
        b (L (L^[m] x)) * (logIterateWeight m x * (1 + L^[m] x)⁻¹) =
            (b (L (L^[m] x)) / (1 + L^[m] x)) * logIterateWeight m x := by ring
        _ = pullbackLogDensity b m x := by rw [hinv _ hm]; rfl
        _ = _ := ih

/-- A density germ invariant under `log (1+x)` extends analytically to all positive reals. -/
theorem exists_global_density_of_local {ε : ℝ} (hε : 0 < ε) {b : ℝ → ℝ}
    (hb : AnalyticOnNhd ℝ b (Ioo 0 ε))
    (hbpos : ∀ x ∈ Ioo 0 ε, 0 < b x)
    (hinv : ∀ x ∈ Ioo 0 ε, b (L x) / (1 + x) = b x) :
    ∃ B : ℝ → ℝ, AnalyticOnNhd ℝ B (Ioi 0) ∧
      (∀ x > 0, 0 < B x) ∧ (∀ x > 0, B (E x) * Real.exp x = B x) := by
  classical
  let N (x : ℝ) (hx : 0 < x) := Nat.find (exists_L_iterate_lt hx hε)
  have hN (x : ℝ) (hx : 0 < x) : L^[N x hx] x < ε :=
    Nat.find_spec (exists_L_iterate_lt hx hε)
  let B (x : ℝ) := if hx : 0 < x then pullbackLogDensity b (N x hx) x else 0
  have hB (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : L^[n] x < ε) :
      B x = pullbackLogDensity b n x := by
    dsimp only [B]
    rw [dite_eq_left hx]
    exact (pullbackLogDensity_stable hx hinv (hN x hx) (le_max_left _ _)).symm.trans
      (pullbackLogDensity_stable hx hinv hn (le_max_right _ _))
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    let n := N x hx
    have hn := hN x hx
    have ha : AnalyticAt ℝ (pullbackLogDensity b n) x :=
      ((hb _ ⟨L_iterate_pos hx n, hn⟩).comp (analyticAt_L_iterate hx n)).mul
        (analyticAt_logIterateWeight hx n)
    apply ha.congr
    have hp : ∀ᶠ y in 𝓝 x, 0 < y := lt_mem_nhds hx
    have hq : ∀ᶠ y in 𝓝 x, L^[n] y < ε :=
      (analyticAt_L_iterate hx n).continuousAt.eventually (gt_mem_nhds hn)
    filter_upwards [hp, hq] with y hy hny
    exact (hB y hy n hny).symm
  · intro x hx
    rw [hB x hx (N x hx) (hN x hx)]
    exact mul_pos (hbpos _ ⟨L_iterate_pos hx _, hN x hx⟩) (logIterateWeight_pos hx _)
  · have hBL (x : ℝ) (hx : 0 < x) : B (L x) / (1 + x) = B x := by
      obtain ⟨n, hn⟩ := exists_L_iterate_lt (L_pos hx) hε
      rw [hB (L x) (L_pos hx) n hn,
        hB x hx (n + 1) (by simpa only [Function.iterate_succ_apply] using hn),
        pullbackLogDensity_succ']
    intro x hx
    have h := hBL (E x) (E_pos hx)
    rw [L_E] at h
    have he : 1 + E x = Real.exp x := by unfold E; ring
    rw [he] at h
    exact (div_eq_iff (Real.exp_ne_zero x)).mp h |>.symm

end AbelFormalization
