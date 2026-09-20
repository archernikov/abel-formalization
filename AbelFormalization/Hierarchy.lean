import AbelFormalization.InverseEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Separation of inverse Abel values

This proves the first assertion of the manuscript's separation lemma for real
sequences. Its proof needs only the lower bound on the smaller Abel time, so
the unused upper bound on the larger Abel time is omitted.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

private theorem tendsto_real_sub_const (d : ℝ) :
    Tendsto (fun s : ℝ => s - d) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + d)] with s hs
  linarith

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

private theorem logLog_inverse_differentiableAt {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (fun t => Real.log (Real.log (inverse A t))) s :=
  (((hA.inverse_hasDerivAt s).log (ne_of_gt (hA.inverse_pos s))).log
    (ne_of_gt (Real.log_pos (hA.one_lt_inverse hs)))).differentiableAt

/-- A mean-value estimate for the double logarithm, uniformly on a tail. -/
theorem logLog_inverse_increment_lower_bound :
    ∃ R : ℝ, ∀ a b : ℝ, R ≤ b → b < a →
      (a - b) * inverse A (b - 2) ≤
        Real.log (Real.log (inverse A a)) - Real.log (Real.log (inverse A b)) := by
  obtain ⟨r, hr⟩ := eventually_atTop.mp hA.eventually_logLog_inverse_deriv_estimates
  refine ⟨max r 1, ?_⟩
  intro a b hb hab
  have hbpos : 0 < b := by have := le_max_right r 1; linarith
  let f : ℝ → ℝ := fun s => Real.log (Real.log (inverse A s))
  have hcont : ContinuousOn f (Icc b a) := by
    intro x hx
    exact (hA.logLog_inverse_differentiableAt (hbpos.trans_le hx.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo b a) := by
    intro x hx
    exact (hA.logLog_inverse_differentiableAt (hbpos.trans hx.1)).differentiableWithinAt
  obtain ⟨z, hz, hder⟩ := exists_deriv_eq_slope f hab hcont hdiff
  have hzlarge : r ≤ z := (le_max_left r 1).trans (hb.trans hz.1.le)
  have hinv : inverse A (b - 2) ≤ inverse A (z - 2) :=
    hA.inverse_strictMono.monotone (sub_le_sub_right hz.1.le 2)
  have hbound : inverse A (b - 2) < (f a - f b) / (a - b) := by
    rw [← hder]
    exact (hinv.trans_lt (hr z hzlarge).2).trans (hr z hzlarge).1
  have hmul := (lt_div_iff₀ (sub_pos.mpr hab)).mp hbound
  simpa only [mul_comm] using hmul.le

/-- One unit of Abel time multiplies the inverse by a factor tending to infinity. -/
theorem inverse_add_one_div_tendsto_atTop :
    Tendsto (fun s : ℝ => inverse A (s + 1) / inverse A s) atTop atTop := by
  have h := (Real.tendsto_mul_exp_add_div_pow_atTop 1 (-1) 1 zero_lt_one).comp
    hA.inverse_tendsto_atTop
  simpa only [Function.comp_def, one_mul, pow_one, ← sub_eq_add_neg,
    hA.inverse_add_one] using h

/-- The same domination holds for any fixed shift of at least one. -/
theorem inverse_shift_div_tendsto_atTop {d : ℝ} (hd : 1 ≤ d) :
    Tendsto (fun s : ℝ => inverse A (s + d) / inverse A s) atTop atTop := by
  apply tendsto_atTop_mono _ hA.inverse_add_one_div_tendsto_atTop
  intro s
  exact div_le_div_of_nonneg_right
    (hA.inverse_strictMono.monotone (by linarith : s + 1 ≤ s + d)) (hA.inverse_pos s).le

/-- The double-logarithm gap diverges under the separation hypothesis. -/
theorem hierarchy_logLog_gap_tendsto_atTop
    (t a b : ℕ → ℝ) {D N c : ℝ} (hc : 0 < c) (hN : D + 4 ≤ N)
    (ht : Tendsto t atTop atTop)
    (horder : ∀ᶠ n in atTop, t n - D ≤ b n ∧ b n < a n)
    (hgap : ∀ᶠ n in atTop, c / inverse A (t n - N) ≤ a n - b n) :
    Tendsto (fun n => Real.log (Real.log (inverse A (a n))) -
      Real.log (Real.log (inverse A (b n)))) atTop atTop := by
  have hb : Tendsto b atTop atTop :=
    tendsto_atTop_mono' atTop (horder.mono fun _ h => h.1)
      ((tendsto_real_sub_const D).comp ht)
  have hscale : Tendsto (fun n =>
      c * (inverse A (t n - D - 2) / inverse A (t n - N))) atTop atTop := by
    have h := ((hA.inverse_shift_div_tendsto_atTop
      (d := N - D - 2) (by linarith)).comp ((tendsto_real_sub_const N).comp ht)).const_mul_atTop hc
    convert h using 1
    funext n
    simp only [Function.comp_apply]
    rw [show t n - N + (N - D - 2) = t n - D - 2 by ring]
  obtain ⟨R, hR⟩ := hA.logLog_inverse_increment_lower_bound
  apply tendsto_atTop_mono' atTop _ hscale
  filter_upwards [horder, hgap, hb.eventually (eventually_ge_atTop R)] with n hn hg hbR
  have hi : inverse A (t n - D - 2) ≤ inverse A (b n - 2) :=
    hA.inverse_strictMono.monotone (sub_le_sub_right hn.1 2)
  calc
    c * (inverse A (t n - D - 2) / inverse A (t n - N)) =
        (c / inverse A (t n - N)) * inverse A (t n - D - 2) := by ring
    _ ≤ (a n - b n) * inverse A (t n - D - 2) :=
      mul_le_mul_of_nonneg_right hg (hA.inverse_pos _).le
    _ ≤ (a n - b n) * inverse A (b n - 2) :=
      mul_le_mul_of_nonneg_left hi (sub_pos.mpr hn.2).le
    _ ≤ Real.log (Real.log (inverse A (a n))) -
        Real.log (Real.log (inverse A (b n))) := hR (a n) (b n) hbR hn.2

/-- The first assertion of the separation lemma. In fact every real power `q`
is allowed, so the manuscript's case `q > 0` is included. -/
theorem hierarchy_separation
    (t a b : ℕ → ℝ) {D N c : ℝ} (hc : 0 < c) (hN : D + 4 ≤ N)
    (ht : Tendsto t atTop atTop)
    (horder : ∀ᶠ n in atTop, t n - D ≤ b n ∧ b n < a n)
    (hgap : ∀ᶠ n in atTop, c / inverse A (t n - N) ≤ a n - b n)
    (q : ℝ) :
    Tendsto (fun n => inverse A (a n) / (inverse A (b n)) ^ q) atTop atTop := by
  have hb : Tendsto b atTop atTop :=
    tendsto_atTop_mono' atTop (horder.mono fun _ h => h.1)
      ((tendsto_real_sub_const D).comp ht)
  have ha : Tendsto a atTop atTop :=
    tendsto_atTop_mono' atTop (horder.mono fun _ h => h.2.le) hb
  have hla : Tendsto (fun n => Real.log (inverse A (a n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hA.inverse_tendsto_atTop.comp ha)
  have hlb : Tendsto (fun n => Real.log (inverse A (b n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hA.inverse_tendsto_atTop.comp hb)
  have hratio : Tendsto (fun n =>
      Real.log (inverse A (a n)) / Real.log (inverse A (b n))) atTop atTop := by
    have h := Real.tendsto_exp_atTop.comp
      (hA.hierarchy_logLog_gap_tendsto_atTop t a b hc hN ht horder hgap)
    apply h.congr'
    filter_upwards [hla.eventually (eventually_gt_atTop 0),
      hlb.eventually (eventually_gt_atTop 0)] with n hnA hnB
    simp only [Function.comp_def, Real.exp_sub, Real.exp_log hnA, Real.exp_log hnB]
  have hdiff : Tendsto (fun n =>
      Real.log (inverse A (a n)) - q * Real.log (inverse A (b n))) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hlb
    filter_upwards [hratio.eventually (eventually_ge_atTop (q + 1)),
      hlb.eventually (eventually_gt_atTop 0)] with n hn hnB
    have h := (le_div_iff₀ hnB).mp hn
    nlinarith
  have hlog : Tendsto (fun n =>
      Real.log (inverse A (a n) / (inverse A (b n)) ^ q)) atTop atTop := by
    convert hdiff using 1
    funext n
    rw [Real.log_div (ne_of_gt (hA.inverse_pos _))
      (ne_of_gt (Real.rpow_pos_of_pos (hA.inverse_pos _) q)),
      Real.log_rpow (hA.inverse_pos _) q]
  apply (Real.tendsto_exp_atTop.comp hlog).congr'
  filter_upwards [] with n
  exact Real.exp_log (div_pos (hA.inverse_pos _)
    (Real.rpow_pos_of_pos (hA.inverse_pos _) q))

end IsAbel

end AbelFormalization
