import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Growth of inverse Abel functions

The growth conclusion needs only monotonicity, the inverse Abel recurrence,
and one value at least two. In particular, this argument does not assume the
o-minimality conclusion of the manuscript.
-/

namespace AbelFormalization

private theorem exp_sub_one_ge_add_two {x : ℝ} (hx : 2 ≤ x) :
    x + 2 ≤ Real.exp x - 1 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := x) (by linarith)
  nlinarith [sq_nonneg (x - 2)]

private theorem exp_add_one_sub_one_ge {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x + 1 ≤ Real.exp (x + 1) - 1 := by
  rw [Real.exp_add]
  have hx' : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr h1)]

private theorem self_le_exp_iterate (k : ℕ) (x : ℝ) :
    x ≤ (Real.exp^[k]) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      linarith [Real.add_one_le_exp ((Real.exp^[k]) x)]

/-- At integer times after a value at least two, the inverse Abel function
increases by at least two per unit of time. -/
theorem linear_lower_bound_nat {T : ℝ → ℝ} (hmono : Monotone T)
    (hstep : ∀ s : ℝ, T (s + 1) = Real.exp (T s) - 1)
    {r : ℝ} (hr : 2 ≤ T r) (n : ℕ) :
    T r + 2 * (n : ℝ) ≤ T (r + (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hbase : 2 ≤ T (r + (n : ℝ)) := by
        apply hr.trans
        apply hmono
        exact le_add_of_nonneg_right (Nat.cast_nonneg n)
      have hinc := exp_sub_one_ge_add_two hbase
      rw [← hstep (r + (n : ℝ))] at hinc
      simp only [Nat.cast_succ]
      calc
        T r + 2 * ((n : ℝ) + 1) ≤ T (r + (n : ℝ)) + 2 := by linarith
        _ ≤ T ((r + (n : ℝ)) + 1) := hinc
        _ = T (r + ((n : ℝ) + 1)) := by congr 1; ring

/-- Every fixed affine function of slope one is eventually below `T`. -/
theorem eventually_affine_lower_bound {T : ℝ → ℝ} (hmono : Monotone T)
    (hstep : ∀ s : ℝ, T (s + 1) = Real.exp (T s) - 1)
    (hlarge : ∃ r : ℝ, 2 ≤ T r) (c : ℝ) :
    ∃ threshold : ℝ, ∀ s : ℝ, threshold ≤ s → s + c + 1 ≤ T s := by
  obtain ⟨r, hr⟩ := hlarge
  refine ⟨max r (2 * r + c + 3 - T r), ?_⟩
  intro s hs
  have hrs : r ≤ s := (le_max_left _ _).trans hs
  have hthreshold : 2 * r + c + 3 - T r ≤ s := (le_max_right _ _).trans hs
  let n : ℕ := ⌊s - r⌋₊
  have hnlo : (n : ℝ) ≤ s - r := Nat.floor_le (by linarith)
  have hnhi : s - r < (n : ℝ) + 1 := Nat.lt_floor_add_one (s - r)
  have hlinear := linear_lower_bound_nat hmono hstep hr n
  have hcompare : T (r + (n : ℝ)) ≤ T s := hmono (by linarith)
  linarith

/-- Stronger than transexponential growth: any fixed translation of the
argument can be absorbed, with a positive additive margin. -/
theorem eventually_exp_iterate_lower_bound {T : ℝ → ℝ} (hmono : Monotone T)
    (hstep : ∀ s : ℝ, T (s + 1) = Real.exp (T s) - 1)
    (hlarge : ∃ r : ℝ, 2 ≤ T r) (k : ℕ) (c : ℝ) :
    ∃ threshold : ℝ, ∀ s : ℝ, threshold ≤ s →
      (Real.exp^[k]) (s + c) + 1 ≤ T s := by
  induction k generalizing c with
  | zero =>
      simpa using eventually_affine_lower_bound hmono hstep hlarge c
  | succ k ih =>
      obtain ⟨r, hr⟩ := ih (c + 1)
      refine ⟨max (r + 1) (1 - c), ?_⟩
      intro s hs
      have hsr : r + 1 ≤ s := (le_max_left _ _).trans hs
      have hsc : 1 - c ≤ s := (le_max_right _ _).trans hs
      have hprev := hr (s - 1) (by linarith)
      have harg : s - 1 + (c + 1) = s + c := by ring
      rw [harg] at hprev
      have hx : 1 ≤ (Real.exp^[k]) (s + c) :=
        le_trans (by linarith) (self_le_exp_iterate k (s + c))
      have hexp := Real.exp_le_exp.mpr hprev
      have hmargin := exp_add_one_sub_one_ge hx
      have hrec : T s = Real.exp (T (s - 1)) - 1 := by
        simpa using hstep (s - 1)
      rw [Function.iterate_succ_apply', hrec]
      linarith

/-- The precise growth assertion in the manuscript, independent of its
proposed o-minimality argument. -/
theorem transexponential_of_recurrence {T : ℝ → ℝ} (hmono : Monotone T)
    (hstep : ∀ s : ℝ, T (s + 1) = Real.exp (T s) - 1)
    (hlarge : ∃ r : ℝ, 2 ≤ T r) :
    ∀ k : ℕ, ∃ threshold : ℝ, ∀ s : ℝ, threshold < s →
      (Real.exp^[k]) s < T s := by
  intro k
  obtain ⟨r, hr⟩ := eventually_exp_iterate_lower_bound hmono hstep hlarge k 0
  refine ⟨r, ?_⟩
  intro s hs
  have h := hr s hs.le
  simp only [add_zero] at h
  linarith

end AbelFormalization
