import AbelFormalization.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# The inverse of an Abel function

The inverse and its recurrence are derived from the paper's hypotheses.
No surjectivity or inverse-function hypotheses are added.
-/

noncomputable section

namespace AbelFormalization

open Set Function

/-- The inverse dynamical map on the positive half-line. -/
def L (x : ℝ) : ℝ := Real.log (1 + x)

theorem L_pos {x : ℝ} (hx : 0 < x) : 0 < L x := by
  exact Real.log_pos (by linarith)

theorem E_L {x : ℝ} (hx : 0 < x) : E (L x) = x := by
  unfold E L
  rw [Real.exp_log (by linarith : 0 < 1 + x)]
  ring

theorem L_iterate_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < L^[n] x := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using L_pos ih

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem abel_L {x : ℝ} (hx : 0 < x) : A (L x) = A x - 1 := by
  have h := hA.abel (L x) (L_pos hx)
  rw [E_L hx] at h
  linarith

theorem abel_L_iterate {x : ℝ} (hx : 0 < x) (n : ℕ) :
    A (L^[n] x) = A x - n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', hA.abel_L (L_iterate_pos hx n), ih]
      push_cast
      ring

/-- Every real number is attained at a positive argument. -/
theorem surjOn : Set.SurjOn A (Set.Ioi 0) Set.univ := by
  intro y _
  obtain ⟨n, hn⟩ := exists_nat_gt |y|
  have hlo : A (L^[n] 1) = -(n : ℝ) := by
    rw [hA.abel_L_iterate (by norm_num : (0 : ℝ) < 1), hA.normalized]
    ring
  have hhi : A (E^[n] 1) = (n : ℝ) := by
    rw [hA.abel_iterate (by norm_num : (0 : ℝ) < 1), hA.normalized]
    ring
  apply hA.analytic.continuousOn.surjOn_Icc
    (L_iterate_pos (by norm_num : (0 : ℝ) < 1) n)
    (E_iterate_pos (by norm_num : (0 : ℝ) < 1) n)
  constructor
  · rw [hlo]
    have := neg_abs_le y
    linarith
  · rw [hhi]
    exact (le_abs_self y).trans hn.le

theorem bijOn : Set.BijOn A (Set.Ioi 0) Set.univ :=
  ⟨fun _ _ => Set.mem_univ _, hA.injectiveOn, hA.surjOn⟩

end IsAbel

/-- The inverse of `A` on its positive domain. -/
def inverse (A : ℝ → ℝ) : ℝ → ℝ := Function.invFunOn A (Set.Ioi 0)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem inverse_pos (s : ℝ) : 0 < inverse A s :=
  Function.invFunOn_mem (hA.surjOn (Set.mem_univ s))

theorem apply_inverse (s : ℝ) : A (inverse A s) = s :=
  Function.invFunOn_eq (hA.surjOn (Set.mem_univ s))

theorem inverse_apply {x : ℝ} (hx : 0 < x) : inverse A (A x) = x :=
  hA.injectiveOn.leftInvOn_invFunOn hx

theorem inverse_strictMono : StrictMono (inverse A) := by
  intro a b hab
  by_contra h
  have hle := le_of_not_gt h
  have he := hA.strictMonoOn.monotoneOn (hA.inverse_pos b) (hA.inverse_pos a) hle
  rw [hA.apply_inverse, hA.apply_inverse] at he
  exact (not_le_of_gt hab) he

theorem inverse_zero : inverse A 0 = 1 := by
  rw [← hA.normalized]
  exact hA.inverse_apply (by norm_num)

theorem inverse_add_one (s : ℝ) : inverse A (s + 1) = Real.exp (inverse A s) - 1 := by
  apply hA.injectiveOn (hA.inverse_pos (s + 1)) (E_pos (hA.inverse_pos s))
  rw [hA.apply_inverse, hA.abel _ (hA.inverse_pos s), hA.apply_inverse]

theorem one_lt_inverse {s : ℝ} (hs : 0 < s) : 1 < inverse A s := by
  simpa only [hA.inverse_zero] using hA.inverse_strictMono hs

theorem inverse_eq_iff {s x : ℝ} :
    inverse A s = x ↔ 0 < x ∧ A x = s := by
  constructor
  · rintro rfl
    exact ⟨hA.inverse_pos s, hA.apply_inverse s⟩
  · rintro ⟨hx, he⟩
    rw [← he]
    exact hA.inverse_apply hx

theorem inverse_eq_iff_of_pos {s x : ℝ} (hs : 0 < s) :
    inverse A s = x ↔ 1 < x ∧ A x = s := by
  constructor
  · rintro rfl
    exact ⟨hA.one_lt_inverse hs, hA.apply_inverse s⟩
  · rintro ⟨hx, he⟩
    exact hA.inverse_eq_iff.mpr ⟨lt_trans (by norm_num) hx, he⟩

end IsAbel

end AbelFormalization
