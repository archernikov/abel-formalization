import AbelFormalization.ComplexEstimates

/-! # A common complex extension on a right half-strip

The compatible disk extensions of an Abel function determine one analytic
function on each sufficiently far right half-strip.  Its logarithmic bound is
expressed in terms of the real part of the argument.
-/

open Set Filter Metric
open scoped Topology

namespace AbelFormalization

/-- A horizontal strip restricted to the right of a real threshold. -/
def rightHalfStrip (X M : ℝ) : Set ℂ :=
  {z | X < z.re ∧ |z.im| < M}

theorem isOpen_rightHalfStrip (X M : ℝ) : IsOpen (rightHalfStrip X M) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)

/-- The vertical distance to the real axis is the absolute imaginary part. -/
theorem mem_ball_realPart_iff (z : ℂ) (M : ℝ) :
    z ∈ ball (z.re : ℂ) M ↔ |z.im| < M := by
  rw [mem_ball, Complex.dist_of_re_eq (by simp)]
  simp

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- A single complex analytic extension exists on any fixed-width right
half-strip, with a uniform logarithmic bound. -/
theorem exists_bounded_complex_strip {M : ℝ} (hM : 0 < M) :
    ∃ X K : ℝ, ∃ F : ℂ → ℂ, 1 < X ∧ 0 < K ∧
      AnalyticOnNhd ℂ F (rightHalfStrip X M) ∧
      (∀ x : ℝ, X < x → F (x : ℂ) = (A x : ℂ)) ∧
      ∀ z ∈ rightHalfStrip X M, ‖F z‖ ≤ K * Real.log z.re := by
  classical
  obtain ⟨X, K, B, hX, hK, hB, hcompat⟩ :=
    hA.exists_compatible_bounded_complex_extensions hM
  let F : ℂ → ℂ := fun z => B z.re z
  refine ⟨X, K, F, hX, hK, ?_, ?_, ?_⟩
  · intro z hz
    have hzball : z ∈ ball (z.re : ℂ) M :=
      (mem_ball_realPart_iff z M).mpr hz.2
    apply ((hB z.re hz.1).1 z hzball).congr
    filter_upwards [(isOpen_rightHalfStrip X M).mem_nhds hz,
      isOpen_ball.mem_nhds hzball] with w hw hwball
    exact hcompat z.re w.re hz.1 hw.1
      ⟨hwball, (mem_ball_realPart_iff w M).mpr hw.2⟩
  · intro x hx
    exact (hB x hx).2.1 x (mem_ball_self hM)
  · intro z hz
    exact (hB z.re hz.1).2.2 z ((mem_ball_realPart_iff z M).mpr hz.2)

end IsAbel
end AbelFormalization
