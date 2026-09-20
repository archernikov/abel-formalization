import Mathlib.Data.Real.Basic

example {k : ℕ} (F : (Fin (0 + k) → ℝ) → ℝ)
    (x : Fin (0 + k) → ℝ) : True := by
  rw [Nat.zero_add k] at F x
  trivial

example {k : ℕ} (F : Fin (0 + k) → ℝ)
    (x : Fin (0 + k)) (h : F x = 0) :
    ∃ (G : Fin k → ℝ) (y : Fin k), G y = 0 := by
  have hzk : 0 + k = k := Nat.zero_add k
  cases hzk
  exact ⟨F, x, h⟩
