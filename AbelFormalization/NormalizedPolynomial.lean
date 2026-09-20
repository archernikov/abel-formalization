import AbelFormalization.AnalyticMultiplicity

/-!
# Factorial-normalized polynomial coefficients and jets

The manuscript writes its interpolant as `Σ a_j z^j / j!`. This module
identifies those coefficients with the polynomial's derivatives at zero and
proves the corresponding evaluation formula for every derivative.
-/

noncomputable section

namespace AbelFormalization

open Polynomial

def normalizedCoeff (P : ℂ[X]) (j : ℕ) : ℂ := (j.factorial : ℂ) * P.coeff j

theorem normalizedCoeff_zero (P : ℂ[X]) : normalizedCoeff P 0 = P.eval 0 := by
  simp [normalizedCoeff, coeff_zero_eq_eval_zero]

theorem normalizedCoeff_eq_iteratedDeriv (P : ℂ[X]) (r : ℕ) :
    normalizedCoeff P r = iteratedDeriv r (fun z => P.eval z) 0 := by
  rw [iteratedDeriv_polynomial_eval]
  change normalizedCoeff P r = (Polynomial.derivative^[r] P).eval 0
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp [normalizedCoeff, nsmul_eq_mul, Nat.descFactorial_self]

/-- The factorial-normalized expansion of any polynomial with the given
degree bound. -/
theorem polynomial_eval_normalized (P : ℂ[X]) {d : ℕ} (hd : P.natDegree < d) (z : ℂ) :
    P.eval z = ∑ j ∈ Finset.range d, normalizedCoeff P j * z ^ j / (j.factorial : ℂ) := by
  rw [eval_eq_sum_range' hd]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [normalizedCoeff]
  have hjne : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

/-- Derivatives of the factorial-normalized expansion have the manuscript's
shifted factorial denominators. -/
theorem polynomial_iteratedDeriv_normalized (P : ℂ[X]) {d r : ℕ}
    (hd : P.natDegree < d) (hr : r < d) (z : ℂ) :
    iteratedDeriv r (fun w => P.eval w) z =
      ∑ j ∈ Finset.Ico r d, normalizedCoeff P j * z ^ (j - r) / ((j - r).factorial : ℂ) := by
  have hdeg : (Polynomial.derivative^[r] P).natDegree < d - r := by
    have h := natDegree_iterate_derivative P r
    omega
  rw [iteratedDeriv_polynomial_eval]
  change (Polynomial.derivative^[r] P).eval z = _
  rw [eval_eq_sum_range' hdeg, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_iterate_derivative]
  simp only [nsmul_eq_mul, normalizedCoeff, Nat.add_sub_cancel_left]
  have hfact : ((j + r).factorial : ℂ) =
      (j.factorial : ℂ) * ((j + r).descFactorial r : ℂ) := by
    have h := Nat.factorial_mul_descFactorial (show r ≤ j + r by omega)
    simpa using (congrArg (fun n : ℕ => (n : ℂ)) h).symm
  have hjne : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [Nat.add_comm r j, hfact]
  field_simp

end AbelFormalization
