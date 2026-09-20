import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The polynomial kernel for contour Hermite interpolation

Division by `X - C ζ` constructs the polynomial whose value at `z` is
`(Q(ζ) - Q(z)) / (ζ - z)` away from the diagonal. The polynomial identity
is valid on the diagonal as well, where the kernel has value `Q'(ζ)`.
-/

noncomputable section

namespace AbelFormalization

open Polynomial

/-- The polynomial divided difference with one fixed argument. -/
def hermiteKernel (Q : ℂ[X]) (ζ : ℂ) : ℂ[X] := Q /ₘ (X - C ζ)

/-- An explicit finite formula for every coefficient, polynomial in `ζ`. -/
theorem hermiteKernel_coeff (Q : ℂ[X]) (ζ : ℂ) (j : ℕ) :
    (hermiteKernel Q ζ).coeff j =
      ∑ i ∈ Finset.Icc (j + 1) Q.natDegree, ζ ^ (i - (j + 1)) * Q.coeff i :=
  Polynomial.coeff_divByMonic_X_sub_C Q ζ j

theorem hermiteKernel_mul (Q : ℂ[X]) (ζ : ℂ) :
    (X - C ζ) * hermiteKernel Q ζ = Q - C (Q.eval ζ) := by
  have h := Q.modByMonic_add_div (X - C ζ)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  change C (Q.eval ζ) + (X - C ζ) * hermiteKernel Q ζ = Q at h
  linear_combination h

/-- The numerator identity has no off-diagonal hypothesis. -/
theorem hermiteKernel_identity (Q : ℂ[X]) (ζ z : ℂ) :
    (ζ - z) * (hermiteKernel Q ζ).eval z = Q.eval ζ - Q.eval z := by
  have h := congrArg (Polynomial.eval z) (hermiteKernel_mul Q ζ)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at h
  linear_combination -h

/-- Away from the diagonal, the kernel is the usual divided difference. -/
theorem hermiteKernel_eval_of_ne (Q : ℂ[X]) {ζ z : ℂ} (h : z ≠ ζ) :
    (hermiteKernel Q ζ).eval z = (Q.eval ζ - Q.eval z) / (ζ - z) := by
  apply (eq_div_iff (sub_ne_zero.mpr h.symm)).mpr
  simpa only [mul_comm] using hermiteKernel_identity Q ζ z

/-- The diagonal value gives the removable extension of the quotient. -/
theorem hermiteKernel_eval_self (Q : ℂ[X]) (ζ : ℂ) :
    (hermiteKernel Q ζ).eval ζ = Q.derivative.eval ζ := by
  have h := congrArg (fun p : ℂ[X] => p.derivative.eval ζ) (hermiteKernel_mul Q ζ)
  simpa using h

theorem hermiteKernel_natDegree (Q : ℂ[X]) (ζ : ℂ) :
    (hermiteKernel Q ζ).natDegree = Q.natDegree - 1 := by
  rw [hermiteKernel, Polynomial.natDegree_divByMonic Q (monic_X_sub_C ζ), natDegree_X_sub_C]

/-- A degree bound suitable for a kernel of an interpolation polynomial with
`d` nodes counted with multiplicity. -/
theorem hermiteKernel_natDegree_lt (Q : ℂ[X]) (ζ : ℂ) {d : ℕ}
    (hd : 0 < d) (hQ : Q.natDegree ≤ d) : (hermiteKernel Q ζ).natDegree < d := by
  rw [hermiteKernel_natDegree]
  omega

theorem hermiteKernel_degree_lt (Q : ℂ[X]) (ζ : ℂ) (hQ : Q ≠ 0) :
    (hermiteKernel Q ζ).degree < Q.degree := by
  apply Polynomial.degree_divByMonic_lt Q (X - C ζ) hQ
  simp

end AbelFormalization
