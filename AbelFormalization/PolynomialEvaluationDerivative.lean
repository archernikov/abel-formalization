import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Explicit differentials of actual polynomial evaluation

The differential of a fixed real multivariate polynomial is the finite sum
of its evaluated formal partial derivatives times coordinate projections.
The proof is ordinary calculus and polynomial induction. The coefficient
family theorem is a literal finite product-rule formula; no topology on the
whole polynomial ring and no compatibility of unrelated germ representatives
is assumed.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/-- The explicit continuous linear differential of polynomial evaluation. -/
def polynomialEvaluationDifferential (P : MvPolynomial ι ℝ) (z : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, MvPolynomial.eval z (MvPolynomial.pderiv i P) • ContinuousLinearMap.proj i

@[simp]
theorem polynomialEvaluationDifferential_C (c : ℝ) (z : ι → ℝ) :
    polynomialEvaluationDifferential (MvPolynomial.C c) z = 0 := by
  simp [polynomialEvaluationDifferential]

theorem polynomialEvaluationDifferential_add (P Q : MvPolynomial ι ℝ) (z : ι → ℝ) :
    polynomialEvaluationDifferential (P + Q) z =
      polynomialEvaluationDifferential P z + polynomialEvaluationDifferential Q z := by
  simp only [polynomialEvaluationDifferential, map_add, add_smul, Finset.sum_add_distrib]

theorem polynomialEvaluationDifferential_mul_X (P : MvPolynomial ι ℝ)
    (i : ι) (z : ι → ℝ) :
    polynomialEvaluationDifferential (P * MvPolynomial.X i) z =
      MvPolynomial.eval z P • ContinuousLinearMap.proj i +
        z i • polynomialEvaluationDifferential P z := by
  classical
  have hXi (j : ι) : MvPolynomial.eval z (MvPolynomial.pderiv j (MvPolynomial.X i)) =
      if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp
    · simp [MvPolynomial.pderiv_X, hji, Ne.symm hji]
  calc
    polynomialEvaluationDifferential (P * MvPolynomial.X i) z =
        (∑ j, (z i * MvPolynomial.eval z (MvPolynomial.pderiv j P)) •
          ContinuousLinearMap.proj j) +
        ∑ j, (if j = i then MvPolynomial.eval z P else 0) •
          ContinuousLinearMap.proj j := by
      unfold polynomialEvaluationDifferential
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.eval_X, hXi]
      by_cases hji : j = i <;> simp [hji, add_smul, mul_comm]
    _ = z i • polynomialEvaluationDifferential P z +
        MvPolynomial.eval z P • ContinuousLinearMap.proj i := by
      simp [polynomialEvaluationDifferential, Finset.smul_sum, smul_smul, ite_smul]
    _ = _ := add_comm _ _

set_option backward.isDefEq.respectTransparency false in
/-- The actual Fréchet derivative of real polynomial evaluation. -/
theorem hasFDerivAt_polynomial_eval (P : MvPolynomial ι ℝ) (z : ι → ℝ) :
    HasFDerivAt (fun w => MvPolynomial.eval w P) (polynomialEvaluationDifferential P z) z := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simpa only [MvPolynomial.eval_C, polynomialEvaluationDifferential_C] using
        hasFDerivAt_const (𝕜 := ℝ) c z
  | add P Q hP hQ =>
      simpa only [map_add, polynomialEvaluationDifferential_add] using! hP.fun_add hQ
  | mul_X P i hP =>
      simpa only [map_mul, MvPolynomial.eval_X, polynomialEvaluationDifferential_mul_X] using!
        hP.fun_mul (hasFDerivAt_apply i z)

theorem fderiv_polynomial_eval (P : MvPolynomial ι ℝ) (z : ι → ℝ) :
    fderiv ℝ (fun w => MvPolynomial.eval w P) z = polynomialEvaluationDifferential P z :=
  (hasFDerivAt_polynomial_eval P z).fderiv

/-- Evaluating the differential in any direction gives the usual dot product
with the evaluated formal gradient. -/
theorem fderiv_polynomial_eval_apply (P : MvPolynomial ι ℝ) (z v : ι → ℝ) :
    fderiv ℝ (fun w => MvPolynomial.eval w P) z v =
      ∑ i, MvPolynomial.eval z (MvPolynomial.pderiv i P) * v i := by
  rw [fderiv_polynomial_eval]
  simp [polynomialEvaluationDifferential]

section Composition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Polynomial evaluation along a differentiable symbol assignment, with
the chain rule written as a finite sum of scalar differentials. -/
theorem hasFDerivAt_polynomial_eval_comp (P : MvPolynomial ι ℝ)
    (z : E → ι → ℝ) (z' : ι → E →L[ℝ] ℝ) (x : E)
    (hz : ∀ i, HasFDerivAt (fun w => z w i) (z' i) x) :
    HasFDerivAt (fun w => MvPolynomial.eval (z w) P)
      (∑ i, MvPolynomial.eval (z x) (MvPolynomial.pderiv i P) • z' i) x := by
  have hzall : HasFDerivAt z (ContinuousLinearMap.pi z') x := hasFDerivAt_pi.mpr hz
  have h := (hasFDerivAt_polynomial_eval P (z x)).comp x hzall
  have hD : (polynomialEvaluationDifferential P (z x)).comp (ContinuousLinearMap.pi z') =
      ∑ i, MvPolynomial.eval (z x) (MvPolynomial.pderiv i P) • z' i := by
    ext v
    simp [polynomialEvaluationDifferential]
  simpa only [Function.comp_def, hD] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Evaluation of a literal finite coefficient family is a finite sum of
coefficient functions times fixed monomial evaluations. -/
theorem eval_coefficientFamily (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (z : E → ι → ℝ) (w : E) :
    MvPolynomial.eval (z w) (∑ d ∈ s, MvPolynomial.monomial d (a d w)) =
      ∑ d ∈ s, a d w * MvPolynomial.eval (z w) (MvPolynomial.monomial d 1) := by
  simp [map_sum, MvPolynomial.eval_monomial]

/-- A genuine chain/product rule for varying coefficient functions and
varying symbols. The finite sum is kept explicit, so it remains usable
without putting a norm on the polynomial ring. -/
theorem hasFDerivAt_eval_coefficientFamily (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (a' : (ι →₀ ℕ) → E →L[ℝ] ℝ)
    (z : E → ι → ℝ) (z' : ι → E →L[ℝ] ℝ) (x : E)
    (ha : ∀ d ∈ s, HasFDerivAt (a d) (a' d) x)
    (hz : ∀ i, HasFDerivAt (fun w => z w i) (z' i) x) :
    HasFDerivAt
      (fun w => MvPolynomial.eval (z w) (∑ d ∈ s, MvPolynomial.monomial d (a d w)))
      (∑ d ∈ s,
        (a d x • (∑ i, MvPolynomial.eval (z x)
          (MvPolynomial.pderiv i (MvPolynomial.monomial d 1)) • z' i) +
        MvPolynomial.eval (z x) (MvPolynomial.monomial d 1) • a' d)) x := by
  simp_rw [eval_coefficientFamily]
  apply HasFDerivAt.fun_sum
  intro d hd
  exact (ha d hd).mul (hasFDerivAt_polynomial_eval_comp (MvPolynomial.monomial d 1) z z' x hz)

end Composition

end AbelFormalization
