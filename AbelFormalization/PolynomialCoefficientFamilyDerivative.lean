import AbelFormalization.PolynomialEvaluationDerivative

set_option autoImplicit false

/-!
# Coefficient and symbol parts of a polynomial-family differential

The finite product-rule differential is regrouped into the differential of
the coefficient functions and the
evaluated formal gradient in the independent symbols. No analytic-germ or
polynomial-valued differentiability hypothesis is used.
-/

noncomputable section

namespace AbelFormalization

variable {ι : Type*}

/-- The scalar coefficient of a monomial factors out of an evaluated formal
partial derivative. -/
theorem eval_pderiv_monomial_scalar (d : ι →₀ ℕ) (c : ℝ)
    (z : ι → ℝ) (i : ι) :
    MvPolynomial.eval z (MvPolynomial.pderiv i (MvPolynomial.monomial d c)) =
      c * MvPolynomial.eval z (MvPolynomial.pderiv i (MvPolynomial.monomial d 1)) := by
  have hm : (MvPolynomial.monomial d c : MvPolynomial ι ℝ) =
      MvPolynomial.C c * MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C]

/-- Formal differentiation and evaluation of a finite coefficient family
are the corresponding finite sum of monomial derivatives. -/
theorem eval_pderiv_coefficientFamily (s : Finset (ι →₀ ℕ))
    (c : (ι →₀ ℕ) → ℝ) (z : ι → ℝ) (i : ι) :
    MvPolynomial.eval z (MvPolynomial.pderiv i (∑ d ∈ s, MvPolynomial.monomial d (c d))) =
      ∑ d ∈ s, c d *
        MvPolynomial.eval z (MvPolynomial.pderiv i (MvPolynomial.monomial d 1)) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_pderiv_monomial_scalar d (c d) z i

section Differential

variable [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Regroup the literal product-rule sum as an equality of continuous linear
maps, keeping the coefficient and symbol contributions separate. -/
theorem coefficientFamily_derivative_regroup (s : Finset (ι →₀ ℕ))
    (c : (ι →₀ ℕ) → ℝ) (a' : (ι →₀ ℕ) → E →L[ℝ] ℝ)
    (z : ι → ℝ) (z' : ι → E →L[ℝ] ℝ) :
    (∑ d ∈ s,
      (c d • (∑ i, MvPolynomial.eval z
        (MvPolynomial.pderiv i (MvPolynomial.monomial d 1)) • z' i) +
      MvPolynomial.eval z (MvPolynomial.monomial d 1) • a' d)) =
    (∑ d ∈ s, MvPolynomial.eval z (MvPolynomial.monomial d 1) • a' d) +
      ∑ i, MvPolynomial.eval z
        (MvPolynomial.pderiv i (∑ d ∈ s, MvPolynomial.monomial d (c d))) • z' i := by
  classical
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_smul, eval_pderiv_coefficientFamily]

/-- The actual derivative with a coefficient term and an evaluated formal
symbol-gradient term. Only the supported coefficient functions need derivatives. -/
theorem hasFDerivAt_eval_coefficientFamily_grouped (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (a' : (ι →₀ ℕ) → E →L[ℝ] ℝ)
    (z : E → ι → ℝ) (z' : ι → E →L[ℝ] ℝ) (x : E)
    (ha : ∀ d ∈ s, HasFDerivAt (a d) (a' d) x)
    (hz : ∀ i, HasFDerivAt (fun w => z w i) (z' i) x) :
    HasFDerivAt
      (fun w => MvPolynomial.eval (z w) (∑ d ∈ s, MvPolynomial.monomial d (a d w)))
      ((∑ d ∈ s, MvPolynomial.eval (z x) (MvPolynomial.monomial d 1) • a' d) +
        ∑ i, MvPolynomial.eval (z x)
          (MvPolynomial.pderiv i (∑ d ∈ s, MvPolynomial.monomial d (a d x))) • z' i) x := by
  have h := hasFDerivAt_eval_coefficientFamily s a a' z z' x ha hz
  rw [coefficientFamily_derivative_regroup] at h
  exact h

/-- Continuous-linear-map form of the grouped Fréchet derivative. -/
theorem fderiv_eval_coefficientFamily (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (a' : (ι →₀ ℕ) → E →L[ℝ] ℝ)
    (z : E → ι → ℝ) (z' : ι → E →L[ℝ] ℝ) (x : E)
    (ha : ∀ d ∈ s, HasFDerivAt (a d) (a' d) x)
    (hz : ∀ i, HasFDerivAt (fun w => z w i) (z' i) x) :
    fderiv ℝ
      (fun w => MvPolynomial.eval (z w) (∑ d ∈ s, MvPolynomial.monomial d (a d w))) x =
      (∑ d ∈ s, MvPolynomial.eval (z x) (MvPolynomial.monomial d 1) • a' d) +
        ∑ i, MvPolynomial.eval (z x)
          (MvPolynomial.pderiv i (∑ d ∈ s, MvPolynomial.monomial d (a d x))) • z' i :=
  (hasFDerivAt_eval_coefficientFamily_grouped s a a' z z' x ha hz).fderiv

/-- Directional form: coefficient derivatives assemble into an actual
polynomial, and the remaining term is the dot product with the formal gradient. -/
theorem fderiv_eval_coefficientFamily_apply (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (a' : (ι →₀ ℕ) → E →L[ℝ] ℝ)
    (z : E → ι → ℝ) (z' : ι → E →L[ℝ] ℝ) (x h : E)
    (ha : ∀ d ∈ s, HasFDerivAt (a d) (a' d) x)
    (hz : ∀ i, HasFDerivAt (fun w => z w i) (z' i) x) :
    fderiv ℝ
      (fun w => MvPolynomial.eval (z w) (∑ d ∈ s, MvPolynomial.monomial d (a d w))) x h =
      MvPolynomial.eval (z x) (∑ d ∈ s, MvPolynomial.monomial d (a' d h)) +
        ∑ i, MvPolynomial.eval (z x)
          (MvPolynomial.pderiv i (∑ d ∈ s, MvPolynomial.monomial d (a d x))) * z' i h := by
  classical
  rw [fderiv_eval_coefficientFamily s a a' z z' x ha hz]
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [MvPolynomial.eval_monomial, mul_comm]

end Differential

end AbelFormalization
