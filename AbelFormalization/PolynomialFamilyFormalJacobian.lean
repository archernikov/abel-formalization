import AbelFormalization.PolynomialCoefficientFamilyDerivative
import AbelFormalization.SurjectiveJacobianRank
import Mathlib.LinearAlgebra.Pi

/-!
# An actual polynomial family factors through its formal Jacobian

The source is an arbitrary real
normed space. Only the coefficient argument and the independent symbol
argument have finite coordinate sets. The two sets of formal columns are
kept separate using `Fin p ⊕ ι`.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {ι : Type*} [Fintype ι] {p n : ℕ}

/-- A scalar continuous linear map on finitely many real coordinates is
the dot product with its values on the coordinate directions. -/
theorem continuousLinearMap_fin_apply
    (L : (Fin p → ℝ) →L[ℝ] ℝ) (v : Fin p → ℝ) :
    L v = ∑ j, L (Pi.single j 1) * v j := by
  classical
  have hsingle (i : Fin p) :
      (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  simpa only [hsingle, smul_eq_mul, mul_comm] using!
    LinearMap.pi_apply_eq_sum_univ L.toLinearMap v

omit [Fintype ι] in
/-- Evaluated coefficient differentials split into the formal coordinate
partials, even when the finite sum has redundant or zero monomials. -/
theorem eval_linearCoefficientFamily_fin_coordinates
    (s : Finset (ι →₀ ℕ)) (L : (ι →₀ ℕ) → (Fin p → ℝ) →L[ℝ] ℝ)
    (z : ι → ℝ) (v : Fin p → ℝ) :
    MvPolynomial.eval z (∑ d ∈ s, MvPolynomial.monomial d (L d v)) =
      ∑ j, MvPolynomial.eval z
        (∑ d ∈ s, MvPolynomial.monomial d (L d (Pi.single j 1))) * v j := by
  classical
  have hL (d : ι →₀ ℕ) : L d v = ∑ j, L d (Pi.single j 1) * v j :=
    continuousLinearMap_fin_apply (L d) v
  calc
    MvPolynomial.eval z (∑ d ∈ s, MvPolynomial.monomial d (L d v)) =
        ∑ d ∈ s, (∑ j, L d (Pi.single j 1) * v j) *
          d.prod (fun i k => z i ^ k) := by
      simp only [map_sum, MvPolynomial.eval_monomial, hL, Finset.sum_mul]
    _ = ∑ j, (∑ d ∈ s, L d (Pi.single j 1) *
          d.prod (fun i k => z i ^ k)) * v j := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro d hd
      exact mul_right_comm _ _ _
    _ = _ := by simp only [map_sum, MvPolynomial.eval_monomial]

/-- The actual finite system of evaluated polynomial equations. -/
def polynomialFamilyEvaluation {E : Type*}
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : E → Fin p → ℝ) (z : E → ι → ℝ) : E → Fin n → ℝ :=
  fun x i => MvPolynomial.eval (z x)
    (∑ d ∈ s i, MvPolynomial.monomial d (a i d (w x)))

/-- The formal Jacobian first differentiates coefficient functions in
their finite coordinate arguments, then differentiates the independent
polynomial symbols. Both blocks are evaluated at the specified arguments. -/
def polynomialFamilyFormalJacobian
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (u : Fin p → ℝ) (z : ι → ℝ) : Matrix (Fin n) (Fin p ⊕ ι) ℝ :=
  fun i => Sum.elim
    (fun j => MvPolynomial.eval z (∑ d ∈ s i,
      MvPolynomial.monomial d (fderiv ℝ (a i d) u (Pi.single j 1))))
    (fun j => MvPolynomial.eval z (MvPolynomial.pderiv j
      (∑ d ∈ s i, MvPolynomial.monomial d (a i d u))))

section Source

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Supported differentiable coefficients and differentiable argument
maps give a differentiable actual equation system. -/
theorem differentiableAt_polynomialFamilyEvaluation
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : E → Fin p → ℝ) (z : E → ι → ℝ) (x : E)
    (hw : DifferentiableAt ℝ w x) (hz : DifferentiableAt ℝ z x)
    (ha : ∀ i d, d ∈ s i → DifferentiableAt ℝ (a i d) (w x)) :
    DifferentiableAt ℝ (polynomialFamilyEvaluation s a w z) x := by
  apply differentiableAt_pi.mpr
  intro i
  exact (hasFDerivAt_eval_coefficientFamily_grouped (s i)
    (fun d t => a i d (w t))
    (fun d => (fderiv ℝ (a i d) (w x)).comp (fderiv ℝ w x))
    z (fun j => (ContinuousLinearMap.proj j).comp (fderiv ℝ z x)) x
    (fun d hd => (ha i d hd).hasFDerivAt.comp x hw.hasFDerivAt)
    (hasFDerivAt_pi'.mp hz.hasFDerivAt)).differentiableAt

/-- The genuine Fréchet derivative of the equation system factors through
the formal Jacobian. No finite-dimensionality assumption on `E` is used. -/
theorem fderiv_polynomialFamilyEvaluation_factorization
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : E → Fin p → ℝ) (z : E → ι → ℝ) (x : E)
    (hw : DifferentiableAt ℝ w x) (hz : DifferentiableAt ℝ z x)
    (ha : ∀ i d, d ∈ s i → DifferentiableAt ℝ (a i d) (w x))
    (h : E) :
    fderiv ℝ (polynomialFamilyEvaluation s a w z) x h =
      (polynomialFamilyFormalJacobian s a (w x) (z x)).mulVec
        (Sum.elim (fderiv ℝ w x h) (fderiv ℝ z x h)) := by
  classical
  have hF := differentiableAt_polynomialFamilyEvaluation s a w z x hw hz ha
  funext i
  have hcoordinate :
      (fderiv ℝ (polynomialFamilyEvaluation s a w z) x h) i =
        fderiv ℝ (fun t => polynomialFamilyEvaluation s a w z t i) x h := by
    rw [fderiv_apply hF i]
    rfl
  rw [hcoordinate]
  change fderiv ℝ
    (fun t => MvPolynomial.eval (z t)
      (∑ d ∈ s i, MvPolynomial.monomial d (a i d (w t)))) x h = _
  rw [fderiv_eval_coefficientFamily_apply (s i)
    (fun d t => a i d (w t))
    (fun d => (fderiv ℝ (a i d) (w x)).comp (fderiv ℝ w x))
    z (fun j => (ContinuousLinearMap.proj j).comp (fderiv ℝ z x)) x h
    (fun d hd => (ha i d hd).hasFDerivAt.comp x hw.hasFDerivAt)
    (hasFDerivAt_pi'.mp hz.hasFDerivAt)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [eval_linearCoefficientFamily_fin_coordinates]
  simp only [polynomialFamilyFormalJacobian, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- A surjective actual differential forces positivity of the sum of the
squares of all full-row-size formal Jacobian minors. -/
theorem polynomialFamilyFormalJacobian_sumSquares_pos
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : E → Fin p → ℝ) (z : E → ι → ℝ) (x : E)
    (hw : DifferentiableAt ℝ w x) (hz : DifferentiableAt ℝ z x)
    (ha : ∀ i d, d ∈ s i → DifferentiableAt ℝ (a i d) (w x))
    (hregular : Function.Surjective
      (fderiv ℝ (polynomialFamilyEvaluation s a w z) x)) :
    0 < sumSquaresColumnMinors (polynomialFamilyFormalJacobian s a (w x) (z x)) := by
  exact sumSquaresColumnMinors_pos_of_surjective_continuousLinearMap_factorization
    (polynomialFamilyFormalJacobian s a (w x) (z x))
    (fderiv ℝ (polynomialFamilyEvaluation s a w z) x)
    (fun h => Sum.elim (fderiv ℝ w x h) (fderiv ℝ z x h)) hregular
    (fderiv_polynomialFamilyEvaluation_factorization s a w z x hw hz ha)

end Source

end AbelFormalization
