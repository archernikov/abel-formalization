import AbelFormalization.OrdinaryHomogenization
import AbelFormalization.RestrictedExpressionTower

/-!
# Clearing a common denominator in a multivariate-polynomial evaluation
-/

noncomputable section

open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- Evaluate the degree-`D` homogenization at a common denominator `delta`
and at denominator-cleared variable values `num`.  The definition is kept as
the literal finite monomial sum needed for subalgebra membership. -/
def denominatorClearedMvPolynomialEval
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (D : ℕ) (c : R →+* S) (delta : S) (num : σ → S)
    (P : MvPolynomial σ R) : S := by
  classical
  exact ∑ d ∈ P.support,
    c (P.coeff d) * delta ^ (D - d.sum fun _ e ↦ e) *
      ∏ i ∈ d.support, num i ^ d i

/-- Literal denominator clearing: if `delta * old i = num i` for every
variable and `D` bounds the total degree, multiplying the old evaluation by
`delta^D` gives the denominator-cleared monomial sum. -/
theorem pow_mul_eval₂_eq_denominatorClearedMvPolynomialEval
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (D : ℕ) (c : R →+* S) (delta : S) (old num : σ → S)
    (P : MvPolynomial σ R) (hD : P.totalDegree ≤ D)
    (hvar : ∀ i, delta * old i = num i) :
    delta ^ D * MvPolynomial.eval₂ c old P =
      denominatorClearedMvPolynomialEval D c delta num P := by
  classical
  rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
  unfold denominatorClearedMvPolynomialEval
  apply Finset.sum_congr rfl
  intro d hd
  have hdd : d.sum (fun _ e ↦ e) ≤ D :=
    (MvPolynomial.le_totalDegree hd).trans hD
  have hprod :
      (∏ i ∈ d.support, num i ^ d i) =
        delta ^ (d.sum fun _ e ↦ e) *
          ∏ i ∈ d.support, old i ^ d i := by
    calc
      (∏ i ∈ d.support, num i ^ d i) =
          ∏ i ∈ d.support, (delta * old i) ^ d i := by
            apply Finset.prod_congr rfl
            intro z hz
            rw [hvar z]
      _ = ∏ i ∈ d.support,
          (delta ^ d i * old i ^ d i) := by
            apply Finset.prod_congr rfl
            intro z hz
            rw [mul_pow]
      _ = (∏ i ∈ d.support, delta ^ d i) *
          ∏ i ∈ d.support, old i ^ d i :=
            Finset.prod_mul_distrib
      _ = delta ^ (d.sum fun _ e ↦ e) *
          ∏ i ∈ d.support, old i ^ d i := by
            rw [Finset.prod_pow_eq_pow_sum]
            rfl
  rw [hprod]
  have hpow : delta ^ (D - d.sum (fun _ e ↦ e)) *
      delta ^ (d.sum fun _ e ↦ e) = delta ^ D := by
    rw [← pow_add, Nat.sub_add_cancel hdd]
  rw [← hpow]
  ring

/-- The cleared value belongs to a function subalgebra whenever its finitely
many coefficients, the common denominator, and its used cleared variables do. -/
theorem denominatorClearedMvPolynomialEval_mem_subalgebra
    {X R σ : Type*} [CommSemiring R]
    (B : Subalgebra ℝ (X → ℝ))
    (D : ℕ) (c : R →+* (X → ℝ)) (delta : X → ℝ)
    (num : σ → X → ℝ) (P : MvPolynomial σ R)
    (hc : ∀ d, d ∈ P.support → c (P.coeff d) ∈ B)
    (hdelta : delta ∈ B)
    (hnum : ∀ d, d ∈ P.support → ∀ i, i ∈ d.support → num i ∈ B) :
    denominatorClearedMvPolynomialEval D c delta num P ∈ B := by
  classical
  unfold denominatorClearedMvPolynomialEval
  apply B.sum_mem
  intro d hd
  exact B.mul_mem
    (B.mul_mem (hc d hd) (B.pow_mem hdelta _))
    (B.prod_mem fun i hi ↦ B.pow_mem (hnum d hd i hi) _)

/-- A finite family has an explicit common total-degree bound. -/
noncomputable def mvPolynomialFamilyTotalDegree
    {R σ : Type*} [CommSemiring R] {n : ℕ}
    (Q : Fin n → MvPolynomial σ R) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i ↦ (Q i).totalDegree

theorem mvPolynomial_totalDegree_le_familyTotalDegree
    {R σ : Type*} [CommSemiring R] {n : ℕ}
    (Q : Fin n → MvPolynomial σ R) (i : Fin n) :
    (Q i).totalDegree ≤ mvPolynomialFamilyTotalDegree Q := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun j : Fin n ↦ (Q j).totalDegree)
    (Finset.mem_univ i)

end AbelFormalization
