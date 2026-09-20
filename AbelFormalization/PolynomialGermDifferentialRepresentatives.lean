import AbelFormalization.PolynomialGermIdentities
import AbelFormalization.PolynomialGermDerivations

/-!
# Derivative representatives from the same finite coefficient family

The actual coefficient derivation is represented by differentiating the
chosen analytic coefficient functions. Every finite expansion uses the
original polynomial support, even when differentiation annihilates some
coefficient germs. Symbol differentiation is compatible with the same
polynomial-valued representative by an exact finite monomial calculation.
-/

noncomputable section

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The polynomial-valued germ of an arbitrary finite analytic monomial
sum. The finite set need not equal the support after summing. -/
theorem analyticPolynomialGermHom_sum_monomial_of (x : E)
    (s : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → E → ℝ)
    (ha : ∀ d, AnalyticAt ℝ (a d) x) :
    analyticPolynomialGermHom x
        (∑ d ∈ s, MvPolynomial.monomial d (analyticGermOf (a d) (ha d))) =
      (polynomialFromCoefficientRepresentatives s a :
        Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  classical
  have hfun : polynomialFromCoefficientRepresentatives s a =
      ∑ d ∈ s, (fun w => MvPolynomial.monomial d (a d w)) := by
    funext w
    simp only [polynomialFromCoefficientRepresentatives, Finset.sum_apply]
  rw [map_sum]
  calc
    (∑ d ∈ s, analyticPolynomialGermHom x
      (MvPolynomial.monomial d (analyticGermOf (a d) (ha d)))) =
        ∑ d ∈ s, ((fun w => MvPolynomial.monomial d (a d w)) :
          Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact analyticPolynomialGermHom_monomial_of x d (a d) (ha d)
    _ = _ := by
      rw [hfun]
      exact (map_sum (Germ.coeRingHom (𝓝 x)) _ _).symm

/-- The coefficient derivation has a finite expansion using exactly the
original support and the derivatives of the originally chosen functions. -/
theorem mvPolynomialCoefficientDerivation_eq_same_support_sum
    (x v : E) (P : MvPolynomial ι (AnalyticGermAt x))
    (a : (ι →₀ ℕ) → E → ℝ) (ha : ∀ d, AnalyticAt ℝ (a d) x)
    (hrep : ∀ d ∈ P.support, P.coeff d = analyticGermOf (a d) (ha d)) :
    mvPolynomialCoefficientDerivation (analyticGermDerivation x v) P =
      ∑ d ∈ P.support, MvPolynomial.monomial d
        (analyticGermOf (fun w => fderiv ℝ (a d) w v)
          (analyticAt_directionalDerivative (ha d) v)) := by
  classical
  calc
    mvPolynomialCoefficientDerivation (analyticGermDerivation x v) P =
        ∑ d ∈ P.support,
          mvPolynomialCoefficientDerivation (analyticGermDerivation x v)
            (MvPolynomial.monomial d (P.coeff d)) := by
      rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [mvPolynomialCoefficientDerivation_monomial, hrep d hd, analyticGermDerivation_of]

/-- Exact compatibility between the actual germ coefficient derivation and
the derivative polynomial-valued representative formed from the same data. -/
theorem analyticPolynomialGermHom_coefficientDerivation_eq_representative
    (x v : E) (P : MvPolynomial ι (AnalyticGermAt x))
    (a : (ι →₀ ℕ) → E → ℝ) (ha : ∀ d, AnalyticAt ℝ (a d) x)
    (hrep : ∀ d ∈ P.support, P.coeff d = analyticGermOf (a d) (ha d)) :
    analyticPolynomialGermHom x
        (mvPolynomialCoefficientDerivation (analyticGermDerivation x v) P) =
      (polynomialFromCoefficientRepresentatives P.support
        (fun d w => fderiv ℝ (a d) w v) : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  rw [mvPolynomialCoefficientDerivation_eq_same_support_sum x v P a ha hrep]
  exact analyticPolynomialGermHom_sum_monomial_of x P.support _
    (fun d => analyticAt_directionalDerivative (ha d) v)

/-- Every coefficient function of this explicit derivative representative
is analytic at the base point, including the coefficients outside the fixed
support, which vanish identically. -/
theorem analyticAt_same_support_derivative_coefficient (x v : E)
    (s : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → E → ℝ)
    (ha : ∀ d, AnalyticAt ℝ (a d) x) (d : ι →₀ ℕ) :
    AnalyticAt ℝ (fun w =>
      (polynomialFromCoefficientRepresentatives s
        (fun e z => fderiv ℝ (a e) z v) w).coeff d) x := by
  classical
  by_cases hd : d ∈ s
  · simpa only [polynomialFromCoefficientRepresentatives_coeff, ite_eq_left hd] using
      analyticAt_directionalDerivative (ha d) v
  · simpa only [polynomialFromCoefficientRepresentatives_coeff, ite_eq_right hd] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : E => (0 : ℝ)) x)

/-- Symbol differentiation commutes with the polynomial-valued germ map
on each monomial represented by an actual analytic coefficient function. -/
theorem analyticPolynomialGermHom_pderiv_monomial_of (x : E)
    (j : ι) (d : ι →₀ ℕ) (a : E → ℝ) (ha : AnalyticAt ℝ a x) :
    analyticPolynomialGermHom x
        (MvPolynomial.pderiv j (MvPolynomial.monomial d (analyticGermOf a ha))) =
      ((fun w => MvPolynomial.pderiv j (MvPolynomial.monomial d (a w))) :
        Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  classical
  have hnat : (d j : AnalyticGermAt x) =
      analyticGermOf (fun _ : E => (d j : ℝ)) analyticAt_const := by
    rw [← analyticGerm_algebraMap]
    simp
  have hscale : analyticGermOf a ha * (d j : AnalyticGermAt x) =
      analyticGermOf (fun w => a w * (d j : ℝ)) (ha.mul analyticAt_const) := by
    rw [hnat, ← analyticGermOf_mul]
    rfl
  rw [MvPolynomial.pderiv_monomial, hscale, analyticPolynomialGermHom_monomial_of]
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun w => MvPolynomial.pderiv_monomial.symm

/-- The symbol derivative has the literal pointwise symbol derivative of
the same finite polynomial family as a representative. No relation between
the two polynomial supports is assumed. -/
theorem analyticPolynomialGermHom_pderiv_eq_representative
    (x : E) (j : ι) (P : MvPolynomial ι (AnalyticGermAt x))
    (a : (ι →₀ ℕ) → E → ℝ) (ha : ∀ d, AnalyticAt ℝ (a d) x)
    (hrep : ∀ d ∈ P.support, P.coeff d = analyticGermOf (a d) (ha d)) :
    analyticPolynomialGermHom x (MvPolynomial.pderiv j P) =
      ((fun w => MvPolynomial.pderiv j
        (polynomialFromCoefficientRepresentatives P.support a w)) :
          Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  classical
  have hfun : (fun w => MvPolynomial.pderiv j
      (polynomialFromCoefficientRepresentatives P.support a w)) =
      ∑ d ∈ P.support, (fun w => MvPolynomial.pderiv j (MvPolynomial.monomial d (a d w))) := by
    funext w
    simp only [polynomialFromCoefficientRepresentatives, map_sum, Finset.sum_apply]
  calc
    analyticPolynomialGermHom x (MvPolynomial.pderiv j P) =
        ∑ d ∈ P.support, analyticPolynomialGermHom x
          (MvPolynomial.pderiv j (MvPolynomial.monomial d (P.coeff d))) := by
      rw [← map_sum, ← map_sum, MvPolynomial.support_sum_monomial_coeff]
    _ = ∑ d ∈ P.support, ((fun w =>
        MvPolynomial.pderiv j (MvPolynomial.monomial d (a d w))) :
          Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hrep d hd, analyticPolynomialGermHom_pderiv_monomial_of]
    _ = _ := by
      rw [hfun]
      exact (map_sum (Germ.coeRingHom (𝓝 x)) _ _).symm

end AbelFormalization
