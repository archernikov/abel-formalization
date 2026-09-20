import AbelFormalization.HermiteKernel
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.Polynomial

/-! # The contour polynomial and analytic Hermite remainder

The coefficients of the interpolation polynomial are contour integrals of the
polynomial divided-difference kernel.  The construction requires no choice of
distinct interpolation nodes: repeated roots are carried by the polynomial `Q`.
-/

noncomputable section

open Set Metric Polynomial
open scoped Topology

namespace AbelFormalization

/-- The normalization in the Cauchy integral formula. -/
def cauchyNormalization : ℂ := (2 * Real.pi * Complex.I)⁻¹

/-- The coefficient of the contour interpolation polynomial. -/
def hermiteContourCoeff (f : ℂ → ℂ) (Q : ℂ[X]) (R : ℝ) (j : ℕ) : ℂ :=
  cauchyNormalization *
    ∮ ζ in C(0, R), (hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ

/-- The contour interpolation polynomial has fewer coefficients than `Q`. -/
def hermiteContourPolynomial (f : ℂ → ℂ) (Q : ℂ[X]) (R : ℝ) : ℂ[X] :=
  ∑ j ∈ Finset.range Q.natDegree, monomial j (hermiteContourCoeff f Q R j)

/-- The analytic factor of the interpolation remainder. -/
def hermiteContourQuotient (f : ℂ → ℂ) (Q : ℂ[X]) (R : ℝ) (z : ℂ) : ℂ :=
  cauchyNormalization * ∮ ζ in C(0, R), f ζ / (Q.eval ζ * (ζ - z))

theorem hermiteContourPolynomial_degree_lt (f : ℂ → ℂ) (Q : ℂ[X]) (R : ℝ) :
    (hermiteContourPolynomial f Q R).degree < (Q.natDegree : WithBot ℕ) := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro j hj
  exact (degree_monomial_le _ _).trans_lt
    (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hj))

theorem hermiteContourPolynomial_natDegree_lt (f : ℂ → ℂ) (Q : ℂ[X]) (R : ℝ)
    (hd : 0 < Q.natDegree) : (hermiteContourPolynomial f Q R).natDegree < Q.natDegree := by
  by_cases hP : hermiteContourPolynomial f Q R = 0
  · simpa only [hP, natDegree_zero] using hd
  · exact (natDegree_lt_iff_degree_lt hP).mpr
      (hermiteContourPolynomial_degree_lt f Q R)

theorem hermiteContourPolynomial_coeff (f : ℂ → ℂ) (Q : ℂ[X]) (R : ℝ)
    {j : ℕ} (hj : j < Q.natDegree) :
    (hermiteContourPolynomial f Q R).coeff j = hermiteContourCoeff f Q R j := by
  simp [hermiteContourPolynomial, coeff_monomial, hj]

theorem continuous_hermiteKernel_coeff (Q : ℂ[X]) (j : ℕ) :
    Continuous (fun ζ => (hermiteKernel Q ζ).coeff j) := by
  simp only [hermiteKernel_coeff]
  fun_prop

theorem continuous_hermiteKernel_eval (Q : ℂ[X]) (z : ℂ)
    (hd : 0 < Q.natDegree) : Continuous (fun ζ => (hermiteKernel Q ζ).eval z) := by
  have he : (fun ζ => (hermiteKernel Q ζ).eval z) =
      fun ζ => ∑ j ∈ Finset.range Q.natDegree, (hermiteKernel Q ζ).coeff j * z ^ j := by
    funext ζ
    exact eval_eq_sum_range' (hermiteKernel_natDegree_lt Q ζ hd le_rfl) z
  rw [he]
  exact continuous_finsetSum _ fun j _ => (continuous_hermiteKernel_coeff Q j).mul
    continuous_const

/-- Evaluation commutes with the finite family of coefficient integrals. -/
theorem hermiteContourPolynomial_eval {f : ℂ → ℂ} {Q : ℂ[X]} {R : ℝ}
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere (0 : ℂ) R))
    (hQ : ∀ ζ ∈ sphere (0 : ℂ) R, Q.eval ζ ≠ 0) (hd : 0 < Q.natDegree)
    (z : ℂ) :
    (hermiteContourPolynomial f Q R).eval z = cauchyNormalization *
      ∮ ζ in C(0, R), (hermiteKernel Q ζ).eval z * f ζ / Q.eval ζ := by
  have hi (j : ℕ) : CircleIntegrable
      (fun ζ => (hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ * z ^ j) 0 R :=
    ((((continuous_hermiteKernel_coeff Q j).continuousOn.mul hf).div
      Q.continuousOn hQ).mul continuousOn_const).circleIntegrable hR
  have hsum (ζ : ℂ) : (hermiteKernel Q ζ).eval z * f ζ / Q.eval ζ =
      ∑ j ∈ Finset.range Q.natDegree,
        (hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ * z ^ j := by
    rw [eval_eq_sum_range' (hermiteKernel_natDegree_lt Q ζ hd le_rfl) z,
      Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [hermiteContourPolynomial, eval_finsetSum, eval_monomial,
    hermiteContourCoeff]
  simp_rw [hsum]
  rw [circleIntegral.integral_fun_sum (fun j _ => hi j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (∮ ζ in C(0, R), (hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ * z ^ j) =
      (∮ ζ in C(0, R), (hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ) * z ^ j by
    exact circleIntegral.integral_smul_const _ _ _ _]
  ring

/-- Even boundary continuity suffices for analyticity of the remainder factor. -/
theorem hermiteContourQuotient_analyticOnNhd {f : ℂ → ℂ} {Q : ℂ[X]} {R : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (sphere (0 : ℂ) R))
    (hQ : ∀ ζ ∈ sphere (0 : ℂ) R, Q.eval ζ ≠ 0) :
    AnalyticOnNhd ℂ (hermiteContourQuotient f Q R) (ball (0 : ℂ) R) := by
  have hi : CircleIntegrable (fun ζ => f ζ / Q.eval ζ) 0 R :=
    (hf.div Q.continuousOn hQ).circleIntegrable hR.le
  have he : hermiteContourQuotient f Q R = fun z => cauchyNormalization *
      ∮ ζ in C(0, R), (ζ - z)⁻¹ • (f ζ / Q.eval ζ) := by
    funext z
    simp only [hermiteContourQuotient, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    congr 1
    congr 1
    funext ζ
    ring
  rw [he]
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro z hz
  have hzs : z ∉ sphere (0 : ℂ) |R| := by
    rw [abs_of_pos hR]
    intro hs
    exact (ne_of_lt (mem_ball.mp hz)) (mem_sphere.mp hs)
  exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul hi hzs).const_mul
    cauchyNormalization).differentiableAt.differentiableWithinAt

/-- The contour construction gives the exact Hermite remainder, including at
zeros of `Q`.  The analytic quotient removes the apparent singularities there. -/
theorem hermiteContour_remainder {f : ℂ → ℂ} {Q : ℂ[X]} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hQ : ∀ ζ ∈ sphere (0 : ℂ) R, Q.eval ζ ≠ 0) (hd : 0 < Q.natDegree)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    f z - (hermiteContourPolynomial f Q R).eval z =
      Q.eval z * hermiteContourQuotient f Q R z := by
  have hfc : ContinuousOn f (sphere (0 : ℂ) R) :=
    hf.continuousOn.mono sphere_subset_closedBall
  have hzs : z ∉ sphere (0 : ℂ) R := by
    intro hs
    exact (ne_of_lt (mem_ball.mp hz)) (mem_sphere.mp hs)
  have hnz (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) : ζ - z ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hzs)
  have hcauchy : cauchyNormalization * (∮ ζ in C(0, R), f ζ / (ζ - z)) = f z := by
    simpa only [cauchyNormalization, smul_eq_mul, div_eq_inv_mul] using
      Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        countable_empty hz hf.continuousOn
        (fun ζ hζ => (hf ζ (ball_subset_closedBall hζ.1)).differentiableAt)
  have hi₁ : CircleIntegrable (fun ζ => f ζ / (ζ - z)) 0 R :=
    (hfc.div (continuousOn_id.sub continuousOn_const) hnz).circleIntegrable hR.le
  have hi₂ : CircleIntegrable
      (fun ζ => (hermiteKernel Q ζ).eval z * f ζ / Q.eval ζ) 0 R :=
    (((continuous_hermiteKernel_eval Q z hd).continuousOn.mul hfc).div
      Q.continuousOn hQ).circleIntegrable hR.le
  have hid : (∮ ζ in C(0, R), f ζ / (ζ - z)) -
      (∮ ζ in C(0, R), (hermiteKernel Q ζ).eval z * f ζ / Q.eval ζ) =
      Q.eval z * (∮ ζ in C(0, R), f ζ / (Q.eval ζ * (ζ - z))) := by
    calc
      _ = ∮ ζ in C(0, R), f ζ / (ζ - z) -
          (hermiteKernel Q ζ).eval z * f ζ / Q.eval ζ :=
        (circleIntegral.integral_sub hi₁ hi₂).symm
      _ = ∮ ζ in C(0, R), Q.eval z * (f ζ / (Q.eval ζ * (ζ - z))) := by
        apply circleIntegral.integral_congr hR.le
        intro ζ hζ
        dsimp only
        rw [hermiteKernel_eval_of_ne Q (ne_of_mem_of_not_mem hζ hzs).symm]
        field_simp [hQ ζ hζ, hnz ζ hζ]
        ring
      _ = _ := circleIntegral.integral_const_mul _ _ _ _
  calc
    f z - (hermiteContourPolynomial f Q R).eval z = cauchyNormalization *
        ((∮ ζ in C(0, R), f ζ / (ζ - z)) -
          (∮ ζ in C(0, R), (hermiteKernel Q ζ).eval z * f ζ / Q.eval ζ)) := by
      rw [hermiteContourPolynomial_eval hR.le hfc hQ hd z, ← hcauchy]
      ring
    _ = Q.eval z * hermiteContourQuotient f Q R z := by
      rw [hid]
      dsimp only [hermiteContourQuotient]
      ring

/-- A polynomial of degree less than `Q`, and an analytic remainder divisible
by `Q`, are obtained with explicit contour-integral formulas. -/
theorem exists_hermiteContour_factorization {f : ℂ → ℂ} {Q : ℂ[X]} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hQ : ∀ ζ ∈ sphere (0 : ℂ) R, Q.eval ζ ≠ 0) (hd : 0 < Q.natDegree) :
    ∃ P : ℂ[X], ∃ H : ℂ → ℂ, P.degree < (Q.natDegree : WithBot ℕ) ∧
      AnalyticOnNhd ℂ H (ball (0 : ℂ) R) ∧
      ∀ z ∈ ball (0 : ℂ) R, f z - P.eval z = Q.eval z * H z := by
  exact ⟨hermiteContourPolynomial f Q R, hermiteContourQuotient f Q R,
    hermiteContourPolynomial_degree_lt f Q R,
    hermiteContourQuotient_analyticOnNhd hR
      (hf.continuousOn.mono sphere_subset_closedBall) hQ,
    fun _ hz => hermiteContour_remainder hR hf hQ hd hz⟩

end AbelFormalization
