import AbelFormalization.HermiteContour
import AbelFormalization.HermiteBounds

/-! # Uniform bounds for contour interpolation coefficients

A uniform bound on the coefficient kernel and a bound on the boundary values
of the interpolated function control every coefficient.  Multiplication by
the total-degree factorial gives the same conclusion for the manuscript's
factorial-normalized coefficients, uniformly at colliding nodes.
-/

noncomputable section

open Set Metric Polynomial

namespace AbelFormalization

/-- The coefficient bound follows directly from the normalized contour norm
estimate.  No regularity assumptions beyond the displayed boundary bounds
are needed for this inequality. -/
theorem norm_hermiteContourCoeff_le {f : ℂ → ℂ} {Q : ℂ[X]} {R C S : ℝ} {j : ℕ}
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hkernel : ∀ ζ ∈ sphere (0 : ℂ) R,
      ‖(hermiteKernel Q ζ).coeff j / Q.eval ζ‖ ≤ C)
    (hf : ∀ ζ ∈ sphere (0 : ℂ) R, ‖f ζ‖ ≤ S) :
    ‖hermiteContourCoeff f Q R j‖ ≤ R * C * S := by
  have hb : ∀ ζ ∈ sphere (0 : ℂ) R,
      ‖(hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ‖ ≤ C * S := by
    intro ζ hζ
    rw [show (hermiteKernel Q ζ).coeff j * f ζ / Q.eval ζ =
      ((hermiteKernel Q ζ).coeff j / Q.eval ζ) * f ζ by ring, norm_mul]
    exact mul_le_mul (hkernel ζ hζ) (hf ζ hζ) (norm_nonneg _) hC
  simpa only [hermiteContourCoeff, cauchyNormalization, smul_eq_mul, mul_assoc] using
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR hb

variable {ι : Type*} [Fintype ι]

/-- One positive constant depending only on the node-radius bound and the
multiplicities bounds both ordinary and normalized coefficients by the
boundary norm bound.  The same constant works for all allowed node tuples. -/
theorem exists_uniform_hermiteContour_coeff_bounds (B : ℝ) (m : ι → ℕ) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ (δ : ι → ℂ) (f : ℂ → ℂ) (S : ℝ),
      (∀ i, ‖δ i‖ ≤ B + 1 / 4) → 0 ≤ S →
      (∀ ζ : ℂ, ‖ζ‖ = B + 1 → ‖f ζ‖ ≤ S) →
      ∀ j : ℕ, j < totalMultiplicity m →
        ‖(hermiteContourPolynomial f (nodePolynomial δ m) (B + 1)).coeff j‖ ≤ D * S ∧
        ‖(j.factorial : ℂ) *
          (hermiteContourPolynomial f (nodePolynomial δ m) (B + 1)).coeff j‖ ≤ D * S := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_hermiteCoefficientKernel_bound B m
  let D₀ : ℝ := (B + 1) * C
  let D : ℝ := ((totalMultiplicity m).factorial : ℝ) * D₀
  have hD₀ : 0 < D₀ := mul_pos (by linarith) hC
  have hfact₁ : (1 : ℝ) ≤ ((totalMultiplicity m).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (totalMultiplicity m))
  have hD₀D : D₀ ≤ D := by
    exact (one_mul D₀).symm.le.trans
      (mul_le_mul_of_nonneg_right hfact₁ hD₀.le)
  refine ⟨D, hD₀.trans_le hD₀D, ?_⟩
  intro δ f S hδ hS hf j hj
  have hjQ : j < (nodePolynomial δ m).natDegree := by
    simpa only [nodePolynomial_natDegree] using hj
  have hb : ‖(hermiteContourPolynomial f (nodePolynomial δ m) (B + 1)).coeff j‖ ≤
      D₀ * S := by
    rw [hermiteContourPolynomial_coeff f (nodePolynomial δ m) (B + 1) hjQ]
    apply norm_hermiteContourCoeff_le (by linarith) hC.le
    · intro ζ hζ
      exact hkernel δ ζ hδ (by simpa only [mem_sphere, dist_zero_right] using hζ) j hj
    · intro ζ hζ
      exact hf ζ (by simpa only [mem_sphere, dist_zero_right] using hζ)
  refine ⟨hb.trans (mul_le_mul_of_nonneg_right hD₀D hS), ?_⟩
  have hfact : (j.factorial : ℝ) ≤ ((totalMultiplicity m).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj.le
  rw [norm_mul, Complex.norm_natCast]
  calc
    (j.factorial : ℝ) *
        ‖(hermiteContourPolynomial f (nodePolynomial δ m) (B + 1)).coeff j‖ ≤
        ((totalMultiplicity m).factorial : ℝ) * (D₀ * S) :=
      mul_le_mul hfact hb (norm_nonneg _) (by positivity)
    _ = D * S := by dsimp only [D]; ring

end AbelFormalization
