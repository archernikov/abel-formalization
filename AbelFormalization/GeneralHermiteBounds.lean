import AbelFormalization.HermiteCoefficientBounds
import AbelFormalization.NormalizedPolynomial

/-! # Hermite coefficient bounds for arbitrary separated radii

The contour radius may be any positive `R`; the nodes may lie in any closed
disk of radius `b < R`.  The gap `R-b` keeps the node polynomial nonzero on
the contour, and compactness gives coefficient bounds uniform in all nodes.
-/

noncomputable section

open Set Metric Polynomial

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/-- Closed node polydisk and contour circle, with independent radii. -/
def generalHermiteContourParameters (b R : ℝ) : Set ((ι → ℂ) × ℂ) :=
  {p | (∀ i, ‖p.1 i‖ ≤ b) ∧ ‖p.2‖ = R}

omit [Fintype ι] in
theorem isCompact_generalHermiteContourParameters (b R : ℝ) :
    IsCompact (generalHermiteContourParameters (ι := ι) b R) := by
  have hn : IsCompact {δ : ι → ℂ | ∀ i, δ i ∈ closedBall 0 b} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall 0 b
  have hn' : IsCompact {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ b} := by
    simpa only [mem_closedBall, dist_zero_right] using hn
  have hs : IsCompact {ζ : ℂ | ‖ζ‖ = R} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) R
  exact hn'.prod hs

/-- The positive radial gap bounds the denominator away from zero, also when
some of the nodes coincide. -/
theorem nodePolynomial_ne_zero_of_radius_gap (m : ι → ℕ) {δ : ι → ℂ}
    {b R : ℝ} (hb : b < R) (hδ : ∀ i, ‖δ i‖ ≤ b) {ζ : ℂ} (hζ : ‖ζ‖ = R) :
    (nodePolynomial δ m).eval ζ ≠ 0 := by
  have hgap : 0 < R - b := sub_pos.mpr hb
  have hbound := nodePolynomial_radius_gap_bound m hgap.le hδ
    (show b + (R - b) ≤ ‖ζ‖ by linarith)
  exact norm_pos_iff.mp ((pow_pos hgap _).trans_le hbound)

theorem continuousOn_generalHermiteCoefficientKernel (m : ι → ℕ)
    {b R : ℝ} (hb : b < R) (j : ℕ) :
    ContinuousOn (fun p : (ι → ℂ) × ℂ => hermiteCoefficientKernel p.1 m p.2 j)
      (generalHermiteContourParameters b R) := by
  intro p hp
  exact (continuousAt_hermiteCoefficientKernel m j p
    (nodePolynomial_ne_zero_of_radius_gap m hb hp.1 hp.2)).continuousWithinAt

/-- One positive kernel bound works for every coefficient and all nodes in
the smaller closed disk, for any fixed separated radii. -/
theorem exists_uniform_hermiteCoefficientKernel_bound_of_radius_gap (m : ι → ℕ)
    {b R : ℝ} (hb : b < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ι → ℂ) (ζ : ℂ),
      (∀ i, ‖δ i‖ ≤ b) → ‖ζ‖ = R →
      ∀ j : ℕ, j < totalMultiplicity m → ‖hermiteCoefficientKernel δ m ζ j‖ ≤ C := by
  let F : ((ι → ℂ) × ℂ) → Fin (totalMultiplicity m) → ℂ :=
    fun p j => hermiteCoefficientKernel p.1 m p.2 j
  have hF : ContinuousOn F (generalHermiteContourParameters b R) :=
    continuousOn_pi.mpr fun j => continuousOn_generalHermiteCoefficientKernel m hb j
  obtain ⟨C, hC⟩ :=
    (isCompact_generalHermiteContourParameters b R).exists_bound_of_continuousOn hF
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro δ ζ hδ hζ j hj
  have hp : (δ, ζ) ∈ generalHermiteContourParameters b R := ⟨hδ, hζ⟩
  exact ((norm_le_pi_norm (F (δ, ζ)) ⟨j, hj⟩).trans (hC (δ, ζ) hp)).trans
    (le_max_left C 1)

/-- For arbitrary contour and node radii `0 < R` and `b < R`, one positive
constant bounds every factorial-normalized interpolation coefficient by the
boundary norm bound. No distinctness or positive multiplicity assumptions
are needed for this bound. -/
theorem exists_uniform_normalizedHermiteCoeff_bound (m : ι → ℕ)
    {b R : ℝ} (hR : 0 < R) (hb : b < R) :
    ∃ D : ℝ, 0 < D ∧ ∀ (δ : ι → ℂ) (f : ℂ → ℂ) (S : ℝ),
      (∀ i, ‖δ i‖ ≤ b) → 0 ≤ S →
      (∀ ζ : ℂ, ‖ζ‖ = R → ‖f ζ‖ ≤ S) →
      ∀ j : ℕ, j < totalMultiplicity m →
        ‖normalizedCoeff (hermiteContourPolynomial f (nodePolynomial δ m) R) j‖ ≤ D * S := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_hermiteCoefficientKernel_bound_of_radius_gap m hb
  let D : ℝ := ((totalMultiplicity m).factorial : ℝ) * (R * C)
  have hfactpos : (0 : ℝ) < ((totalMultiplicity m).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (totalMultiplicity m)
  refine ⟨D, mul_pos hfactpos (mul_pos hR hC), ?_⟩
  intro δ f S hδ hS hf j hj
  have hjQ : j < (nodePolynomial δ m).natDegree := by
    simpa only [nodePolynomial_natDegree] using hj
  have hcoeff : ‖(hermiteContourPolynomial f (nodePolynomial δ m) R).coeff j‖ ≤ R * C * S := by
    rw [hermiteContourPolynomial_coeff f (nodePolynomial δ m) R hjQ]
    apply norm_hermiteContourCoeff_le hR.le hC.le
    · intro ζ hζ
      exact hkernel δ ζ hδ (by simpa only [mem_sphere, dist_zero_right] using hζ) j hj
    · intro ζ hζ
      exact hf ζ (by simpa only [mem_sphere, dist_zero_right] using hζ)
  have hfact : (j.factorial : ℝ) ≤ ((totalMultiplicity m).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj.le
  rw [normalizedCoeff, norm_mul, Complex.norm_natCast]
  calc
    (j.factorial : ℝ) * ‖(hermiteContourPolynomial f (nodePolynomial δ m) R).coeff j‖ ≤
        (j.factorial : ℝ) * (R * C * S) :=
      mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ ≤ ((totalMultiplicity m).factorial : ℝ) * (R * C * S) :=
      mul_le_mul_of_nonneg_right hfact (mul_nonneg (mul_nonneg hR.le hC.le) hS)
    _ = D * S := by dsimp only [D]; ring

end AbelFormalization
