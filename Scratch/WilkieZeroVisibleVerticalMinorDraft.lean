import AbelFormalization.WilkieVerticalMinorDerivativeBridge

/-!
# Wilkie 2.9 at zero visible arity

When the visible block has arity zero, the regular fiber map is square.
Surjectivity of its derivative makes the one vertical maximal minor nonzero.
This supplies the terminal regular-minor seed for the Case 2 descent; it
does not by itself transport a seed back through fixed-coordinate slices.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- At zero visible arity, regularity makes the vertical Jacobian minor
nonzero. -/
theorem wilkieZeroVisible_verticalMinor_ne_zero_of_regular
    {k : ℕ} {F : RealEuclidean (0 + k) → RealEuclidean k}
    {x : RealEuclidean (0 + k)}
    (hFdiff : DifferentiableAt ℝ F x)
    (hregular : Function.Surjective (fderiv ℝ F x)) :
    standardJacobianColumnMinor F (Fin.natAddEmb 0) x ≠ 0 := by
  rw [Nat.zero_add k] at F x hFdiff hregular ⊢
  let A : Matrix (Fin k) (Fin k) ℝ := standardRectangularJacobian F x
  have hA_surj : Function.Surjective A.mulVec := by
    intro y
    obtain ⟨v, hv⟩ := hregular y
    refine ⟨v, ?_⟩
    rw [fderiv_eq_standardRectangularJacobian_mulVec hFdiff] at hv
    exact hv
  have hA_unit : IsUnit A :=
    Matrix.mulVec_surjective_iff_isUnit.mp hA_surj
  have hA_det_ne : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp hA_unit).ne_zero
  have hminor_eq :
      standardJacobianColumnMinor F (Fin.natAddEmb 0) x = A.det := by
    simp [standardJacobianColumnMinor, A, Matrix.submatrix,
      Fin.natAddEmb, Fin.natAdd]
  rw [hminor_eq]
  exact hA_det_ne

end AbelFormalization
