import AbelFormalization.WilkieVerticalMinorDerivativeBridge

/-!
# Wilkie 2.9 at zero visible arity

At zero visible arity, the vertical columns are all the source columns.
The finite-index cast below makes that fact explicit, so surjectivity of the
derivative makes the vertical square Jacobian invertible.
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
  classical
  let A : Matrix (Fin k) (Fin (0 + k)) ℝ :=
    standardRectangularJacobian F x
  have hcolsSurj :
      Function.Surjective (Fin.natAddEmb 0 : Fin k → Fin (0 + k)) := by
    intro j
    refine ⟨Fin.cast (Nat.zero_add k) j, ?_⟩
    apply Fin.ext
    simp [Fin.natAddEmb_apply, Fin.natAdd]
  let e : Fin k ≃ Fin (0 + k) :=
    Equiv.ofBijective (Fin.natAddEmb 0 : Fin k → Fin (0 + k))
      ⟨(Fin.natAddEmb 0).injective, hcolsSurj⟩
  have he (i : Fin k) : e i = (Fin.natAddEmb 0) i := by
    rfl
  let B : Matrix (Fin k) (Fin k) ℝ := A.submatrix id e
  have hBsurj : Function.Surjective B.mulVec := by
    intro y
    obtain ⟨v, hv⟩ := hregular y
    refine ⟨v ∘ e, ?_⟩
    have hreindex : (v ∘ e) ∘ e.symm = v := by
      funext j
      simp
    calc
      B.mulVec (v ∘ e) = A.mulVec v := by
        simpa only [B, hreindex, Function.comp_id] using
          Matrix.submatrix_mulVec_equiv A (v ∘ e) id e
      _ = fderiv ℝ F x v := (fderiv_eq_standardRectangularJacobian_mulVec hFdiff v).symm
      _ = y := hv
  have hBunit : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hBsurj
  have hBdet : B.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B).mp hBunit).ne_zero
  have hminor : standardJacobianColumnMinor F (Fin.natAddEmb 0) x = B.det := by
    change (A.submatrix id (Fin.natAddEmb 0)).det = B.det
    have hfun : (e : Fin k → Fin (0 + k)) =
        (Fin.natAddEmb 0 : Fin k → Fin (0 + k)) := funext he
    rw [← hfun]
  rw [hminor]
  exact hBdet

end AbelFormalization
