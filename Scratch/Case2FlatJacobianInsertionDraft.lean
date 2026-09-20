import AbelFormalization.WilkieCase2MinorTransport

/-!
# Flat Jacobian of a coordinate slice

This source-only draft discharges the `hJac` interface in
`wilkieCase2_sliceMinor_squared_interval_transport` when the slice fixes one
source coordinate and keeps the remaining coordinates in order.  The only
analytic premise is differentiability of the original map at the inserted
point.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Insert a zero at `fixed`.  This is the linear part of the affine
coordinate insertion `wilkieCase2_coordinateInsert fixed b`. -/
def wilkieCase2_coordinateInsertLinear {a : ℕ}
    (fixed : Fin (a + 1)) :
    RealEuclidean a →L[ℝ] RealEuclidean (a + 1) :=
  ContinuousLinearMap.pi
    (Fin.insertNth fixed
      (0 : RealEuclidean a →L[ℝ] ℝ)
      (fun j : Fin a ↦ ContinuousLinearMap.proj j))

theorem wilkieCase2_coordinateInsertLinear_fixed {a : ℕ}
    (fixed : Fin (a + 1)) (v : RealEuclidean a) :
    wilkieCase2_coordinateInsertLinear fixed v fixed = 0 := by
  simp [wilkieCase2_coordinateInsertLinear]

theorem wilkieCase2_coordinateInsertLinear_free {a : ℕ}
    (fixed : Fin (a + 1)) (v : RealEuclidean a) (j : Fin a) :
    wilkieCase2_coordinateInsertLinear fixed v (fixed.succAbove j) = v j := by
  simp [wilkieCase2_coordinateInsertLinear]

/-- The derivative of the affine insertion is zero insertion, at every
point and for every inserted value. -/
theorem wilkieCase2_coordinateInsert_hasFDerivAt {a : ℕ}
    (fixed : Fin (a + 1)) (b : ℝ) (x : RealEuclidean a) :
    HasFDerivAt (wilkieCase2_coordinateInsert fixed b)
      (wilkieCase2_coordinateInsertLinear fixed) x := by
  unfold wilkieCase2_coordinateInsert wilkieCase2_coordinateInsertLinear
  rw [hasFDerivAt_pi]
  intro i
  rcases Fin.eq_self_or_eq_succAbove fixed i with rfl | ⟨j, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using
      (hasFDerivAt_const b x :
        HasFDerivAt (fun _ : RealEuclidean a ↦ b)
          (0 : RealEuclidean a →L[ℝ] ℝ) x)
  · simpa only [Fin.insertNth_apply_succAbove] using
      (hasFDerivAt_apply (𝕜 := ℝ) j x)

/-- Zero insertion sends a standard source basis vector to the standard
basis vector at its corresponding free coordinate. -/
theorem wilkieCase2_coordinateInsertLinear_basis {a : ℕ}
    (fixed : Fin (a + 1)) (j : Fin a) :
    wilkieCase2_coordinateInsertLinear fixed
      ((Pi.basisFun ℝ (Fin a)) j) =
        (Pi.basisFun ℝ (Fin (a + 1))) (fixed.succAbove j) := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove fixed i with rfl | ⟨t, rfl⟩
  · simp [wilkieCase2_coordinateInsertLinear_fixed, Pi.basisFun_apply,
      Fin.ne_succAbove]
  · simp [wilkieCase2_coordinateInsertLinear_free, Pi.basisFun_apply,
      Pi.single_apply, Fin.succAbove_right_inj]

/-- The Jacobian of `F` after fixing one source coordinate consists of the
columns of the original Jacobian indexed by `Fin.succAboveEmb fixed`.
The output rows retain their original order. -/
theorem wilkieCase2_flatJacobian_coordinateInsert
    {a k : ℕ}
    (F : RealEuclidean (a + 1) → RealEuclidean k)
    (fixed : Fin (a + 1)) (b : ℝ) (x : RealEuclidean a)
    (hF : DifferentiableAt ℝ F
      (wilkieCase2_coordinateInsert fixed b x)) :
    standardRectangularJacobian
      (fun y ↦ F (wilkieCase2_coordinateInsert fixed b y)) x =
        (standardRectangularJacobian F
          (wilkieCase2_coordinateInsert fixed b x)).submatrix
          (Equiv.refl (Fin k)) (Fin.succAboveEmb fixed) := by
  ext i j
  have hFi : DifferentiableAt ℝ (fun z ↦ F z i)
      (wilkieCase2_coordinateInsert fixed b x) :=
    (differentiableAt_pi.mp hF) i
  have hchain :
      HasFDerivAt
        (fun y ↦ F (wilkieCase2_coordinateInsert fixed b y) i)
        ((fderiv ℝ (fun z ↦ F z i)
          (wilkieCase2_coordinateInsert fixed b x)).comp
          (wilkieCase2_coordinateInsertLinear fixed)) x := by
    simpa only [Function.comp_def] using
      (hFi.hasFDerivAt.comp x
        (wilkieCase2_coordinateInsert_hasFDerivAt fixed b x))
  have hscalar := hchain.fderiv
  change fderiv ℝ
      (fun y ↦ F (wilkieCase2_coordinateInsert fixed b y) i) x
        ((Pi.basisFun ℝ (Fin a)) j) =
    fderiv ℝ (fun z ↦ F z i)
      (wilkieCase2_coordinateInsert fixed b x)
        ((Pi.basisFun ℝ (Fin (a + 1))) (fixed.succAbove j))
  rw [hscalar]
  change fderiv ℝ (fun z ↦ F z i)
      (wilkieCase2_coordinateInsert fixed b x)
      (wilkieCase2_coordinateInsertLinear fixed
        ((Pi.basisFun ℝ (Fin a)) j)) = _
  rw [wilkieCase2_coordinateInsertLinear_basis]

/-- Set-level form of the exact `hJac` premise used by the minor transport
theorem. -/
theorem wilkieCase2_flatJacobian_coordinateInsert_on
    {a k : ℕ}
    (F : RealEuclidean (a + 1) → RealEuclidean k)
    (fixed : Fin (a + 1)) (b : ℝ)
    {S : Set (RealEuclidean a)}
    (hF : ∀ x ∈ S, DifferentiableAt ℝ F
      (wilkieCase2_coordinateInsert fixed b x)) :
    ∀ x ∈ S,
      standardRectangularJacobian
        (fun y ↦ F (wilkieCase2_coordinateInsert fixed b y)) x =
          (standardRectangularJacobian F
            (wilkieCase2_coordinateInsert fixed b x)).submatrix
            (Equiv.refl (Fin k)) (Fin.succAboveEmb fixed) := by
  intro x hx
  exact wilkieCase2_flatJacobian_coordinateInsert F fixed b x (hF x hx)

end AbelFormalization
