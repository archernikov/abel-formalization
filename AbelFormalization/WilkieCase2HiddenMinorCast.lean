import AbelFormalization.WilkieCase2ProductFlatEquiv
import AbelFormalization.WilkieZeroVisibleVerticalMinor

/-!
# Case 2 hidden-column minor through the visible-coordinate Nat cast

The inserted visible column is omitted by the slice derivative.  Each hidden
column has the same position among the hidden columns before and after the
cast `(m + q) + 1 = (m + 1) + q`, so the two ordered square minors agree
exactly.  The squared identity used by the Case 2 inductive invariant is an
immediate corollary.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Relabel `(m + q) + 1` coordinates as `(m + 1) + q` coordinates. -/
private def case2HiddenArityCastLinear (m q : ℕ) :
    RealEuclidean ((m + q) + 1) →L[ℝ]
      RealEuclidean ((m + 1) + q) :=
  ContinuousLinearMap.pi
    (fun r ↦ ContinuousLinearMap.proj
      (r.cast (wilkieCase2_add_succ_cast m q).symm))

private theorem case2HiddenArityCastLinear_basis (m q : ℕ)
    (j : Fin ((m + q) + 1)) :
    case2HiddenArityCastLinear m q
      ((Pi.basisFun ℝ (Fin ((m + q) + 1))) j) =
        (Pi.basisFun ℝ (Fin ((m + 1) + q)))
          (j.cast (wilkieCase2_add_succ_cast m q)) := by
  ext r
  have heq :
      r.cast (wilkieCase2_add_succ_cast m q).symm = j ↔
        r = j.cast (wilkieCase2_add_succ_cast m q) := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [Fin.val_cast] using congrArg Fin.val h
    · intro h
      subst r
      apply Fin.ext
      simp only [Fin.val_cast]
  simp [case2HiddenArityCastLinear, Pi.basisFun_apply,
    Pi.single_apply, heq]

/-- The linear part of `wilkieCase2FlatCastInsert`. -/
private def case2HiddenCastInsertLinear {m q : ℕ}
    (i : Fin (m + 1)) :
    RealEuclidean (m + q) →L[ℝ]
      RealEuclidean ((m + 1) + q) :=
  (case2HiddenArityCastLinear m q).comp
    (wilkieCase2_coordinateInsertLinear
      (wilkieCase2FlatFixedIndex (q := q) i))

private theorem case2HiddenCastInsert_hasFDerivAt {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (y : RealEuclidean (m + q)) :
    HasFDerivAt (wilkieCase2FlatCastInsert i b)
      (case2HiddenCastInsertLinear (q := q) i) y := by
  change HasFDerivAt
    (fun v ↦ case2HiddenArityCastLinear m q
      (wilkieCase2_coordinateInsert
        (wilkieCase2FlatFixedIndex (q := q) i) b v))
    (case2HiddenCastInsertLinear (q := q) i) y
  exact (case2HiddenArityCastLinear m q).hasFDerivAt.comp y
    (wilkieCase2_coordinateInsert_hasFDerivAt
      (wilkieCase2FlatFixedIndex (q := q) i) b y)

/-- A lower-arity hidden basis vector becomes the corresponding original
hidden basis vector under the derivative of the casted insertion. -/
private theorem case2HiddenCastInsertLinear_basis_hidden {m q : ℕ}
    (i : Fin (m + 1)) (j : Fin q) :
    case2HiddenCastInsertLinear (q := q) i
      ((Pi.basisFun ℝ (Fin (m + q))) (Fin.natAdd m j)) =
        (Pi.basisFun ℝ (Fin ((m + 1) + q)))
          (Fin.natAdd (m + 1) j) := by
  let fixed := wilkieCase2FlatFixedIndex (q := q) i
  have hindex :
      (fixed.succAbove (Fin.natAdd m j)).cast
          (wilkieCase2_add_succ_cast m q) =
        Fin.natAdd (m + 1) j := by
    change
      ((wilkieCase2FlatFixedIndex (q := q) i).succAbove
        (Fin.natAdd m j)).cast
          (wilkieCase2_add_succ_cast m q) =
        Fin.natAdd (m + 1) j
    rw [wilkieCase2FlatFixedIndex_free_hidden]
    apply Fin.ext
    simp only [Fin.val_cast]
  change case2HiddenArityCastLinear m q
    (wilkieCase2_coordinateInsertLinear fixed
      ((Pi.basisFun ℝ (Fin (m + q))) (Fin.natAdd m j))) = _
  rw [wilkieCase2_coordinateInsertLinear_basis,
    case2HiddenArityCastLinear_basis, hindex]

/-- Each hidden entry of the sliced Jacobian equals the corresponding entry
of the original Jacobian at the inserted point. -/
private theorem case2HiddenCastInsert_jacobian_hidden {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ) (y : RealEuclidean (m + q))
    (hFdiff : DifferentiableAt ℝ F
      (wilkieCase2FlatCastInsert i b y))
    (r j : Fin q) :
    standardRectangularJacobian
      (F ∘ wilkieCase2FlatCastInsert i b) y r
        (Fin.natAdd m j) =
      standardRectangularJacobian F
        (wilkieCase2FlatCastInsert i b y) r
          (Fin.natAdd (m + 1) j) := by
  have hFr : DifferentiableAt ℝ (fun z ↦ F z r)
      (wilkieCase2FlatCastInsert i b y) :=
    (differentiableAt_pi.mp hFdiff) r
  have hchain :
      HasFDerivAt
        (fun v ↦ F (wilkieCase2FlatCastInsert i b v) r)
        ((fderiv ℝ (fun z ↦ F z r)
          (wilkieCase2FlatCastInsert i b y)).comp
          (case2HiddenCastInsertLinear (q := q) i)) y := by
    simpa only [Function.comp_def] using
      (hFr.hasFDerivAt.comp y
        (case2HiddenCastInsert_hasFDerivAt i b y))
  have hscalar := hchain.fderiv
  change fderiv ℝ
      (fun v ↦ F (wilkieCase2FlatCastInsert i b v) r) y
        ((Pi.basisFun ℝ (Fin (m + q))) (Fin.natAdd m j)) =
    fderiv ℝ (fun z ↦ F z r)
      (wilkieCase2FlatCastInsert i b y)
        ((Pi.basisFun ℝ (Fin ((m + 1) + q)))
          (Fin.natAdd (m + 1) j))
  rw [hscalar]
  change fderiv ℝ (fun z ↦ F z r)
      (wilkieCase2FlatCastInsert i b y)
      (case2HiddenCastInsertLinear (q := q) i
        ((Pi.basisFun ℝ (Fin (m + q))) (Fin.natAdd m j))) = _
  rw [case2HiddenCastInsertLinear_basis_hidden]

/-- The original and sliced ordered hidden-column minors agree pointwise.
The only analytic premise is differentiability of the original map at the
inserted point. -/
theorem wilkieCase2_flatVerticalMinor_insert
    {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ) (y : RealEuclidean (m + q))
    (hFdiff : DifferentiableAt ℝ F
      (wilkieCase2FlatCastInsert i b y)) :
    standardJacobianColumnMinor
      (F ∘ wilkieCase2FlatCastInsert i b)
      (Fin.natAddEmb m) y =
    standardJacobianColumnMinor F (Fin.natAddEmb (m + 1))
      (wilkieCase2FlatCastInsert i b y) := by
  have hmatrix :
      (standardRectangularJacobian
        (F ∘ wilkieCase2FlatCastInsert i b) y).submatrix
          id (Fin.natAddEmb m) =
      (standardRectangularJacobian F
        (wilkieCase2FlatCastInsert i b y)).submatrix
          id (Fin.natAddEmb (m + 1)) := by
    ext r j
    exact case2HiddenCastInsert_jacobian_hidden
      F i b y hFdiff r j
  change
    ((standardRectangularJacobian
      (F ∘ wilkieCase2FlatCastInsert i b) y).submatrix
        id (Fin.natAddEmb m)).det =
    ((standardRectangularJacobian F
      (wilkieCase2FlatCastInsert i b y)).submatrix
        id (Fin.natAddEmb (m + 1))).det
  rw [hmatrix]

/-- The fixed hidden-column certificate required by the Case 2 descent. -/
theorem wilkieCase2_flatVerticalMinor_sq_insert
    {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ) (y : RealEuclidean (m + q))
    (hFdiff : DifferentiableAt ℝ F
      (wilkieCase2FlatCastInsert i b y)) :
    (standardJacobianColumnMinor
      (F ∘ wilkieCase2FlatCastInsert i b)
      (Fin.natAddEmb m) y) ^ 2 =
    (standardJacobianColumnMinor F (Fin.natAddEmb (m + 1))
      (wilkieCase2FlatCastInsert i b y)) ^ 2 := by
  rw [wilkieCase2_flatVerticalMinor_insert F i b y hFdiff]

/-- Pointwise nonzeroness of the lower hidden-column certificate lifts to
the original arity at the inserted point. -/
theorem wilkieCase2_flatVerticalMinor_ne_zero_insert
    {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ) (y : RealEuclidean (m + q))
    (hFdiff : DifferentiableAt ℝ F
      (wilkieCase2FlatCastInsert i b y))
    (hminor : standardJacobianColumnMinor
      (F ∘ wilkieCase2FlatCastInsert i b)
      (Fin.natAddEmb m) y ≠ 0) :
    standardJacobianColumnMinor F (Fin.natAddEmb (m + 1))
      (wilkieCase2FlatCastInsert i b y) ≠ 0 := by
  rw [← wilkieCase2_flatVerticalMinor_insert F i b y hFdiff]
  exact hminor

end AbelFormalization
