import AbelFormalization.WilkieCase2ProductFlatEquiv
import AbelFormalization.WilkieVerticalMinorProjectionFork

/-!
# Case 2: a selected minor interval over a visible cylinder

The lower visible set is the literal preimage of `U` under `Fin.insertNth`.
The lower flat fiber and the original fiber are both `wilkieFiberOver` sets.
The only derivative hypothesis is differentiability of `F` on the original
restricted fiber.  The cast bridge below accounts for the equality
`(m + q) + 1 = (m + 1) + q` in the flat Jacobian columns.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The visible cylinder left after fixing visible coordinate `i` to `b`. -/
def wilkieCase2VisibleCylinderSlice {m : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (U : Set (RealEuclidean (m + 1))) : Set (RealEuclidean m) :=
  (wilkieCase2_coordinateInsert i b) ⁻¹' U

theorem wilkieCase2VisibleCylinderSlice_isOpen {m : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    {U : Set (RealEuclidean (m + 1))} (hU : IsOpen U) :
    IsOpen (wilkieCase2VisibleCylinderSlice i b U) := by
  have hcontinuous : Continuous (wilkieCase2_coordinateInsert i b) :=
    continuous_iff_continuousAt.mpr
      (fun x ↦ (wilkieCase2_coordinateInsert_hasFDerivAt i b x).continuousAt)
  exact hU.preimage hcontinuous

/-- Cast the generic flat insertion target into visible-first arity.  This
is the linear map behind `wilkieCase2FlatCastInsert`. -/
def wilkieCase2FlatArityCastLinear (m q : ℕ) :
    RealEuclidean ((m + q) + 1) →L[ℝ]
      RealEuclidean ((m + 1) + q) :=
  ContinuousLinearMap.pi
    (fun r ↦ ContinuousLinearMap.proj
      (r.cast (wilkieCase2_add_succ_cast m q).symm))

/-- The column permutation induced by the arity cast. -/
def wilkieCase2FlatArityCastColumns (m q : ℕ) :
    Fin ((m + q) + 1) ↪ Fin ((m + 1) + q) where
  toFun j := j.cast (wilkieCase2_add_succ_cast m q)
  inj' := by
    intro j t hjt
    apply Fin.ext
    simpa only [Fin.val_cast] using congrArg Fin.val hjt

theorem wilkieCase2FlatArityCastLinear_basis (m q : ℕ)
    (j : Fin ((m + q) + 1)) :
    wilkieCase2FlatArityCastLinear m q
        ((Pi.basisFun ℝ (Fin ((m + q) + 1))) j) =
      (Pi.basisFun ℝ (Fin ((m + 1) + q)))
        (wilkieCase2FlatArityCastColumns m q j) := by
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
  simp [wilkieCase2FlatArityCastLinear,
    wilkieCase2FlatArityCastColumns, Pi.basisFun_apply,
    Pi.single_apply, heq]
  rfl

/-- A cast of finite coordinate arity only relabels Jacobian columns. -/
theorem wilkieCase2_flatJacobian_arityCast {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (z : RealEuclidean ((m + q) + 1))
    (hF : DifferentiableAt ℝ F
      (wilkieCase2FlatArityCastLinear m q z)) :
    standardRectangularJacobian
        (fun v ↦ F (wilkieCase2FlatArityCastLinear m q v)) z =
      (standardRectangularJacobian F
        (wilkieCase2FlatArityCastLinear m q z)).submatrix
          (Equiv.refl (Fin q))
          (wilkieCase2FlatArityCastColumns m q) := by
  ext r j
  have hFr : DifferentiableAt ℝ (fun w ↦ F w r)
      (wilkieCase2FlatArityCastLinear m q z) :=
    (differentiableAt_pi.mp hF) r
  have hchain :
      HasFDerivAt
        (fun v ↦ F (wilkieCase2FlatArityCastLinear m q v) r)
        ((fderiv ℝ (fun w ↦ F w r)
          (wilkieCase2FlatArityCastLinear m q z)).comp
          (wilkieCase2FlatArityCastLinear m q)) z := by
    simpa only [Function.comp_def] using
      (hFr.hasFDerivAt.comp z
        (wilkieCase2FlatArityCastLinear m q).hasFDerivAt)
  have hscalar := hchain.fderiv
  change fderiv ℝ
      (fun v ↦ F (wilkieCase2FlatArityCastLinear m q v) r) z
        ((Pi.basisFun ℝ (Fin ((m + q) + 1))) j) =
    fderiv ℝ (fun w ↦ F w r)
      (wilkieCase2FlatArityCastLinear m q z)
        ((Pi.basisFun ℝ (Fin ((m + 1) + q)))
          (wilkieCase2FlatArityCastColumns m q j))
  rw [hscalar]
  change fderiv ℝ (fun w ↦ F w r)
      (wilkieCase2FlatArityCastLinear m q z)
      (wilkieCase2FlatArityCastLinear m q
        ((Pi.basisFun ℝ (Fin ((m + q) + 1))) j)) = _
  rw [wilkieCase2FlatArityCastLinear_basis]

theorem wilkieCase2FlatCastInsert_eq_arityCast {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (v : RealEuclidean (m + q)) :
    wilkieCase2FlatCastInsert (q := q) i b v =
      wilkieCase2FlatArityCastLinear m q
        (wilkieCase2_coordinateInsert
          (wilkieCase2FlatFixedIndex (q := q) i) b v) := by
  ext r
  rfl

/-- The source columns retained by a visible-coordinate insertion. -/
def wilkieCase2CylinderColumnInsert {m q : ℕ}
    (i : Fin (m + 1)) :
    Fin (m + q) ↪ Fin ((m + 1) + q) :=
  (Fin.succAboveEmb (wilkieCase2FlatFixedIndex (q := q) i)).trans
    (wilkieCase2FlatArityCastColumns m q)

/-- The visible part of the flat inserted point is exactly the visible
`Fin.insertNth` tuple. -/
theorem wilkieCase2FlatCastInsert_takeLeft {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (v : RealEuclidean (m + q)) :
    realEuclideanTakeLeft (wilkieCase2FlatCastInsert i b v) =
      wilkieCase2_coordinateInsert i b (realEuclideanTakeLeft v) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun t ↦ ?_) j
  · calc
      realEuclideanTakeLeft (wilkieCase2FlatCastInsert i b v) i = b := by
        change wilkieCase2_coordinateInsert
          (wilkieCase2FlatFixedIndex (q := q) i) b v
          (wilkieCase2FlatFixedIndex (q := q) i) = b
        exact wilkieCase2_coordinateInsert_fixed _ _ _
      _ = wilkieCase2_coordinateInsert i b (realEuclideanTakeLeft v) i :=
        (wilkieCase2_coordinateInsert_fixed i b _).symm
  · have hindex := wilkieCase2FlatFixedIndex_free_visible (q := q) i t
    calc
      realEuclideanTakeLeft (wilkieCase2FlatCastInsert i b v)
          (i.succAbove t) = v (Fin.castAdd q t) := by
        change wilkieCase2_coordinateInsert
          (wilkieCase2FlatFixedIndex (q := q) i) b v
            ((Fin.castAdd q (i.succAbove t)).cast
              (wilkieCase2_add_succ_cast m q).symm) =
          v (Fin.castAdd q t)
        rw [← hindex, wilkieCase2_coordinateInsert_free]
      _ = wilkieCase2_coordinateInsert i b
          (realEuclideanTakeLeft v) (i.succAbove t) :=
        (wilkieCase2_coordinateInsert_free i b (realEuclideanTakeLeft v) t).symm

/-- Literal inclusion of the sliced visible-cylinder fiber in the original
restricted fiber. -/
theorem wilkieCase2CylinderFiber_insert_image_subset {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (a : RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ)
    (U : Set (RealEuclidean (m + 1))) :
    wilkieCase2FlatCastInsert i b ''
        wilkieFiberOver
          (fun v ↦ F (wilkieCase2FlatCastInsert i b v)) a
          (wilkieCase2VisibleCylinderSlice i b U) ⊆
      wilkieFiberOver F a U := by
  rintro z ⟨v, hv, rfl⟩
  change F (wilkieCase2FlatCastInsert i b v) = a ∧
    realEuclideanTakeLeft v ∈
      wilkieCase2VisibleCylinderSlice i b U at hv
  change F (wilkieCase2FlatCastInsert i b v) = a ∧
    realEuclideanTakeLeft (wilkieCase2FlatCastInsert i b v) ∈ U
  exact ⟨hv.1, by
    rw [wilkieCase2FlatCastInsert_takeLeft]
    exact hv.2⟩

/-- An initial squared-minor interval on the lower sliced fiber transfers
to the same selected squared-minor interval on the original visible-cylinder
fiber.  `U` is open, hence so is its literal slice.  Neither the Jacobian
identity nor the image inclusion is a premise of this theorem. -/
theorem wilkieCase2_cylinderSliceMinor_squared_interval_lift
    {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (a : RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ)
    (U : Set (RealEuclidean (m + 1))) (hU : IsOpen U)
    (cols : Fin q ↪ Fin (m + q))
    (order : Equiv.Perm (Fin q))
    (hFdiff : ∀ z ∈ wilkieFiberOver F a U,
      DifferentiableAt ℝ F z)
    {η : ℝ} (hη : 0 < η)
    (hinterval : Set.Icc (0 : ℝ) η ⊆
      (fun v ↦ (standardJacobianColumnMinor
        (fun y ↦ F (wilkieCase2FlatCastInsert i b y))
        (order.toEmbedding.trans cols) v) ^ 2) ''
        wilkieFiberOver
          (fun y ↦ F (wilkieCase2FlatCastInsert i b y)) a
          (wilkieCase2VisibleCylinderSlice i b U)) :
    IsOpen (wilkieCase2VisibleCylinderSlice i b U) ∧
      0 < η ∧ Set.Icc (0 : ℝ) η ⊆
        (fun z ↦ (standardJacobianColumnMinor F
          (cols.trans (wilkieCase2CylinderColumnInsert (q := q) i)) z) ^ 2) ''
          wilkieFiberOver F a U := by
  let S : Set (RealEuclidean (m + q)) :=
    wilkieFiberOver
      (fun y ↦ F (wilkieCase2FlatCastInsert i b y)) a
      (wilkieCase2VisibleCylinderSlice i b U)
  have himage : wilkieCase2FlatCastInsert i b '' S ⊆
      wilkieFiberOver F a U :=
    wilkieCase2CylinderFiber_insert_image_subset F a i b U
  have hJac : ∀ v ∈ S,
      standardRectangularJacobian
        (fun y ↦ F (wilkieCase2FlatCastInsert i b y)) v =
      (standardRectangularJacobian F
        (wilkieCase2FlatCastInsert i b v)).submatrix
          (Equiv.refl (Fin q))
          (wilkieCase2CylinderColumnInsert (q := q) i) := by
    intro v hv
    let fixed := wilkieCase2FlatFixedIndex (q := q) i
    let z := wilkieCase2_coordinateInsert fixed b v
    have hz : wilkieCase2FlatCastInsert i b v ∈
        wilkieFiberOver F a U :=
      himage ⟨v, hv, rfl⟩
    have hF : DifferentiableAt ℝ F
        (wilkieCase2FlatArityCastLinear m q z) := by
      rw [← wilkieCase2FlatCastInsert_eq_arityCast]
      exact hFdiff _ hz
    have hFcast : DifferentiableAt ℝ
        (fun w ↦ F (wilkieCase2FlatArityCastLinear m q w)) z :=
      hF.comp z (wilkieCase2FlatArityCastLinear m q).differentiableAt
    have hInsert := wilkieCase2_flatJacobian_coordinateInsert
      (fun w ↦ F (wilkieCase2FlatArityCastLinear m q w))
      fixed b v hFcast
    have hCast := wilkieCase2_flatJacobian_arityCast F z hF
    simp only [wilkieCase2FlatCastInsert_eq_arityCast]
    rw [hInsert, hCast]
    ext r j
    rfl
  refine ⟨wilkieCase2VisibleCylinderSlice_isOpen i b hU, ?_⟩
  exact wilkieCase2_sliceMinor_squared_interval_transport
    F
    (fun y ↦ F (wilkieCase2FlatCastInsert i b y))
    (wilkieCase2FlatCastInsert i b)
    (wilkieCase2CylinderColumnInsert (q := q) i)
    cols (Equiv.refl (Fin q)) order
    hJac himage hη hinterval

end AbelFormalization
