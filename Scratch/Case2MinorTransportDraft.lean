import AbelFormalization.WilkieArbitraryMinorDerivativeBridge
import AbelFormalization.WilkieFixedMinorConnectedInterval

/-!
# Case 2: transport of a selected maximal minor through one coordinate slice

This source-only draft isolates the algebraic part of the one-visible-coordinate
step in Wilkie's proof of Corollary 2.9.  A slice derivative has the full
Jacobian's columns with the fixed coordinate omitted.  The row permutation
`rows` records any reordering of the equations; `order` records any reordering
of the selected `k` columns.  Both permutations affect the determinant by at
most a sign, and therefore do not affect its square.

`wilkieCase2_sliceMinor_squared_interval_transport` records the exact remaining
analytic interface: `hJac` is the chain-rule identity for the affine coordinate
insertion, and `himage` places the inserted slice in the original restricted
fiber.  Neither premise asserts a conclusion about the minor itself.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Insert one fixed source coordinate, leaving every other coordinate in
its original order.  In Wilkie Case 2 the fixed index lies in the visible
block; `Fin.succAboveEmb fixed` is then the corresponding column injection. -/
def wilkieCase2_coordinateInsert {a : ℕ}
    (fixed : Fin (a + 1)) (b : ℝ)
    (x : RealEuclidean a) : RealEuclidean (a + 1) :=
  Fin.insertNth fixed b x

theorem wilkieCase2_coordinateInsert_fixed {a : ℕ}
    (fixed : Fin (a + 1)) (b : ℝ) (x : RealEuclidean a) :
    wilkieCase2_coordinateInsert fixed b x fixed = b := by
  exact Fin.insertNth_apply_same (α := fun _ ↦ ℝ) fixed b x

theorem wilkieCase2_coordinateInsert_free {a : ℕ}
    (fixed : Fin (a + 1)) (b : ℝ) (x : RealEuclidean a)
    (j : Fin a) :
    wilkieCase2_coordinateInsert fixed b x (fixed.succAbove j) = x j := by
  exact Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) fixed b x j

/-- Permuting rows and columns of a real square matrix preserves the square
of its determinant.  This is the sign bookkeeping needed when Wilkie writes
the selected columns as merely distinct rather than in increasing order. -/
private theorem wilkieCase2_det_sq_reindex {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ)
    (rows order : Equiv.Perm (Fin k)) :
    ((M.submatrix rows order).det) ^ 2 = M.det ^ 2 := by
  calc
    ((M.submatrix rows order).det) ^ 2 =
        |(M.submatrix rows order).det| ^ 2 :=
      (sq_abs _).symm
    _ = |M.det| ^ 2 :=
      congrArg (fun t : ℝ ↦ t ^ 2)
        (Matrix.abs_det_submatrix_equiv_equiv rows order M)
    _ = M.det ^ 2 := sq_abs _

/-- Selecting a minor after a column insertion and arbitrary equation/column
reordering gives the same *squared* minor of the original matrix.  The
injection `insert` is the source-column map of the fixed-coordinate slice. -/
theorem wilkieCase2_matrixMinor_sq_transport {a b k : ℕ}
    (J : Matrix (Fin k) (Fin b) ℝ)
    (insert : Fin a ↪ Fin b) (cols : Fin k ↪ Fin a)
    (rows order : Equiv.Perm (Fin k)) :
    (((J.submatrix rows insert).submatrix id
      (order.toEmbedding.trans cols)).det) ^ 2 =
      ((J.submatrix id (cols.trans insert)).det) ^ 2 := by
  have hmatrix :
      (J.submatrix rows insert).submatrix id
          (order.toEmbedding.trans cols) =
        (J.submatrix id (cols.trans insert)).submatrix rows order := by
    ext i j
    rfl
  rw [hmatrix]
  exact wilkieCase2_det_sq_reindex
    (J.submatrix id (cols.trans insert)) rows order

/-- A pointwise equality of squared minor values and inclusion of the
inserted slice transport an initial image interval to the original fiber. -/
theorem wilkieCase2_squared_interval_image_transport
    {Slice Original : Type*} {S : Set Slice} {X : Set Original}
    (insert : Slice → Original) (d : Slice → ℝ) (D : Original → ℝ)
    (himage : insert '' S ⊆ X)
    (hvalue : ∀ x ∈ S, (d x) ^ 2 = (D (insert x)) ^ 2)
    {η : ℝ}
    (hinterval : Set.Icc (0 : ℝ) η ⊆ (fun x ↦ (d x) ^ 2) '' S) :
    Set.Icc (0 : ℝ) η ⊆ (fun y ↦ (D y) ^ 2) '' X := by
  intro t ht
  obtain ⟨x, hxS, hxt⟩ := hinterval ht
  refine ⟨insert x, himage ⟨x, hxS, rfl⟩, ?_⟩
  exact (hvalue x hxS).symm.trans hxt

/-- The selected minor of the sliced map gives the *same squared-minor
interval* on the original fiber.  To apply this to a concrete Wilkie slice,
prove `hJac` from the affine insertion chain rule, with `columnInsert` omitting
the fixed visible coordinate, and prove `himage` from the definition of the
restricted fibers.  The row/column order is permitted to change. -/
theorem wilkieCase2_sliceMinor_squared_interval_transport
    {a b k : ℕ}
    (F : RealEuclidean b → RealEuclidean k)
    (G : RealEuclidean a → RealEuclidean k)
    (sliceInsert : RealEuclidean a → RealEuclidean b)
    (columnInsert : Fin a ↪ Fin b)
    (cols : Fin k ↪ Fin a)
    (rows order : Equiv.Perm (Fin k))
    {S : Set (RealEuclidean a)} {X : Set (RealEuclidean b)}
    (hJac : ∀ x ∈ S,
      standardRectangularJacobian G x =
        (standardRectangularJacobian F (sliceInsert x)).submatrix
          rows columnInsert)
    (himage : sliceInsert '' S ⊆ X)
    {η : ℝ} (hη : 0 < η)
    (hinterval : Set.Icc (0 : ℝ) η ⊆
      (fun x ↦ (standardJacobianColumnMinor G
        (order.toEmbedding.trans cols) x) ^ 2) '' S) :
    0 < η ∧ Set.Icc (0 : ℝ) η ⊆
      (fun y ↦ (standardJacobianColumnMinor F
        (cols.trans columnInsert) y) ^ 2) '' X := by
  refine ⟨hη, ?_⟩
  apply wilkieCase2_squared_interval_image_transport
    sliceInsert
    (standardJacobianColumnMinor G (order.toEmbedding.trans cols))
    (standardJacobianColumnMinor F (cols.trans columnInsert))
    himage ?_ hinterval
  intro x hxS
  change (((standardRectangularJacobian G x).submatrix id
      (order.toEmbedding.trans cols)).det) ^ 2 =
    (((standardRectangularJacobian F (sliceInsert x)).submatrix id
      (cols.trans columnInsert)).det) ^ 2
  rw [hJac x hxS]
  exact wilkieCase2_matrixMinor_sq_transport
    (standardRectangularJacobian F (sliceInsert x))
    columnInsert cols rows order

end AbelFormalization
