import AbelFormalization.WilkieCase2SliceRegularity
import AbelFormalization.WilkieCase2FlatJacobianInsertion
import AbelFormalization.LionGlobalSubmersionFixedSquare

/-!
# Case 2 product/flat coordinate transport

The regular-ball slice is formulated on a product with visible coordinates
first.  The Jacobian transport uses one flat `RealEuclidean` vector.  This
draft makes the concatenation and the one-coordinate `Nat` cast explicit.
All lemmas are source-only pending the root agent's compilation pass.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Visible-first concatenation, in the exact source and target arities of
the Case 2 descent. -/
def wilkieCase2ProductFlatEquiv (n q : ℕ) :
    ((Fin n → ℝ) × (Fin q → ℝ)) ≃L[ℝ] RealEuclidean (n + q) :=
  realEuclideanAppendContinuousLinearEquiv n q

@[simp]
theorem wilkieCase2ProductFlatEquiv_visible {n q : ℕ}
    (z : (Fin n → ℝ) × (Fin q → ℝ)) (j : Fin n) :
    wilkieCase2ProductFlatEquiv n q z (Fin.castAdd q j) = z.1 j := by
  simp [wilkieCase2ProductFlatEquiv]

@[simp]
theorem wilkieCase2ProductFlatEquiv_hidden {n q : ℕ}
    (z : (Fin n → ℝ) × (Fin q → ℝ)) (j : Fin q) :
    wilkieCase2ProductFlatEquiv n q z (Fin.natAdd n j) = z.2 j := by
  simp [wilkieCase2ProductFlatEquiv]

/-- The one-coordinate slice has target `(m + 1) + q`, while the generic
flat insertion has target `(m + q) + 1`. -/
theorem wilkieCase2_add_succ_cast (m q : ℕ) :
    (m + q) + 1 = (m + 1) + q := by
  omega

/-- The fixed flat column is the chosen visible column after the arity
cast. -/
def wilkieCase2FlatFixedIndex {m q : ℕ}
    (i : Fin (m + 1)) : Fin ((m + q) + 1) :=
  (Fin.castAdd q i).cast (wilkieCase2_add_succ_cast m q).symm

/-- Free visible columns retain their index after deleting the pivot. -/
theorem wilkieCase2FlatFixedIndex_free_visible {m q : ℕ}
    (i : Fin (m + 1)) (j : Fin m) :
    (wilkieCase2FlatFixedIndex (q := q) i).succAbove
        (Fin.castAdd q j) =
      (Fin.castAdd q (i.succAbove j)).cast
        (wilkieCase2_add_succ_cast m q).symm := by
  apply Fin.ext
  simp only [wilkieCase2FlatFixedIndex, Fin.succAbove, Fin.lt_def,
    Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val]

/-- Every hidden column is shifted by one flat position, independently of
which visible coordinate was fixed. -/
theorem wilkieCase2FlatFixedIndex_free_hidden {m q : ℕ}
    (i : Fin (m + 1)) (j : Fin q) :
    (wilkieCase2FlatFixedIndex (q := q) i).succAbove
        (Fin.natAdd m j) =
      (Fin.natAdd (m + 1) j).cast
        (wilkieCase2_add_succ_cast m q).symm := by
  apply Fin.ext
  simp only [wilkieCase2FlatFixedIndex, Fin.succAbove, Fin.lt_def,
    Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc,
    Fin.val_succ, apply_ite Fin.val]
  split_ifs <;> omega

/-- Generic flat insertion, followed by the arity cast needed to put the
visible and hidden blocks in their original order. -/
def wilkieCase2FlatCastInsert {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (v : RealEuclidean (m + q)) : RealEuclidean ((m + 1) + q) :=
  fun r ↦ wilkieCase2_coordinateInsert
    (wilkieCase2FlatFixedIndex (q := q) i) b v
    (r.cast (wilkieCase2_add_succ_cast m q).symm)

/-- Inserting a visible coordinate in the product and flattening gives
exactly the casted flat `Fin.insertNth` insertion. -/
theorem wilkieCase2FlatCastInsert_commutes {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (y : (Fin m → ℝ) × (Fin q → ℝ)) :
    wilkieCase2FlatCastInsert i b
        (wilkieCase2ProductFlatEquiv m q y) =
      wilkieCase2ProductFlatEquiv (m + 1) q
        (wilkieCase2VisibleInsert i b y) := by
  funext r
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) r
  · refine Fin.succAboveCases i ?_ (fun t ↦ ?_) j
    · simp [wilkieCase2FlatCastInsert, wilkieCase2FlatFixedIndex,
        wilkieCase2VisibleInsert, wilkieCase2ProductFlatEquiv,
        wilkieCase2_coordinateInsert]
    · have hindex := wilkieCase2FlatFixedIndex_free_visible (q := q) i t
      simp only [wilkieCase2FlatCastInsert,
        wilkieCase2ProductFlatEquiv_visible, wilkieCase2VisibleInsert]
      rw [← hindex, wilkieCase2_coordinateInsert_free]
      simp
  · have hindex := wilkieCase2FlatFixedIndex_free_hidden (m := m) i j
    simp only [wilkieCase2FlatCastInsert,
      wilkieCase2ProductFlatEquiv_hidden, wilkieCase2VisibleInsert]
    rw [← hindex, wilkieCase2_coordinateInsert_free]
    simp

/-- A ball transported by concatenation has the same membership test at
corresponding points.  The flat set need not itself be a metric ball: the
canonical product and function-space norms can differ. -/
theorem wilkieCase2_flat_ball_mem_iff {n q : ℕ}
    (center : (Fin n → ℝ) × (Fin q → ℝ)) (radius : ℝ)
    (z : (Fin n → ℝ) × (Fin q → ℝ)) :
    wilkieCase2ProductFlatEquiv n q z ∈
        wilkieCase2ProductFlatEquiv n q '' Metric.ball center radius ↔
      z ∈ Metric.ball center radius := by
  constructor
  · rintro ⟨w, hw, hEq⟩
    have hwz := (wilkieCase2ProductFlatEquiv n q).injective hEq
    simpa [hwz] using hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The open part of the product slice is the preimage of the transported
ambient ball under the flat insertion. -/
theorem wilkieCase2_flat_ball_slice_preimage {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (center : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
    (radius : ℝ) :
    (wilkieCase2VisibleInsert i b) ⁻¹' Metric.ball center radius =
      (wilkieCase2FlatCastInsert i b ∘
        wilkieCase2ProductFlatEquiv m q) ⁻¹'
          (wilkieCase2ProductFlatEquiv (m + 1) q ''
            Metric.ball center radius) := by
  ext y
  simp only [Set.mem_preimage, Function.comp_apply]
  rw [wilkieCase2FlatCastInsert_commutes,
    wilkieCase2_flat_ball_mem_iff]

/-- The flat version of a product slice map is a mere source-coordinate
change; this identity is the derivative-transport interface. -/
theorem wilkieCase2_flat_slice_map_eq {m q : ℕ}
    {K : Type*} (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → K)
    (i : Fin (m + 1)) (b : ℝ) :
    (F ∘ (wilkieCase2ProductFlatEquiv (m + 1) q).symm) ∘
      wilkieCase2FlatCastInsert i b =
        (F ∘ wilkieCase2VisibleInsert i b) ∘
          (wilkieCase2ProductFlatEquiv m q).symm := by
  funext z
  let y := (wilkieCase2ProductFlatEquiv m q).symm z
  have hz : wilkieCase2ProductFlatEquiv m q y = z :=
    (wilkieCase2ProductFlatEquiv m q).apply_symm_apply z
  have hcomm := wilkieCase2FlatCastInsert_commutes i b y
  rw [hz] at hcomm
  simp only [Function.comp_apply]
  rw [hcomm, (wilkieCase2ProductFlatEquiv (m + 1) q).symm_apply_apply]

/-- Surjectivity of the sliced derivative survives flattening.  This is
the regularity statement needed before using the flat Jacobian minor. -/
theorem wilkieCase2_flat_slice_fderiv_surjective {m q : ℕ}
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → K)
    (i : Fin (m + 1)) (b : ℝ)
    (y : (Fin m → ℝ) × (Fin q → ℝ))
    (hsurj : Function.Surjective
      (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y)) :
    Function.Surjective
      (fderiv ℝ
        ((F ∘ (wilkieCase2ProductFlatEquiv (m + 1) q).symm) ∘
          wilkieCase2FlatCastInsert i b)
        (wilkieCase2ProductFlatEquiv m q y)) := by
  rw [wilkieCase2_flat_slice_map_eq]
  let E := wilkieCase2ProductFlatEquiv m q
  have hderiv :
      fderiv ℝ ((F ∘ wilkieCase2VisibleInsert i b) ∘ E.symm)
          (E y) =
        (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y).comp
          (E.symm : RealEuclidean (m + q) →L[ℝ]
            ((Fin m → ℝ) × (Fin q → ℝ))) := by
    rw [E.symm.comp_right_fderiv, E.symm_apply_apply]
  rw [hderiv]
  exact hsurj.comp E.symm.surjective

/-- Pointwise regularity on a product slice becomes regularity on its flat
image, with no new analytic assumption. -/
theorem wilkieCase2_flat_slice_regular_on_image {m q : ℕ}
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → K)
    (i : Fin (m + 1)) (b : ℝ)
    (S : Set ((Fin m → ℝ) × (Fin q → ℝ)))
    (hregular : ∀ y ∈ S,
      Function.Surjective
        (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y)) :
    ∀ v ∈ wilkieCase2ProductFlatEquiv m q '' S,
      Function.Surjective
        (fderiv ℝ
          ((F ∘ (wilkieCase2ProductFlatEquiv (m + 1) q).symm) ∘
            wilkieCase2FlatCastInsert i b) v) := by
  rintro v ⟨y, hy, rfl⟩
  exact wilkieCase2_flat_slice_fderiv_surjective
    F i b y (hregular y hy)

end AbelFormalization
