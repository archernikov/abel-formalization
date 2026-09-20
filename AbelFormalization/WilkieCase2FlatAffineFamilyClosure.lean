import AbelFormalization.WilkieCase2CylinderMinorIntervalLift
import AbelFormalization.AbelGeometricFamily

/-!
# Affine-family closure under Wilkie Case 2 slices

The casted flat insertion is packaged as an affine map. Consequently every
component of a geometric-family tuple remains in the family after a visible
coordinate is fixed.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The linear part of the casted flat coordinate insertion. -/
def wilkieCase2FlatCastInsertLinear {m q : ℕ}
    (i : Fin (m + 1)) :
    RealEuclidean (m + q) →L[ℝ] RealEuclidean ((m + 1) + q) :=
  (wilkieCase2FlatArityCastLinear m q).comp
    (wilkieCase2_coordinateInsertLinear
      (wilkieCase2FlatFixedIndex (q := q) i))

/-- The casted flat coordinate insertion as an affine map. -/
def wilkieCase2FlatCastInsertAffine {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ) :
    RealEuclidean (m + q) →ᵃ[ℝ] RealEuclidean ((m + 1) + q) :=
  (wilkieCase2FlatCastInsertLinear (q := q) i).toAffineMap +
    AffineMap.const ℝ (RealEuclidean (m + q))
      (wilkieCase2FlatCastInsert i b 0)

@[simp]
theorem wilkieCase2FlatCastInsertAffine_apply {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ) (z : RealEuclidean (m + q)) :
    wilkieCase2FlatCastInsertAffine i b z =
      wilkieCase2FlatCastInsert i b z := by
  ext r
  change
    wilkieCase2FlatArityCastLinear m q
        (wilkieCase2_coordinateInsertLinear
          (wilkieCase2FlatFixedIndex (q := q) i) z) r +
      wilkieCase2FlatCastInsert i b 0 r =
    wilkieCase2FlatCastInsert i b z r
  change
    wilkieCase2_coordinateInsertLinear
        (wilkieCase2FlatFixedIndex (q := q) i) z
        (r.cast (wilkieCase2_add_succ_cast m q).symm) +
      wilkieCase2_coordinateInsert
        (wilkieCase2FlatFixedIndex (q := q) i) b 0
        (r.cast (wilkieCase2_add_succ_cast m q).symm) =
    wilkieCase2_coordinateInsert
      (wilkieCase2FlatFixedIndex (q := q) i) b z
      (r.cast (wilkieCase2_add_succ_cast m q).symm)
  let fixed := wilkieCase2FlatFixedIndex (q := q) i
  let s := r.cast (wilkieCase2_add_succ_cast m q).symm
  rcases Fin.eq_self_or_eq_succAbove fixed s with hs | ⟨j, hs⟩
  · rw [show r.cast (wilkieCase2_add_succ_cast m q).symm = fixed
        from hs]
    simp only [fixed, wilkieCase2_coordinateInsertLinear_fixed,
      wilkieCase2_coordinateInsert_fixed, zero_add]
  · rw [show r.cast (wilkieCase2_add_succ_cast m q).symm = fixed.succAbove j
        from hs]
    simp only [fixed, wilkieCase2_coordinateInsertLinear_free,
      wilkieCase2_coordinateInsert_free, Pi.zero_apply, add_zero]

/-- Componentwise membership in a geometric family survives a Case 2 flat
visible-coordinate slice. -/
theorem functionTupleInFamily_comp_wilkieCase2FlatCastInsert
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {m q : ℕ}
    (H : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (hH : FunctionTupleInFamily G H)
    (i : Fin (m + 1)) (b : ℝ) :
    FunctionTupleInFamily G
      (H ∘ wilkieCase2FlatCastInsert i b) := by
  intro j
  have hpull := hG.affine_comp (hH j)
    (wilkieCase2FlatCastInsertAffine (q := q) i b)
  change (fun z ↦ H (wilkieCase2FlatCastInsert i b z) j) ∈ G (m + q)
  convert hpull using 1
  funext z
  change H (wilkieCase2FlatCastInsert i b z) j =
    H (wilkieCase2FlatCastInsertAffine i b z) j
  rw [wilkieCase2FlatCastInsertAffine_apply]

end AbelFormalization
