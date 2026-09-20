import AbelFormalization.CharbonnelSardianIntegerAffineSliceGeometry

/-!
# The finite-family algebra of Wilkie's frontier-hyperplane slice

This is the constituent-level part of Wilkie 3.12. Two new hidden
coordinates and two positive parameters are prepended: the reciprocal
radial equation is first, the integer-affine level equation is second,
and every old equation is shifted by two positions. This construction
does not assert an approximation modulus or the arbitrary affine-cut
rank step of Wilkie 3.13.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Retain the visible coordinates and one of two newly appended hidden
coordinates. `i = 0` is radial; `i = 1` is the affine slice level. -/
def wilkieAffineSliceExtraInputLinearMap (n q : ℕ) (i : Fin 2) :
    RealEuclidean (n + (q + 2)) →ₗ[ℝ] RealEuclidean (n + 1) where
  toFun v := Fin.addCases
    (fun j ↦ v (Fin.castAdd (q + 2) j))
    (fun _ ↦ v (Fin.natAdd n (Fin.natAdd q i)))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) k <;> simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) k <;> simp

/-- The extra input map selects exactly the displayed hidden coordinate. -/
theorem wilkieAffineSliceExtraInputLinearMap_append
    {n q : ℕ} (i : Fin 2) (x : RealEuclidean n)
    (oldHidden : RealEuclidean q) (extraHidden : RealEuclidean 2) :
    wilkieAffineSliceExtraInputLinearMap n q i
        (realEuclideanAppend x
          (realEuclideanAppend oldHidden extraHidden)) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ extraHidden i) := by
  funext k
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) k <;>
    simp [wilkieAffineSliceExtraInputLinearMap, realEuclideanAppend]

/-- The old equations discard the two additional hidden coordinates. -/
def wilkieAffineSliceOldEquationLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1)) : RealEuclideanFunction (n + (q + 2)) :=
  old.equation i ∘ realEuclideanProductLeftWitnessLinearMap n 0 q 2

theorem wilkieAffineSliceOldEquationLift_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1)) :
    wilkieAffineSliceOldEquationLift old i ∈ G (n + (q + 2)) :=
  hG.affine_comp (old.equation_mem i)
    (realEuclideanProductLeftWitnessLinearMap n 0 q 2).toAffineMap

theorem wilkieAffineSliceOldEquationLift_append
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1)) (x : RealEuclidean n)
    (oldHidden : RealEuclidean q) (extraHidden : RealEuclidean 2) :
    wilkieAffineSliceOldEquationLift old i
        (realEuclideanAppend x
          (realEuclideanAppend oldHidden extraHidden)) =
      old.equation i (realEuclideanAppend x oldHidden) := by
  have hinput := realEuclideanProductLeftWitnessLinearMap_append
    (n := n) (m := 0) (q := q) (r := 2)
    (v := x) oldHidden extraHidden
  have htake : realEuclideanTakeLeft (n := n) (m := 0) x = x := by
    funext j
    simp [realEuclideanTakeLeft]
  simpa only [wilkieAffineSliceOldEquationLift, htake, Function.comp_apply] using
    congrArg (old.equation i) hinput

/-- The radial equation uses the first new hidden coordinate. -/
def wilkieAffineSliceRadialEquationLift (n q : ℕ) :
    RealEuclideanFunction (n + (q + 2)) :=
  literalZeroRadialReciprocal n ∘
    wilkieAffineSliceExtraInputLinearMap n q 0

theorem wilkieAffineSliceRadialEquationLift_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n q : ℕ) :
    wilkieAffineSliceRadialEquationLift n q ∈ G (n + (q + 2)) :=
  hG.affine_comp (literalZeroRadialReciprocal_mem hG n)
    (wilkieAffineSliceExtraInputLinearMap n q 0).toAffineMap

theorem wilkieAffineSliceRadialEquationLift_append
    {n q : ℕ} (x : RealEuclidean n)
    (oldHidden : RealEuclidean q) (extraHidden : RealEuclidean 2) :
    wilkieAffineSliceRadialEquationLift n q
        (realEuclideanAppend x
          (realEuclideanAppend oldHidden extraHidden)) =
      literalZeroRadialReciprocal n
        (realEuclideanAppend x (fun _ : Fin 1 ↦ extraHidden 0)) := by
  simp [wilkieAffineSliceRadialEquationLift,
    wilkieAffineSliceExtraInputLinearMap_append]

/-- The second new hidden coordinate supplies the positive affine level. -/
def wilkieAffineSliceLevelEquationLift {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) (q : ℕ) :
    RealEuclideanFunction (n + (q + 2)) :=
  integerAffineSliceLevelEquation coeff constant ∘
    wilkieAffineSliceExtraInputLinearMap n q 1

theorem wilkieAffineSliceLevelEquationLift_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) (q : ℕ) :
    wilkieAffineSliceLevelEquationLift coeff constant q ∈
      G (n + (q + 2)) :=
  hG.affine_comp
    (integerAffineSliceLevelEquation_mem hG coeff constant)
    (wilkieAffineSliceExtraInputLinearMap n q 1).toAffineMap

theorem wilkieAffineSliceLevelEquationLift_append
    {n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (x : RealEuclidean n) (oldHidden : RealEuclidean q)
    (extraHidden : RealEuclidean 2) :
    wilkieAffineSliceLevelEquationLift coeff constant q
        (realEuclideanAppend x
          (realEuclideanAppend oldHidden extraHidden)) =
      integerAffineSliceLevelEquation coeff constant
        (realEuclideanAppend x (fun _ : Fin 1 ↦ extraHidden 1)) := by
  simp [wilkieAffineSliceLevelEquationLift,
    wilkieAffineSliceExtraInputLinearMap_append]

/-- Prepend the radial and affine levels to the positive parameter block. -/
def wilkiePrependTwoParameters {q : ℕ}
    (radial slice : ℝ) (old : RealEuclidean (q + 1)) :
    RealEuclidean ((q + 2) + 1) :=
  Fin.cases radial (Fin.cases slice old)

@[simp]
theorem wilkiePrependTwoParameters_radial {q : ℕ}
    (radial slice : ℝ) (old : RealEuclidean (q + 1)) :
    wilkiePrependTwoParameters radial slice old 0 = radial := rfl

@[simp]
theorem wilkiePrependTwoParameters_slice {q : ℕ}
    (radial slice : ℝ) (old : RealEuclidean (q + 1)) :
    wilkiePrependTwoParameters radial slice old
        (Fin.succ (0 : Fin (q + 2))) = slice := rfl

@[simp]
theorem wilkiePrependTwoParameters_old {q : ℕ}
    (radial slice : ℝ) (old : RealEuclidean (q + 1))
    (i : Fin (q + 1)) :
    wilkiePrependTwoParameters radial slice old
        (Fin.succ (Fin.succ i)) = old i := rfl

theorem wilkiePrependTwoParameters_pos_iff {q : ℕ}
    (radial slice : ℝ) (old : RealEuclidean (q + 1)) :
    (∀ i, 0 < wilkiePrependTwoParameters radial slice old i) ↔
      0 < radial ∧ 0 < slice ∧ ∀ i, 0 < old i := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [wilkiePrependTwoParameters] using h 0
    · simpa only [wilkiePrependTwoParameters_slice] using
        h (Fin.succ (0 : Fin (q + 2)))
    · intro i
      simpa [wilkiePrependTwoParameters] using
        h (Fin.succ (Fin.succ i))
  · rintro ⟨hradial, hslice, hold⟩ i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [wilkiePrependTwoParameters] using hradial
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · simpa only [wilkiePrependTwoParameters_slice] using hslice
      · simpa [wilkiePrependTwoParameters] using hold k

/-- The two new equations precede every old equation in one new Sardian
constituent. The global-smoothness premise is used only to certify the
finite differentiability order of the lifted family members. -/
def wilkieAffineSliceConstituent
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q) :
    CharbonnelSardianConstituent G order n (q + 2) where
  visible_pos := old.visible_pos
  equation := Fin.cases (wilkieAffineSliceRadialEquationLift n q)
    (Fin.cases (wilkieAffineSliceLevelEquationLift coeff constant q)
      (wilkieAffineSliceOldEquationLift old))
  equation_mem := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact wilkieAffineSliceRadialEquationLift_mem hG n q
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · exact wilkieAffineSliceLevelEquationLift_mem hG coeff constant q
      · exact wilkieAffineSliceOldEquationLift_mem hG old k
  equation_contDiff := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (hsmooth (n + (q + 2)) _
        (wilkieAffineSliceRadialEquationLift_mem hG n q)).of_le (by simp)
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · exact (hsmooth (n + (q + 2)) _
          (wilkieAffineSliceLevelEquationLift_mem hG coeff constant q)).of_le
          (by simp)
      · exact (hsmooth (n + (q + 2)) _
          (wilkieAffineSliceOldEquationLift_mem hG old k)).of_le (by simp)

/-- Equation zero is the radial compactifier. -/
theorem wilkieAffineSliceConstituent_equation_radial
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q) :
    (wilkieAffineSliceConstituent hG hsmooth coeff constant old).equation 0 =
      wilkieAffineSliceRadialEquationLift n q := rfl

/-- Equation one is the affine level. -/
theorem wilkieAffineSliceConstituent_equation_level
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q) :
    (wilkieAffineSliceConstituent hG hsmooth coeff constant old).equation
        (Fin.succ (0 : Fin (q + 2))) =
      wilkieAffineSliceLevelEquationLift coeff constant q := rfl

/-- Old equation `i` appears at parameter position `i+2`. -/
theorem wilkieAffineSliceConstituent_equation_old
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1)) :
    (wilkieAffineSliceConstituent hG hsmooth coeff constant old).equation
        (Fin.succ (Fin.succ i)) =
      wilkieAffineSliceOldEquationLift old i := rfl

namespace CharbonnelPaddedSardianConstituent

/-- Lift one padded constituent, preserving its original trailing unused
positive parameters after the two new leading parameters. -/
def wilkieAffineSliceLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    CharbonnelPaddedSardianConstituent G order n (K + 2) where
  hiddenArity := piece.hiddenArity + 2
  hiddenArity_le := Nat.add_le_add_right piece.hiddenArity_le 2
  constituent :=
    wilkieAffineSliceConstituent hG hsmooth coeff constant piece.constituent

end CharbonnelPaddedSardianConstituent

namespace CharbonnelFiniteSardianFamily

/-- Apply the same two-equation lift to every member of a finite Sardian
family, retaining the original list and its common order. -/
def wilkieAffineSliceLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (family : CharbonnelFiniteSardianFamily G order n K) :
    CharbonnelFiniteSardianFamily G order n (K + 2) where
  visible_pos := family.visible_pos
  constituents := family.constituents.map
    (CharbonnelPaddedSardianConstituent.wilkieAffineSliceLift
      hG hsmooth coeff constant)

end CharbonnelFiniteSardianFamily

end AbelFormalization
