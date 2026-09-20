import AbelFormalization.CharbonnelSardianIntegerAffineSliceLift

/-!
# Exact sections of Wilkie's one-hyperplane constituent lift

This module eliminates the two new hidden coordinates from the lifted
constituent. For positive radial and slice parameters its visible section
is exactly the old section intersected with a reciprocal-radial compact
region and a small integer-affine level band. These are algebraic carrier
identities only; no approximation modulus or rank-induction statement is
inferred.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The radial level has a hidden witness also at the boundary of its
closed visible sublevel region. -/
theorem literalZeroRadialReciprocal_exists_iff_visible_bound
    {n : ℕ} (x : RealEuclidean n) {radial : ℝ}
    (hradial : 0 < radial) :
    (∃ y : RealEuclidean 1,
      literalZeroRadialReciprocal n (realEuclideanAppend x y) = radial) ↔
      literalZeroVisibleRadialDenominator x ≤ radial⁻¹ := by
  constructor
  · rintro ⟨y, hy⟩
    exact literalZeroRadialReciprocal_visible_bound x y radial hy
  · intro hvisible
    let t := radial⁻¹ - literalZeroVisibleRadialDenominator x
    have ht : 0 ≤ t := sub_nonneg.mpr hvisible
    let y : RealEuclidean 1 := fun _ ↦ Real.sqrt t
    refine ⟨y, ?_⟩
    have hden : literalZeroRadialDenominator n
        (realEuclideanAppend x y) = radial⁻¹ := by
      simp only [literalZeroRadialDenominator,
        realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
      change literalZeroVisibleRadialDenominator x +
        (Real.sqrt t) ^ 2 = radial⁻¹
      rw [Real.sq_sqrt ht]
      dsimp [t]
      ring
    simp only [literalZeroRadialReciprocal, hden, inv_inv]

/-- Before eliminating the new hidden variables, exact membership of the
lifted constituent is the old section together with independent radial
and affine-level witnesses. -/
theorem mem_wilkieAffineSliceConstituent_carrier_iff_witnesses
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q)
    (x : RealEuclidean n) (radial slice : ℝ)
    (oldParameters : RealEuclidean (q + 1)) :
    realEuclideanAppend x
        (wilkiePrependTwoParameters radial slice oldParameters) ∈
      (wilkieAffineSliceConstituent hG hsmooth coeff constant old).carrier ↔
      0 < radial ∧ 0 < slice ∧
        realEuclideanAppend x oldParameters ∈ old.carrier ∧
        (∃ y : RealEuclidean 1,
          literalZeroRadialReciprocal n (realEuclideanAppend x y) = radial) ∧
        (∃ y : RealEuclidean 1,
          integerAffineSliceLevelEquation coeff constant
            (realEuclideanAppend x y) = slice) := by
  let lifted := wilkieAffineSliceConstituent hG hsmooth coeff constant old
  change realEuclideanAppend x
      (wilkiePrependTwoParameters radial slice oldParameters) ∈
      lifted.carrier ↔ _
  rw [lifted.mem_carrier_iff]
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · rintro ⟨⟨hidden, hequations⟩, hpositive⟩
    obtain ⟨hradial, hslice, holdPositive⟩ :=
      (wilkiePrependTwoParameters_pos_iff
        radial slice oldParameters).mp hpositive
    let oldHidden : RealEuclidean q := realEuclideanTakeLeft hidden
    let extraHidden : RealEuclidean 2 := realEuclideanTakeRight hidden
    have hsplit : hidden =
        realEuclideanAppend oldHidden extraHidden :=
      (realEuclideanAppend_takeLeft_takeRight hidden).symm
    rw [hsplit] at hequations
    have holdEquations : ∀ i : Fin (q + 1),
        old.equation i (realEuclideanAppend x oldHidden) =
          oldParameters i := by
      intro i
      have hi := hequations (Fin.succ (Fin.succ i))
      simpa only [lifted,
        wilkieAffineSliceConstituent_equation_old,
        wilkieAffineSliceOldEquationLift_append,
        wilkiePrependTwoParameters_old] using hi
    have holdCarrier :
        realEuclideanAppend x oldParameters ∈ old.carrier := by
      rw [old.mem_carrier_iff]
      simp only [realEuclideanTakeLeft_append,
        realEuclideanTakeRight_append]
      exact ⟨⟨oldHidden, holdEquations⟩, holdPositive⟩
    have hradialEquation := hequations 0
    have hradialWitness : ∃ y : RealEuclidean 1,
        literalZeroRadialReciprocal n (realEuclideanAppend x y) =
          radial := by
      refine ⟨fun _ ↦ extraHidden 0, ?_⟩
      simpa only [lifted,
        wilkieAffineSliceConstituent_equation_radial,
        wilkieAffineSliceRadialEquationLift_append,
        wilkiePrependTwoParameters_radial] using hradialEquation
    have hsliceEquation :=
      hequations (Fin.succ (0 : Fin (q + 2)))
    have hsliceWitness : ∃ y : RealEuclidean 1,
        integerAffineSliceLevelEquation coeff constant
          (realEuclideanAppend x y) = slice := by
      refine ⟨fun _ ↦ extraHidden 1, ?_⟩
      simpa only [lifted,
        wilkieAffineSliceConstituent_equation_level,
        wilkieAffineSliceLevelEquationLift_append,
        wilkiePrependTwoParameters_slice] using hsliceEquation
    exact ⟨hradial, hslice, holdCarrier,
      hradialWitness, hsliceWitness⟩
  · rintro ⟨hradial, hslice, holdCarrier,
        ⟨radialHidden, hradialEquation⟩,
        ⟨sliceHidden, hsliceEquation⟩⟩
    obtain ⟨⟨oldHidden, holdEquations⟩, holdPositive⟩ :=
      (old.mem_carrier_iff).mp holdCarrier
    simp only [realEuclideanTakeLeft_append,
      realEuclideanTakeRight_append] at holdEquations holdPositive
    let extraHidden : RealEuclidean 2 :=
      Fin.cases (radialHidden 0)
        (fun _ : Fin 1 ↦ sliceHidden 0)
    have hradialHidden :
        (fun _ : Fin 1 ↦ extraHidden 0) = radialHidden := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst j
      rfl
    have hsliceHidden :
        (fun _ : Fin 1 ↦ extraHidden 1) = sliceHidden := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst j
      rfl
    have hnewRadial :
        lifted.equation 0
          (realEuclideanAppend x
            (realEuclideanAppend oldHidden extraHidden)) =
          wilkiePrependTwoParameters radial slice oldParameters 0 := by
      simpa only [lifted,
        wilkieAffineSliceConstituent_equation_radial,
        wilkieAffineSliceRadialEquationLift_append,
        wilkiePrependTwoParameters_radial,
        hradialHidden] using hradialEquation
    have hnewSlice :
        lifted.equation (Fin.succ (0 : Fin (q + 2)))
          (realEuclideanAppend x
            (realEuclideanAppend oldHidden extraHidden)) =
          wilkiePrependTwoParameters radial slice oldParameters
            (Fin.succ (0 : Fin (q + 2))) := by
      simpa only [lifted,
        wilkieAffineSliceConstituent_equation_level,
        wilkieAffineSliceLevelEquationLift_append,
        wilkiePrependTwoParameters_slice,
        hsliceHidden] using hsliceEquation
    have hnewOld : ∀ i : Fin (q + 1),
        lifted.equation (Fin.succ (Fin.succ i))
          (realEuclideanAppend x
            (realEuclideanAppend oldHidden extraHidden)) =
          wilkiePrependTwoParameters radial slice oldParameters
            (Fin.succ (Fin.succ i)) := by
      intro i
      simpa only [lifted,
        wilkieAffineSliceConstituent_equation_old,
        wilkieAffineSliceOldEquationLift_append,
        wilkiePrependTwoParameters_old] using holdEquations i
    refine ⟨⟨realEuclideanAppend oldHidden extraHidden, ?_⟩, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact hnewRadial
      · refine Fin.cases ?_ (fun k ↦ ?_) j
        · exact hnewSlice
        · exact hnewOld k
    · exact (wilkiePrependTwoParameters_pos_iff
        radial slice oldParameters).mpr
        ⟨hradial, hslice, holdPositive⟩

/-- Eliminating the two independent witnesses gives the source's exact
visible section: old section, radial compactifier, and affine level band. -/
theorem mem_wilkieAffineSliceConstituent_carrier_iff_bounded_section
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q)
    (x : RealEuclidean n) (radial slice : ℝ)
    (oldParameters : RealEuclidean (q + 1)) :
    realEuclideanAppend x
        (wilkiePrependTwoParameters radial slice oldParameters) ∈
      (wilkieAffineSliceConstituent hG hsmooth coeff constant old).carrier ↔
      0 < radial ∧ 0 < slice ∧
        realEuclideanAppend x oldParameters ∈ old.carrier ∧
        literalZeroVisibleRadialDenominator x ≤ radial⁻¹ ∧
        (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ slice := by
  rw [mem_wilkieAffineSliceConstituent_carrier_iff_witnesses]
  constructor
  · rintro ⟨hradial, hslice, hold, hradialWitness,
        hsliceWitness⟩
    exact ⟨hradial, hslice, hold,
      (literalZeroRadialReciprocal_exists_iff_visible_bound
        x hradial).mp hradialWitness,
      (integerAffineSliceLevel_exists_iff
        coeff constant x slice).mp hsliceWitness⟩
  · rintro ⟨hradial, hslice, hold, hvisible, hlevel⟩
    exact ⟨hradial, hslice, hold,
      (literalZeroRadialReciprocal_exists_iff_visible_bound
        x hradial).mpr hvisible,
      (integerAffineSliceLevel_exists_iff
        coeff constant x slice).mpr hlevel⟩

/-- The literal projected-section identity of the one-constituent
Wilkie 3.12 lift at fixed positive parameters. -/
theorem wilkieAffineSliceConstituent_section_eq
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (old : CharbonnelSardianConstituent G order n q)
    (radial slice : ℝ) (hradial : 0 < radial)
    (hslice : 0 < slice)
    (oldParameters : RealEuclidean (q + 1)) :
    {x : RealEuclidean n |
      realEuclideanAppend x
        (wilkiePrependTwoParameters radial slice oldParameters) ∈
          (wilkieAffineSliceConstituent
            hG hsmooth coeff constant old).carrier} =
      {x : RealEuclidean n |
        realEuclideanAppend x oldParameters ∈ old.carrier} ∩
      {x : RealEuclidean n |
        literalZeroVisibleRadialDenominator x ≤ radial⁻¹} ∩
      {x : RealEuclidean n |
        (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ slice} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [mem_wilkieAffineSliceConstituent_carrier_iff_bounded_section]
  simp only [hradial, hslice, true_and, and_assoc]

end AbelFormalization
