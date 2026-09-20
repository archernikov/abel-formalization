import AbelFormalization.CharbonnelSardianIntegerAffineSliceSections
import AbelFormalization.CharbonnelCompactRadialIntegerAffineSliceBelow

/-!
# Padded-family sections for the Sardian integer-affine lift

The one-constituent section identity for Wilkie's affine-slice lift extends
through the common-depth padding and finite-family union.  Consequently the
compact below-scale estimate applies directly to a section of the lifted
finite Sardian family.

This is the from-below carrier bridge.  Constructing the nested modulus and
the frontier approximation from above remain separate from this algebraic
and compactness step.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

private theorem wilkieAffineSlice_paddedPrefix_eq
    {q K : ℕ} (hqK : q ≤ K)
    (radial slice : ℝ) (oldParameters : RealEuclidean (K + 1)) :
    (fun i : Fin ((q + 2) + 1) ↦
      wilkiePrependTwoParameters radial slice oldParameters
        (Fin.castLE
          (Nat.succ_le_succ (Nat.add_le_add_right hqK 2)) i)) =
      wilkiePrependTwoParameters radial slice
        (fun i : Fin (q + 1) ↦
          oldParameters (Fin.castLE (Nat.succ_le_succ hqK) i)) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · rfl

/-- Membership in a section of the lifted padded family implies membership
in the corresponding old section, together with the radial and squared
affine-level bounds.  This is the finite-family form of
`wilkieAffineSliceConstituent_section_eq`. -/
theorem wilkieAffineSliceFiniteFamily_section_lifts_old
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (family : CharbonnelFiniteSardianFamily G order n K)
    (x : RealEuclidean n) (radial slice : ℝ)
    (oldParameters : RealEuclidean (K + 1))
    (hnew : realEuclideanAppend x
        (wilkiePrependTwoParameters radial slice oldParameters) ∈
      (family.wilkieAffineSliceLift
        hG hsmooth coeff constant).carrier) :
    0 < radial ∧ 0 < slice ∧
      realEuclideanAppend x oldParameters ∈ family.carrier ∧
      literalZeroVisibleRadialDenominator x ≤ radial⁻¹ ∧
      (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ slice := by
  change ∃ liftedPiece ∈ family.constituents.map
      (CharbonnelPaddedSardianConstituent.wilkieAffineSliceLift
        hG hsmooth coeff constant),
      realEuclideanAppend x
          (wilkiePrependTwoParameters radial slice oldParameters) ∈
        liftedPiece.carrier at hnew
  obtain ⟨_, hliftedPiece, hnewPiece⟩ := hnew
  obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hliftedPiece
  let oldPieceParameters : RealEuclidean (piece.hiddenArity + 1) :=
    fun i ↦ oldParameters
      (Fin.castLE (Nat.succ_le_succ piece.hiddenArity_le) i)
  have hnewPadded :=
    (mem_charbonnelParameterPad_append_iff
      (Nat.add_le_add_right piece.hiddenArity_le 2) x
      (wilkiePrependTwoParameters radial slice oldParameters)).mp hnewPiece
  have hnewConstituent :
      realEuclideanAppend x
          (wilkiePrependTwoParameters radial slice oldPieceParameters) ∈
        (wilkieAffineSliceConstituent hG hsmooth coeff constant
          piece.constituent).carrier := by
    rw [← wilkieAffineSlice_paddedPrefix_eq piece.hiddenArity_le]
    exact hnewPadded.1
  have hsection :=
    (mem_wilkieAffineSliceConstituent_carrier_iff_bounded_section
      hG hsmooth coeff constant piece.constituent x radial slice
        oldPieceParameters).mp hnewConstituent
  have holdPiece : realEuclideanAppend x oldParameters ∈ piece.carrier := by
    apply (mem_charbonnelParameterPad_append_iff
      piece.hiddenArity_le x oldParameters).mpr
    refine ⟨hsection.2.2.1, ?_⟩
    intro i hi
    have hindex : piece.hiddenArity + 2 + 1 ≤
        (Fin.succ (Fin.succ i) : Fin ((K + 2) + 1)).val := by
      simpa using Nat.add_le_add_right hi 2
    have hpositive := hnewPadded.2 (Fin.succ (Fin.succ i)) hindex
    simpa only [wilkiePrependTwoParameters_old] using hpositive
  refine ⟨hsection.1, hsection.2.1, ?_, hsection.2.2.2.1,
    hsection.2.2.2.2⟩
  exact ⟨piece, hpiece, holdPiece⟩

/-- Conversely, an old padded-family section point satisfying the radial and
affine-level inequalities belongs to the corresponding lifted section. -/
theorem mem_wilkieAffineSliceFiniteFamily_of_old_section
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (family : CharbonnelFiniteSardianFamily G order n K)
    (x : RealEuclidean n) (radial slice : ℝ)
    (oldParameters : RealEuclidean (K + 1))
    (hradial : 0 < radial) (hslice : 0 < slice)
    (hold : realEuclideanAppend x oldParameters ∈ family.carrier)
    (hradius : literalZeroVisibleRadialDenominator x ≤ radial⁻¹)
    (hlevel :
      (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ slice) :
    realEuclideanAppend x
        (wilkiePrependTwoParameters radial slice oldParameters) ∈
      (family.wilkieAffineSliceLift
        hG hsmooth coeff constant).carrier := by
  change ∃ liftedPiece ∈ family.constituents.map
      (CharbonnelPaddedSardianConstituent.wilkieAffineSliceLift
        hG hsmooth coeff constant),
      realEuclideanAppend x
          (wilkiePrependTwoParameters radial slice oldParameters) ∈
        liftedPiece.carrier
  change ∃ piece ∈ family.constituents,
      realEuclideanAppend x oldParameters ∈ piece.carrier at hold
  obtain ⟨piece, hpiece, holdPiece⟩ := hold
  let oldPieceParameters : RealEuclidean (piece.hiddenArity + 1) :=
    fun i ↦ oldParameters
      (Fin.castLE (Nat.succ_le_succ piece.hiddenArity_le) i)
  have holdPadded :=
    (mem_charbonnelParameterPad_append_iff
      piece.hiddenArity_le x oldParameters).mp holdPiece
  have hnewConstituent :
      realEuclideanAppend x
          (wilkiePrependTwoParameters radial slice oldPieceParameters) ∈
        (wilkieAffineSliceConstituent hG hsmooth coeff constant
          piece.constituent).carrier := by
    apply (mem_wilkieAffineSliceConstituent_carrier_iff_bounded_section
      hG hsmooth coeff constant piece.constituent x radial slice
        oldPieceParameters).mpr
    exact ⟨hradial, hslice, holdPadded.1, hradius, hlevel⟩
  refine ⟨
    CharbonnelPaddedSardianConstituent.wilkieAffineSliceLift
      hG hsmooth coeff constant piece,
    List.mem_map.mpr ⟨piece, hpiece, rfl⟩, ?_⟩
  apply (mem_charbonnelParameterPad_append_iff
    (Nat.add_le_add_right piece.hiddenArity_le 2) x
    (wilkiePrependTwoParameters radial slice oldParameters)).mpr
  constructor
  · rw [wilkieAffineSlice_paddedPrefix_eq piece.hiddenArity_le]
    exact hnewConstituent
  · intro i hi
    let oldIndex : Fin (K + 1) := ⟨i.val - 2, by omega⟩
    have holdIndex : piece.hiddenArity + 1 ≤ oldIndex.val := by
      dsimp only [oldIndex]
      omega
    have hpositive := holdPadded.2 oldIndex holdIndex
    have hiIndex : i = Fin.succ (Fin.succ oldIndex) := by
      have hiTwo : 2 ≤ i.val := by omega
      apply Fin.ext
      dsimp only [oldIndex]
      simp only [Fin.val_succ]
      omega
    rw [hiIndex]
    simpa only [wilkiePrependTwoParameters_old] using hpositive

/-- At a fixed positive radial parameter, sufficiently small old-section
error and affine slice level make every lifted-family section point close
to the actual closed target--hyperplane intersection. -/
theorem exists_wilkieAffineSliceFiniteFamily_below_scales
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (family : CharbonnelFiniteSardianFamily G order n K)
    (oldParameters : RealEuclidean (K + 1))
    (radial : ℝ) (hradial : 0 < radial)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaOld etaSlice : ℝ,
      0 < etaOld ∧ 0 < etaSlice ∧
        ∀ {slice : ℝ}, 0 < slice → slice ≤ etaSlice →
          (∀ x : RealEuclidean n,
            realEuclideanAppend x oldParameters ∈ family.carrier →
              ∃ y ∈ A, dist x y < etaOld) →
          ∀ x : RealEuclidean n,
            realEuclideanAppend x
                (wilkiePrependTwoParameters radial slice oldParameters) ∈
              (family.wilkieAffineSliceLift
                hG hsmooth coeff constant).carrier →
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta := by
  obtain ⟨etaOld, etaSlice, hetaOld, hetaSlice, hbelow⟩ :=
    exists_compactRadial_integerAffineSlice_below_scales
      A hA coeff constant radial hradial hdelta
  refine ⟨etaOld, etaSlice, hetaOld, hetaSlice, ?_⟩
  intro slice hslice hsliceLe hold x hnew
  have hsection := wilkieAffineSliceFiniteFamily_section_lifts_old
    hG hsmooth coeff constant family x radial slice oldParameters hnew
  exact hbelow x hsection.2.2.2.1 (hold x hsection.2.2.1)
    (hsection.2.2.2.2.trans hsliceLe)

end AbelFormalization
