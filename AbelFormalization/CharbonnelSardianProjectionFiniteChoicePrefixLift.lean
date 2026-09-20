import AbelFormalization.CharbonnelSardianProjectionPrefixSectionLift
import AbelFormalization.CharbonnelSardianCertificatePadding

/-!
# Finite-choice section lift for the Sardian projection constructor

Every member of the finite radial/minor choice carrier has a member of one
specific choice carrier as witness.  The previously established one-choice
section lift then recovers an old section after the last parameter is deleted.
The second constructor combines finitely many old constituents of one exact
hidden depth; it retains the actual old constituent as a finite-family witness.

This file does not construct the analytic approximation modulus or an upper
frontier approximation.  In particular, the exact-depth list is not a family
of constituents padded from differing hidden depths.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Extract the particular appended radial-or-minor equation from membership
in the finite choice family for one exact-depth old constituent. -/
theorem mem_sardianProjectionAlgebraicFamily_carrier_iff_exists_choice
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    {v : RealEuclidean (n + ((q + 1) + 1))} :
    v ∈ (sardianProjectionAlgebraicFamily
        hG hsmooth hderiv hn old).carrier ↔
      ∃ choice : SardianProjectionLastEquationChoice n q,
        v ∈ (sardianProjectionAlgebraicConstituent
          hG hsmooth hderiv hn old choice).carrier := by
  classical
  constructor
  · intro hv
    change ∃ piece ∈
      (Finset.univ : Finset (SardianProjectionLastEquationChoice n q)).toList.map
        (fun choice ↦
          CharbonnelPaddedSardianConstituent.ofConstituent
            (Nat.le_refl (q + 1))
            (sardianProjectionAlgebraicConstituent
              hG hsmooth hderiv hn old choice)),
      v ∈ piece.carrier at hv
    obtain ⟨piece, hpiece, hcarrier⟩ := hv
    obtain ⟨choice, _hchoice, rfl⟩ := List.mem_map.mp hpiece
    refine ⟨choice, ?_⟩
    simpa only [CharbonnelPaddedSardianConstituent.carrier_ofConstituent,
      charbonnelParameterPad_refl] using hcarrier
  · rintro ⟨choice, hchoice⟩
    change ∃ piece ∈
      (Finset.univ : Finset (SardianProjectionLastEquationChoice n q)).toList.map
        (fun choice ↦
          CharbonnelPaddedSardianConstituent.ofConstituent
            (Nat.le_refl (q + 1))
            (sardianProjectionAlgebraicConstituent
              hG hsmooth hderiv hn old choice)),
      v ∈ piece.carrier
    refine ⟨CharbonnelPaddedSardianConstituent.ofConstituent
      (Nat.le_refl (q + 1))
      (sardianProjectionAlgebraicConstituent
        hG hsmooth hderiv hn old choice), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨choice, by simp, rfl⟩
    · simpa only [CharbonnelPaddedSardianConstituent.carrier_ofConstituent,
        charbonnelParameterPad_refl] using hchoice

/-- The finite choice family has the exact old section after the new final
parameter is deleted.  This is the `hsection` premise needed by the generic
from-below reduction for an exact-depth old constituent. -/
theorem sardianProjectionAlgebraicFamily_prefixSectionLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (ε : RealEuclidean (((q + 1) + 1) + 1))
    (x : RealEuclidean n)
    (hnew : realEuclideanAppend x
        (CharbonnelModulus.parameterTail ε) ∈
      (sardianProjectionAlgebraicFamily
        hG hsmooth hderiv hn old).carrier) :
    ∃ erased : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x erased)
        (CharbonnelModulus.parameterTail
          (sardianProjectionParameterPrefix ε)) ∈ old.carrier := by
  obtain ⟨choice, hchoice⟩ :=
    (mem_sardianProjectionAlgebraicFamily_carrier_iff_exists_choice
      hG hsmooth hderiv hn old).mp hnew
  exact sardianProjectionAlgebraicConstituent_prefixSectionLift
    hG hsmooth hderiv hn old choice ε x hchoice

/-- Combine the projected choice families of a finite list of old
constituents, all at the same exact hidden depth `q`.  The old order is one
higher than the new order, as required by a single-coordinate projection. -/
def sardianProjectionAlgebraicFamilyOfExactList
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (oldList : List (CharbonnelSardianConstituent G (order + 1) (n + 1) q)) :
    CharbonnelFiniteSardianFamily G order n (q + 1) :=
  { visible_pos := hn
    constituents := oldList.flatMap
      (fun old ↦
        (sardianProjectionAlgebraicFamily
          hG hsmooth hderiv hn old).constituents) }

/-- A member of the combined finite family retains an old constituent in
the input list as its witness. -/
theorem mem_sardianProjectionAlgebraicFamilyOfExactList_carrier_iff
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (oldList : List (CharbonnelSardianConstituent G (order + 1) (n + 1) q))
    {v : RealEuclidean (n + ((q + 1) + 1))} :
    v ∈ (sardianProjectionAlgebraicFamilyOfExactList
        hG hsmooth hderiv hn oldList).carrier ↔
      ∃ old ∈ oldList,
        v ∈ (sardianProjectionAlgebraicFamily
          hG hsmooth hderiv hn old).carrier := by
  constructor
  · intro hv
    change ∃ piece ∈ oldList.flatMap
      (fun old ↦
        (sardianProjectionAlgebraicFamily
          hG hsmooth hderiv hn old).constituents),
      v ∈ piece.carrier at hv
    obtain ⟨piece, hpiece, hcarrier⟩ := hv
    obtain ⟨old, hold, hchoicePiece⟩ := List.mem_flatMap.mp hpiece
    exact ⟨old, hold, piece, hchoicePiece, hcarrier⟩
  · rintro ⟨old, hold, piece, hpiece, hcarrier⟩
    change ∃ piece ∈ oldList.flatMap
      (fun old ↦
        (sardianProjectionAlgebraicFamily
          hG hsmooth hderiv hn old).constituents),
      v ∈ piece.carrier
    exact ⟨piece, List.mem_flatMap.mpr ⟨old, hold, hpiece⟩, hcarrier⟩

/-- Finite-list version of the prefix section lift.  The conclusion names
the old list member, so it can be used with an old finite-family carrier. -/
theorem sardianProjectionAlgebraicFamilyOfExactList_prefixSectionLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (oldList : List (CharbonnelSardianConstituent G (order + 1) (n + 1) q))
    (ε : RealEuclidean (((q + 1) + 1) + 1))
    (x : RealEuclidean n)
    (hnew : realEuclideanAppend x
        (CharbonnelModulus.parameterTail ε) ∈
      (sardianProjectionAlgebraicFamilyOfExactList
        hG hsmooth hderiv hn oldList).carrier) :
    ∃ old ∈ oldList, ∃ erased : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x erased)
        (CharbonnelModulus.parameterTail
          (sardianProjectionParameterPrefix ε)) ∈ old.carrier := by
  obtain ⟨old, hold, hfamily⟩ :=
    (mem_sardianProjectionAlgebraicFamilyOfExactList_carrier_iff
      hG hsmooth hderiv hn oldList).mp hnew
  obtain ⟨erased, hsection⟩ :=
    sardianProjectionAlgebraicFamily_prefixSectionLift
      hG hsmooth hderiv hn old ε x hfamily
  exact ⟨old, hold, erased, hsection⟩

end AbelFormalization
