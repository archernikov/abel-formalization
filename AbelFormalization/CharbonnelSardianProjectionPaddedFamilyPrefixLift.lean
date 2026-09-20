import AbelFormalization.CharbonnelSardianProjectionFiniteChoicePrefixLift
import AbelFormalization.CharbonnelSardianExactDepthExtension

/-!
# Prefix section lift for a mixed-depth finite Sardian family

The old family may contain constituents with individual hidden depths below
its common depth `K`.  Before adding a radial or minor equation, each old
constituent is represented at exact hidden depth `K` by making its unused
positive parameters equal to new hidden-coordinate equations.  All projected
choices therefore put their appended equation at the same final parameter
index `K + 1`.  Deleting that final parameter recovers a section of the
original old padded family, with its exact list member retained as witness.

This is carrier algebra only.  A bounded approximation modulus, regular
values, and the upper boundary clause of Wilkie 3.10 remain separate.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Turn every old padded constituent into an exact-`K` constituent with
the same carrier at the common family depth. -/
def sardianProjectionOldExactDepthList
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (oldFamily : CharbonnelFiniteSardianFamily G (order + 1) (n + 1) K) :
    List (CharbonnelSardianConstituent G (order + 1) (n + 1) K) :=
  oldFamily.constituents.map
    (fun piece ↦
      sardianConstituentExactDepthExtension
        hG hsmooth piece.hiddenArity_le piece.constituent)

/-- All projected radial/minor choices, after normalizing each old list
member to the same exact hidden depth. -/
def sardianProjectionAlgebraicPaddedFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n K : ℕ} (hn : 0 < n)
    (oldFamily : CharbonnelFiniteSardianFamily G (order + 1) (n + 1) K) :
    CharbonnelFiniteSardianFamily G order n (K + 1) :=
  sardianProjectionAlgebraicFamilyOfExactList
    hG hsmooth hderiv hn
    (sardianProjectionOldExactDepthList hG hsmooth oldFamily)

/-- Finite mixed-depth `hsection`: a new point in the normalized projected
family comes from one actual constituent of the old padded family. -/
theorem sardianProjectionAlgebraicPaddedFamily_prefixSectionLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n K : ℕ} (hn : 0 < n)
    (oldFamily : CharbonnelFiniteSardianFamily G (order + 1) (n + 1) K)
    (ε : RealEuclidean (((K + 1) + 1) + 1))
    (x : RealEuclidean n)
    (hnew : realEuclideanAppend x
        (CharbonnelModulus.parameterTail ε) ∈
      (sardianProjectionAlgebraicPaddedFamily
        hG hsmooth hderiv hn oldFamily).carrier) :
    ∃ erased : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x erased)
        (CharbonnelModulus.parameterTail
          (sardianProjectionParameterPrefix ε)) ∈ oldFamily.carrier := by
  obtain ⟨exactOld, hexactOld, erased, hsection⟩ :=
    sardianProjectionAlgebraicFamilyOfExactList_prefixSectionLift
      hG hsmooth hderiv hn
      (sardianProjectionOldExactDepthList hG hsmooth oldFamily)
      ε x hnew
  change exactOld ∈ oldFamily.constituents.map
    (fun piece ↦
      sardianConstituentExactDepthExtension
        hG hsmooth piece.hiddenArity_le piece.constituent) at hexactOld
  obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hexactOld
  have holdPiece :
      realEuclideanAppend (realEuclideanAppend x erased)
        (CharbonnelModulus.parameterTail
          (sardianProjectionParameterPrefix ε)) ∈ piece.carrier := by
    rw [sardianConstituentExactDepthExtension_carrier_eq_pad
      hG hsmooth piece.hiddenArity_le piece.constituent] at hsection
    change realEuclideanAppend (realEuclideanAppend x erased)
      (CharbonnelModulus.parameterTail
        (sardianProjectionParameterPrefix ε)) ∈
          charbonnelParameterPad
            piece.hiddenArity_le piece.constituent.carrier
    exact hsection
  exact ⟨erased, piece, hpiece, holdPiece⟩

/-- The mixed-depth projected carrier is still algebraically a projected
zero set; this does not assert Sardian approximation. -/
theorem sardianProjectionAlgebraicPaddedFamily_isProjectedZeroSet
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n K : ℕ} (hn : 0 < n)
    (oldFamily : CharbonnelFiniteSardianFamily G (order + 1) (n + 1) K) :
    IsProjectedZeroSet G
      (sardianProjectionAlgebraicPaddedFamily
        hG hsmooth hderiv hn oldFamily).carrier :=
  (sardianProjectionAlgebraicPaddedFamily
    hG hsmooth hderiv hn oldFamily).carrier_isProjectedZeroSet hG

end AbelFormalization
