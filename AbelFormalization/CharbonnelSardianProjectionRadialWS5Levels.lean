import AbelFormalization.CharbonnelSardianProjectionRadialValueImage
import AbelFormalization.UnaryNearZeroInterval

/-!
# Small radial levels from WS5's unary consequence

Once the radial value image is in the literal-zero Charbonnel closure and
UFF supplies WS5, its finite unary decomposition turns accumulation at zero
into a full interval of small positive values.  Accumulation itself is an
explicit premise here; the finite-cover localization in Wilkie 3.10 must
establish it for a suitable fixed visible ball.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The scalar radial range has every sufficiently small positive level,
conditional on zero lying in its closure. -/
theorem sardianProjectionRadialValueImage_all_small_levels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hU : U ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (e : RealEuclidean (q + 1))
    (hzero : (0 : ℝ) ∈ closure
      (realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old U e))) :
    ∃ η : ℝ, 0 < η ∧
      ∀ t : ℝ, 0 < t → t < η →
        ∃ v ∈ sardianProjectionOldTupleFiber old U e,
          sardianProjectionRadialReciprocal n q v = t := by
  let R := realEuclideanOneCoordinateImage
    (sardianProjectionRadialValueImage old U e)
  have hdecomposition : UnaryPieceDecomposable R :=
    sardianProjectionRadialValueImage_unaryPieceDecomposable
      hG hsmooth hUFF hn old U hU e
  have hpositive : R ⊆ Ioi (0 : ℝ) := by
    intro t ht
    obtain ⟨z, hz, hzt⟩ := ht
    have hzpos := sardianProjectionRadialValueImage_pos old U e hz
    change 0 < t
    rw [← hzt]
    exact hzpos
  obtain ⟨η, hηpos, hinterval⟩ :=
    hdecomposition.exists_Ioo_zero_subset hpositive hzero
  refine ⟨η, hηpos, ?_⟩
  intro t htpos hteta
  have htR : t ∈ R := hinterval ⟨htpos, hteta⟩
  obtain ⟨z, hz, hzt⟩ := htR
  obtain ⟨v, hvFiber, hzLevel⟩ := hz
  exact ⟨v, hvFiber, hzLevel.symm.trans hzt⟩

/-- The same WS5 interval supplies actual members of the projected finite
choice family at every sufficiently small positive final parameter.  The
fixed old parameter block is assumed positive, as required by its carrier. -/
theorem sardianProjectionRadialValueImage_projectedFamily_all_small_levels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hU : U ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hzero : (0 : ℝ) ∈ closure
      (realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old U e))) :
    ∃ η : ℝ, 0 < η ∧
      ∀ t : ℝ, 0 < t → t < η →
        ∃ x ∈ U,
          realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
            (sardianProjectionAlgebraicFamily
              hG hsmooth hderiv hn old).carrier := by
  obtain ⟨η, hηpos, hlevels⟩ :=
    sardianProjectionRadialValueImage_all_small_levels
      hG hsmooth hUFF hn old U hU e hzero
  refine ⟨η, hηpos, ?_⟩
  intro t htpos hteta
  obtain ⟨v, hvFiber, hradialLevel⟩ := hlevels t htpos hteta
  refine ⟨realEuclideanTakeLeft v, hvFiber.1, ?_⟩
  exact mem_sardianProjectionAlgebraicFamily_of_oldTupleFiber_level
    hG hsmooth hderiv hn old e hepos t htpos none v
    hvFiber.2 hradialLevel

end AbelFormalization
