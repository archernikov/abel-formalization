import AbelFormalization.CharbonnelSardianProjectionConstituentAlgebra

/-!
# The radial branch in Wilkie's one-coordinate Sardian projection

The radial choice in the algebraic constituent has an exact reciprocal
polynomial level.  Its first equations are the reindexed old tuple, while
the last equation bounds every hidden witness at a fixed positive level.
This file supplies the carrier and escape algebra; it does not supply the
regular-value or approximation arguments in Wilkie 3.10.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The radial denominator depends only on the enlarged hidden block. -/
theorem sardianProjectionRadialDenominator_append
    (n q : ℕ) (x : RealEuclidean n) (y : RealEuclidean (q + 1)) :
    sardianProjectionRadialDenominator n q (realEuclideanAppend x y) =
      1 + ∑ j : Fin (q + 1), (y j) ^ 2 := by
  simp only [sardianProjectionRadialDenominator,
    realEuclideanTakeRight_append]

/-- The radial equation is equivalently a positive-polynomial level with
the parameter inverted.  This equivalence also holds at zero because
inversion on the reals is involutive. -/
theorem sardianProjectionRadialReciprocal_append_eq_iff
    (n q : ℕ) (x : RealEuclidean n) (y : RealEuclidean (q + 1))
    (t : ℝ) :
    sardianProjectionRadialReciprocal n q
        (realEuclideanAppend x y) = t ↔
      1 + ∑ j : Fin (q + 1), (y j) ^ 2 = t⁻¹ := by
  rw [sardianProjectionRadialReciprocal,
    sardianProjectionRadialDenominator_append]
  constructor
  · intro h
    simpa only [inv_inv] using congrArg (fun z : ℝ ↦ z⁻¹) h
  · intro h
    rw [h, inv_inv]

/-- Exact radial carrier: the first `q + 1` equations are the old tuple
after moving one visible coordinate into the hidden block; the last is a
reciprocal positive-polynomial level. -/
theorem mem_sardianProjectionRadialBranch_carrier_iff
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (x : RealEuclidean n) (ε : RealEuclidean ((q + 1) + 1)) :
    realEuclideanAppend x ε ∈
        (sardianProjectionAlgebraicConstituent
          hG hsmooth hderiv hn old none).carrier ↔
      (∀ i, 0 < ε i) ∧
        ∃ y : RealEuclidean (q + 1),
          (∀ i : Fin (q + 1),
            sardianProjectionOldTuple old (realEuclideanAppend x y) i =
              ε i.castSucc) ∧
          1 + ∑ j : Fin (q + 1), (y j) ^ 2 =
            (ε (Fin.last (q + 1)))⁻¹ := by
  rw [mem_sardianProjectionAlgebraicConstituent_carrier_iff
    hG hsmooth hderiv hn old none x ε]
  simp only [sardianProjectionLastEquation]
  constructor
  · rintro ⟨hpos, y, hprefix, hlevel⟩
    exact ⟨hpos, y, hprefix,
      (sardianProjectionRadialReciprocal_append_eq_iff n q x y
        (ε (Fin.last (q + 1)))).mp hlevel⟩
  · rintro ⟨hpos, y, hprefix, hlevel⟩
    exact ⟨hpos, y, hprefix,
      (sardianProjectionRadialReciprocal_append_eq_iff n q x y
        (ε (Fin.last (q + 1)))).mpr hlevel⟩

/-- A radial value at least a positive level forces a uniform max-norm
bound on the enlarged hidden block. -/
theorem sardianProjectionRadialReciprocal_hidden_norm_le
    (n q : ℕ) (x : RealEuclidean n) (y : RealEuclidean (q + 1))
    (t : ℝ) (ht : 0 < t)
    (hlevel : t ≤ sardianProjectionRadialReciprocal n q
      (realEuclideanAppend x y)) :
    ‖y‖ ≤ Real.sqrt (t⁻¹ - 1) := by
  have hlevel' :
      t ≤ (1 + ∑ j : Fin (q + 1), (y j) ^ 2)⁻¹ := by
    simpa only [sardianProjectionRadialReciprocal,
      sardianProjectionRadialDenominator_append] using hlevel
  have hden :
      1 + ∑ j : Fin (q + 1), (y j) ^ 2 ≤ t⁻¹ :=
    le_inv_of_le_inv₀ ht hlevel'
  have hsum :
      (∑ j : Fin (q + 1), (y j) ^ 2) ≤ t⁻¹ - 1 := by
    linarith
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro j
  have hj : (y j) ^ 2 ≤
      ∑ i : Fin (q + 1), (y i) ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (y i))
      (Finset.mem_univ j)
  have hj' : (y j) ^ 2 ≤ t⁻¹ - 1 := hj.trans hsum
  simpa only [Real.norm_eq_abs] using Real.abs_le_sqrt hj'

/-- The same bound applies on the exact radial level. -/
theorem sardianProjectionRadialReciprocal_hidden_norm_le_of_eq
    (n q : ℕ) (x : RealEuclidean n) (y : RealEuclidean (q + 1))
    (t : ℝ) (ht : 0 < t)
    (hlevel : sardianProjectionRadialReciprocal n q
      (realEuclideanAppend x y) = t) :
    ‖y‖ ≤ Real.sqrt (t⁻¹ - 1) :=
  sardianProjectionRadialReciprocal_hidden_norm_le n q x y t ht
    hlevel.symm.le

/-- Conversely, witnesses whose hidden norm exceeds the level-dependent
radius have radial value strictly below that positive level. -/
theorem sardianProjectionRadialReciprocal_escape
    (n q : ℕ) (x : RealEuclidean n) (y : RealEuclidean (q + 1))
    (t : ℝ) (ht : 0 < t)
    (hlarge : Real.sqrt (t⁻¹ - 1) < ‖y‖) :
    sardianProjectionRadialReciprocal n q
      (realEuclideanAppend x y) < t := by
  by_contra hnot
  have hlevel : t ≤ sardianProjectionRadialReciprocal n q
      (realEuclideanAppend x y) := le_of_not_gt hnot
  have hbound :=
    sardianProjectionRadialReciprocal_hidden_norm_le n q x y t ht hlevel
  exact (lt_irrefl _) (hlarge.trans_le hbound)

/-- Every member of the radial constituent has an old-tuple witness whose
hidden block satisfies the level-dependent escape bound. -/
theorem mem_sardianProjectionRadialBranch_carrier_iff_bounded
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (x : RealEuclidean n) (ε : RealEuclidean ((q + 1) + 1)) :
    realEuclideanAppend x ε ∈
        (sardianProjectionAlgebraicConstituent
          hG hsmooth hderiv hn old none).carrier ↔
      (∀ i, 0 < ε i) ∧
        ∃ y : RealEuclidean (q + 1),
          (∀ i : Fin (q + 1),
            sardianProjectionOldTuple old (realEuclideanAppend x y) i =
              ε i.castSucc) ∧
          (1 + ∑ j : Fin (q + 1), (y j) ^ 2 =
            (ε (Fin.last (q + 1)))⁻¹) ∧
          ‖y‖ ≤ Real.sqrt ((ε (Fin.last (q + 1)))⁻¹ - 1) := by
  rw [mem_sardianProjectionRadialBranch_carrier_iff
    hG hsmooth hderiv hn old x ε]
  constructor
  · rintro ⟨hpos, y, hprefix, hlevel⟩
    have hrad : sardianProjectionRadialReciprocal n q
        (realEuclideanAppend x y) = ε (Fin.last (q + 1)) :=
      (sardianProjectionRadialReciprocal_append_eq_iff n q x y
        (ε (Fin.last (q + 1)))).mpr hlevel
    exact ⟨hpos, y, hprefix, hlevel,
      sardianProjectionRadialReciprocal_hidden_norm_le_of_eq
        n q x y _ (hpos _) hrad⟩
  · rintro ⟨hpos, y, hprefix, hlevel, _⟩
    exact ⟨hpos, y, hprefix, hlevel⟩

end AbelFormalization
