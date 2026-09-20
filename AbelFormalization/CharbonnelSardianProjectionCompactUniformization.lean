import AbelFormalization.CharbonnelSardianProjectionFromAboveAssembly

/-!
# Compact uniformization in Wilkie's Sardian projection step

The local geometric argument in Wilkie 3.10 produces, near each point of a
bounded piece of the projected boundary, a positive interval of admissible
last parameters.  Compactness turns these pointwise intervals into one
interval that works on the whole bounded boundary piece.  This file proves
that finite-cover step and connects its local formulation directly to the
successor-modulus assembly.

No regular-value or local-fiber assertion is assumed implicitly here.  The
final constructor takes precisely the pointwise local small-level statement
which remains to be supplied by the Sard/Case-2 geometry.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## An abstract compact finite-cover lemma -/

/-- Positive level intervals which work locally on a compact set have one
common positive subinterval which works everywhere on that set. -/
theorem exists_uniform_positive_levels_of_compact_local
    {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (P : ℝ → X → Prop)
    (hlocal : ∀ x ∈ K,
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∃ eta : ℝ, 0 < eta ∧
          ∀ t : ℝ, 0 < t → t < eta →
            ∀ z ∈ K ∩ U, P t z) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : ℝ, 0 < t → t < eta → ∀ x ∈ K, P t x := by
  classical
  have hlocal' : ∀ x : K,
      ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧
        ∃ eta : ℝ, 0 < eta ∧
          ∀ t : ℝ, 0 < t → t < eta →
            ∀ z ∈ K ∩ U, P t z := by
    intro x
    exact hlocal x x.property
  choose U hUopen hxU eta heta hworks using hlocal'
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨F, hFcover⟩ :=
    hK.elim_finite_subcover U hUopen hcover
  by_cases hF : F.Nonempty
  · let common : ℝ := F.inf' hF eta
    have hcommon : 0 < common := by
      apply (Finset.lt_inf'_iff hF (f := eta)).mpr
      intro x hxF
      exact heta x
    refine ⟨common, hcommon, ?_⟩
    intro t ht htc x hxK
    obtain ⟨c, hcF, hxc⟩ := Set.mem_iUnion₂.mp (hFcover hxK)
    apply hworks c t ht
    · exact htc.trans_le (Finset.inf'_le eta hcF)
    · exact ⟨hxK, hxc⟩
  · have hKempty : K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hxK
      have hxcover : x ∈ ⋃ c ∈ F, U c := hFcover hxK
      have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      simpa [hFempty] using hxcover
    refine ⟨1, zero_lt_one, ?_⟩
    intro t _ht _htone x hxK
    rw [hKempty] at hxK
    exact hxK.elim

/-! ## Bounded pieces of the projected boundary -/

/-- The part of the closed projected boundary inside a closed ball. -/
def sardianProjectionBoundaryTruncation
    {n : ℕ} (A : Set (RealEuclidean (n + 1))) (radius : ℝ) :
    Set (RealEuclidean n) :=
  frontier (closure (realEuclideanExistentialProjection A)) ∩
    Metric.closedBall 0 radius

/-- Every bounded projected-boundary truncation is compact. -/
theorem isCompact_sardianProjectionBoundaryTruncation
    {n : ℕ} (A : Set (RealEuclidean (n + 1))) (radius : ℝ) :
    IsCompact (sardianProjectionBoundaryTruncation A radius) := by
  exact (isCompact_closedBall (0 : RealEuclidean n) radius).inter_left
    isClosed_frontier

/-- Pointwise local small-level intervals on a bounded projected-boundary
truncation has one interval valid at every point of that truncation. -/
theorem exists_uniform_sardianProjectionBoundary_smallLevels_of_local
    {n k : ℕ} (A : Set (RealEuclidean (n + 1)))
    (T : Set (RealEuclidean (n + ((k + 1) + 1))))
    (pfx : RealEuclidean ((k + 1) + 1))
    (hlocal : ∀ x ∈ sardianProjectionBoundaryTruncation A (pfx 0)⁻¹,
      ∃ U : Set (RealEuclidean n), IsOpen U ∧ x ∈ U ∧
        ∃ eta : ℝ, 0 < eta ∧
          ∀ t : ℝ, 0 < t → t < eta →
            ∀ z ∈ sardianProjectionBoundaryTruncation A (pfx 0)⁻¹ ∩ U,
              ∃ y : RealEuclidean n,
                dist z y < pfx 0 ∧
                  realEuclideanAppend y
                    (charbonnelAppendLastParameter
                      (CharbonnelModulus.parameterTail pfx) t) ∈ T) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : ℝ, 0 < t → t < eta →
        ∀ x ∈ frontier
            (closure (realEuclideanExistentialProjection A)),
          ‖x‖ < (pfx 0)⁻¹ →
            ∃ y : RealEuclidean n,
              dist x y < pfx 0 ∧
                realEuclideanAppend y
                  (charbonnelAppendLastParameter
                    (CharbonnelModulus.parameterTail pfx) t) ∈ T := by
  let K := sardianProjectionBoundaryTruncation A (pfx 0)⁻¹
  let P : ℝ → RealEuclidean n → Prop := fun t z ↦
    ∃ y : RealEuclidean n,
      dist z y < pfx 0 ∧
        realEuclideanAppend y
          (charbonnelAppendLastParameter
            (CharbonnelModulus.parameterTail pfx) t) ∈ T
  obtain ⟨eta, heta, hglobal⟩ :=
    exists_uniform_positive_levels_of_compact_local K
      (isCompact_sardianProjectionBoundaryTruncation A (pfx 0)⁻¹)
      P hlocal
  refine ⟨eta, heta, ?_⟩
  intro t ht hteta x hxBoundary hxNorm
  apply hglobal t ht hteta x
  refine ⟨hxBoundary, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hxNorm.le

/-! ## Direct connection to the projection certificate -/

/-- A refined old-prefix modulus together with local small-level geometry at
each point of every bounded projected-boundary truncation constructs the
complete one-coordinate projection certificate.  Compactness and the final
successor-modulus choice are both discharged inside this definition. -/
noncomputable def
    sardianProjectionCertificate_of_refinedLocalBoundarySmallLevels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n : ℕ} (horder : 0 < order) (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (prefixModulus : CharbonnelModulus (old.commonHiddenArity + 1))
    (hrefines : prefixModulus.Refines old.modulus)
    (hlocal :
      ∀ pfx : RealEuclidean ((old.commonHiddenArity + 1) + 1),
        prefixModulus.IsBounded pfx →
          ∀ x ∈ sardianProjectionBoundaryTruncation A (pfx 0)⁻¹,
            ∃ U : Set (RealEuclidean n), IsOpen U ∧ x ∈ U ∧
              ∃ eta : ℝ, 0 < eta ∧
                ∀ t : ℝ, 0 < t → t < eta →
                  ∀ z ∈
                      sardianProjectionBoundaryTruncation A (pfx 0)⁻¹ ∩ U,
                    ∃ y : RealEuclidean n,
                      dist z y < pfx 0 ∧
                        realEuclideanAppend y
                          (charbonnelAppendLastParameter
                            (CharbonnelModulus.parameterTail pfx) t) ∈
                          (sardianProjectionAlgebraicPaddedFamily
                            hG hsmooth hderiv hn old.family).carrier) :
    CharbonnelSardianApproximationCertificate
      G order n (realEuclideanExistentialProjection A) := by
  apply sardianProjectionCertificate_of_refinedUniformBoundarySmallLevels
    hG hsmooth hderiv horder hn old prefixModulus hrefines
  intro pfx hpfx
  exact exists_uniform_sardianProjectionBoundary_smallLevels_of_local
    A
    (sardianProjectionAlgebraicPaddedFamily
      hG hsmooth hderiv hn old.family).carrier
    pfx (hlocal pfx hpfx)

/-- Specialization of the compact local-to-global constructor with the old
modulus itself as prefix modulus. -/
noncomputable def
    sardianProjectionCertificate_of_localBoundarySmallLevels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n : ℕ} (horder : 0 < order) (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (hlocal :
      ∀ pfx : RealEuclidean ((old.commonHiddenArity + 1) + 1),
        old.modulus.IsBounded pfx →
          ∀ x ∈ sardianProjectionBoundaryTruncation A (pfx 0)⁻¹,
            ∃ U : Set (RealEuclidean n), IsOpen U ∧ x ∈ U ∧
              ∃ eta : ℝ, 0 < eta ∧
                ∀ t : ℝ, 0 < t → t < eta →
                  ∀ z ∈
                      sardianProjectionBoundaryTruncation A (pfx 0)⁻¹ ∩ U,
                    ∃ y : RealEuclidean n,
                      dist z y < pfx 0 ∧
                        realEuclideanAppend y
                          (charbonnelAppendLastParameter
                            (CharbonnelModulus.parameterTail pfx) t) ∈
                          (sardianProjectionAlgebraicPaddedFamily
                            hG hsmooth hderiv hn old.family).carrier) :
    CharbonnelSardianApproximationCertificate
      G order n (realEuclideanExistentialProjection A) :=
  sardianProjectionCertificate_of_refinedLocalBoundarySmallLevels
    hG hsmooth hderiv horder hn old old.modulus
      (CharbonnelModulus.refines_refl old.modulus) hlocal

end AbelFormalization
