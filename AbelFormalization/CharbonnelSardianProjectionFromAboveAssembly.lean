import AbelFormalization.CharbonnelSardianProjectionFromBelowAssembly
import AbelFormalization.CharbonnelSardianProjectionCase2Bridge

/-!
# Assemble the from-above modulus in Wilkie's Sardian projection step

After the old positive parameter prefix is fixed, the geometric part of
Wilkie 3.10 produces a positive interval of admissible final levels which
works uniformly for the bounded part of the projected boundary.  This file
performs the remaining dependent-choice bookkeeping: it selects one interval
bound for every old prefix, uses a harmless unit bound away from the old
modulus, and constructs the successor `CharbonnelModulus`.

Combining this successor modulus with the already proved prefix-section lift
gives a full one-coordinate Sardian approximation certificate.  Thus the only
premise left in the final theorem below is the geometric uniform small-level
statement itself; no modulus or carrier compatibility premise remains.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelModulus

/-- Uniform small final levels for each prefix bounded by an old Sardian
modulus can be selected into one successor modulus. -/
theorem exists_step_approximatesFromAboveOnBoundedSets
    {n K : ℕ}
    (oldModulus : CharbonnelModulus (K + 1))
    (A : Set (RealEuclidean n))
    (newT : Set (RealEuclidean (n + ((K + 1) + 1))))
    (hlevels : ∀ pfx : RealEuclidean ((K + 1) + 1),
      oldModulus.IsBounded pfx →
        ∃ eta : ℝ, 0 < eta ∧
          ∀ t : ℝ, 0 < t → t < eta →
            ∀ x ∈ A, ‖x‖ < (pfx 0)⁻¹ →
              ∃ y : RealEuclidean n,
                dist x y < pfx 0 ∧
                  realEuclideanAppend y
                    (charbonnelAppendLastParameter
                      (parameterTail pfx) t) ∈ newT) :
    ∃ newModulus : CharbonnelModulus ((K + 1) + 1),
      (∀ epsilon : RealEuclidean (((K + 1) + 1) + 1),
        newModulus.IsBounded epsilon →
          oldModulus.IsBounded (Fin.init epsilon)) ∧
      ApproximatesFromAboveOnBoundedSets newModulus A newT := by
  classical
  let lastBound : RealEuclidean ((K + 1) + 1) → ℝ :=
    fun pfx ↦
      if hpfx : oldModulus.IsBounded pfx then
        Classical.choose (hlevels pfx hpfx)
      else 1
  have hlastBoundPos : ∀ pfx : RealEuclidean ((K + 1) + 1),
      (∀ i, 0 < pfx i) → 0 < lastBound pfx := by
    intro pfx _hpositive
    by_cases hpfx : oldModulus.IsBounded pfx
    · rw [show lastBound pfx =
          Classical.choose (hlevels pfx hpfx) by
        simp only [lastBound, dif_pos hpfx]]
      exact (Classical.choose_spec (hlevels pfx hpfx)).1
    · simp only [lastBound, dif_neg hpfx, zero_lt_one]
  let newModulus : CharbonnelModulus ((K + 1) + 1) :=
    .step oldModulus lastBound hlastBoundPos
  refine ⟨newModulus, ?_, ?_⟩
  · intro epsilon hbounded
    exact hbounded.1
  · intro epsilon hbounded x hxA hxnorm
    have hprefix : oldModulus.IsBounded (Fin.init epsilon) :=
      hbounded.1
    have hlastLt :
        epsilon (Fin.last ((K + 1) + 1)) <
          Classical.choose (hlevels (Fin.init epsilon) hprefix) := by
      have h := hbounded.2.2
      simpa only [newModulus, lastBound, dif_pos hprefix] using h
    have hlastPos : 0 < epsilon (Fin.last ((K + 1) + 1)) :=
      hbounded.2.1
    have hzero : Fin.init epsilon 0 = epsilon 0 := rfl
    obtain ⟨y, hxy, hy⟩ :=
      (Classical.choose_spec (hlevels (Fin.init epsilon) hprefix)).2
        (epsilon (Fin.last ((K + 1) + 1))) hlastPos hlastLt
        x hxA (by simpa only [hzero] using hxnorm)
    refine ⟨y, ?_, ?_⟩
    · simpa only [hzero] using hxy
    · simpa only [charbonnelParameterTail_eq_appendLastParameter_init_last]
        using hy

end CharbonnelModulus

/-- A refined old-prefix modulus can be used in the projection constructor.
This is the source-shaped form needed in Wilkie 3.10, where the old modulus
is first tightened to avoid all singular-value sets and to support a second
evaluation at the boundary-separation scale. -/
noncomputable def
    sardianProjectionCertificate_of_refinedUniformBoundarySmallLevels
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
    (hlevels :
      ∀ pfx : RealEuclidean ((old.commonHiddenArity + 1) + 1),
        prefixModulus.IsBounded pfx →
          ∃ eta : ℝ, 0 < eta ∧
            ∀ t : ℝ, 0 < t → t < eta →
              ∀ x ∈ frontier
                  (closure (realEuclideanExistentialProjection A)),
                ‖x‖ < (pfx 0)⁻¹ →
                  ∃ y : RealEuclidean n,
                    dist x y < pfx 0 ∧
                      realEuclideanAppend y
                        (charbonnelAppendLastParameter
                          (CharbonnelModulus.parameterTail pfx) t) ∈
                        (sardianProjectionAlgebraicPaddedFamily
                          hG hsmooth hderiv hn old.family).carrier) :
    CharbonnelSardianApproximationCertificate
      G order n (realEuclideanExistentialProjection A) := by
  let newFamily := sardianProjectionAlgebraicPaddedFamily
    hG hsmooth hderiv hn old.family
  let hmodulus :=
    CharbonnelModulus.exists_step_approximatesFromAboveOnBoundedSets
      prefixModulus
      (frontier (closure (realEuclideanExistentialProjection A)))
      newFamily.carrier hlevels
  let newModulus := Classical.choose hmodulus
  have hmodulusSpec := Classical.choose_spec hmodulus
  have hprefixBound : ∀ epsilon :
      RealEuclidean (((old.commonHiddenArity + 1) + 1) + 1),
      newModulus.IsBounded epsilon →
        old.modulus.IsBounded (Fin.init epsilon) := by
    intro epsilon hepsilon
    exact hrefines _ (hmodulusSpec.1 epsilon hepsilon)
  have habove := hmodulusSpec.2
  have hbelow : CharbonnelModulus.ApproximatesFromBelow
      newModulus newFamily.carrier
        (closure (realEuclideanExistentialProjection A)) := by
    apply approximatesFromBelow_projection_of_prefixSection
      A old.family.carrier newFamily.carrier old.modulus newModulus
        hprefixBound
    · intro epsilon x hnew
      exact sardianProjectionAlgebraicPaddedFamily_prefixSectionLift
        hG hsmooth hderiv hn old.family epsilon x hnew
    · exact old.approximates.approximatesFromBelow
  exact
    { order_pos := horder
      commonHiddenArity := old.commonHiddenArity + 1
      family := newFamily
      modulus := newModulus
      approximates := ⟨hbelow, habove⟩ }

/-- A uniform geometric small-level theorem for the projected boundary
constructs the complete one-coordinate Sardian certificate.  The old
from-below clause and all mixed-depth carrier algebra are discharged by the
existing projection assembly. -/
noncomputable def
    sardianProjectionCertificate_of_uniformBoundarySmallLevels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n : ℕ} (horder : 0 < order) (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (hlevels :
      ∀ pfx : RealEuclidean ((old.commonHiddenArity + 1) + 1),
        old.modulus.IsBounded pfx →
          ∃ eta : ℝ, 0 < eta ∧
            ∀ t : ℝ, 0 < t → t < eta →
              ∀ x ∈ frontier
                  (closure (realEuclideanExistentialProjection A)),
                ‖x‖ < (pfx 0)⁻¹ →
                  ∃ y : RealEuclidean n,
                    dist x y < pfx 0 ∧
                      realEuclideanAppend y
                        (charbonnelAppendLastParameter
                          (CharbonnelModulus.parameterTail pfx) t) ∈
                        (sardianProjectionAlgebraicPaddedFamily
                          hG hsmooth hderiv hn old.family).carrier) :
    CharbonnelSardianApproximationCertificate
      G order n (realEuclideanExistentialProjection A) := by
  exact sardianProjectionCertificate_of_refinedUniformBoundarySmallLevels
    hG hsmooth hderiv horder hn old old.modulus
      (CharbonnelModulus.refines_refl old.modulus) hlevels

end AbelFormalization
