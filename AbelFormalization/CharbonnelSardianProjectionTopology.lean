import AbelFormalization.CharbonnelSardianRankConstructorReduction
import AbelFormalization.ProjectedFiberComponents

/-!
# The topological projection step in Wilkie 3.10

In the positive-hidden-arity constructor, the new lower approximation is
compared with the closure of the existential projection of the old target.
The needed target-set bridge is purely topological: continuous visible
projection maps `closure A` into `closure (projection A)`.  This file proves
that bridge without imposing any differentiability or regular-value premise.

The construction of the Sardian family and the boundary approximation are
the separate analytic work in Lemma 3.10.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Existential projection is the image of the visible-coordinate map. -/
theorem realEuclideanExistentialProjection_eq_takeLeft_image
    {n q : ℕ} (A : Set (RealEuclidean (n + q))) :
    realEuclideanExistentialProjection A = realEuclideanTakeLeft '' A := by
  ext x
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨realEuclideanAppend x y, hxy,
      realEuclideanTakeLeft_append x y⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨realEuclideanTakeRight v, ?_⟩
    simpa only [realEuclideanAppend_take] using hv

/-- The closure of the old target projects inside the closure of the new
target.  This is the target-set inclusion used by the `from below` half of
Wilkie's projection constructor. -/
theorem realEuclideanExistentialProjection_closure_subset_closure
    {n q : ℕ} (A : Set (RealEuclidean (n + q))) :
    realEuclideanExistentialProjection (closure A) ⊆
      closure (realEuclideanExistentialProjection A) := by
  rw [realEuclideanExistentialProjection_eq_takeLeft_image,
    realEuclideanExistentialProjection_eq_takeLeft_image]
  change (realEuclideanTakeLeftContinuousLinearMap n q) '' closure A ⊆
    closure ((realEuclideanTakeLeftContinuousLinearMap n q) '' A)
  exact image_closure_subset_closure_image
    (realEuclideanTakeLeftContinuousLinearMap n q).continuous

/-- Closing the target before projection does not change the closure of its
projection.  It does not claim that projection itself preserves closedness. -/
theorem closure_realEuclideanExistentialProjection_closure_eq
    {n q : ℕ} (A : Set (RealEuclidean (n + q))) :
    closure (realEuclideanExistentialProjection (closure A)) =
      closure (realEuclideanExistentialProjection A) := by
  rw [realEuclideanExistentialProjection_eq_takeLeft_image,
    realEuclideanExistentialProjection_eq_takeLeft_image]
  change closure ((realEuclideanTakeLeftContinuousLinearMap n q) '' closure A) =
    closure ((realEuclideanTakeLeftContinuousLinearMap n q) '' A)
  exact closure_image_closure
    (realEuclideanTakeLeftContinuousLinearMap n q).continuous

end AbelFormalization
