import AbelFormalization.CharbonnelSardianProjectionRadialBranch
import AbelFormalization.CharbonnelSardianProjectionTopology

/-!
# The from-below reduction in Wilkie 3.10

Appending either the radial equation or a squared Jacobian minor leaves
the old constituent equations as a prefix. Consequently the from-below
clause for one-coordinate projection needs only a carrier-section lift,
prefix compatibility of the new modulus, and the old from-below clause.
The regular-value/minor alternative is needed for the from-above clause,
not for this reduction.

The carrier-section lift is an explicit premise here. Its discharge for
the assembled finite projected family requires an old/new carrier bridge
through `sardianProjectionOldInputReindex` and any trailing parameter pads.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Drop the last positive approximation parameter, retaining `ε₀` and
all the old constituent levels. -/
def sardianProjectionParameterPrefix {k : ℕ}
    (ε : RealEuclidean ((k + 1) + 1)) : RealEuclidean (k + 1) :=
  fun i ↦ ε i.castSucc

@[simp]
theorem sardianProjectionParameterPrefix_zero {k : ℕ}
    (ε : RealEuclidean ((k + 1) + 1)) :
    sardianProjectionParameterPrefix ε 0 = ε 0 :=
  rfl

/-- Visible-coordinate projection contracts the finite-coordinate max
metric used in the approximation inequalities. -/
theorem dist_realEuclideanTakeLeft_le
    {n q : ℕ} (u v : RealEuclidean (n + q)) :
    dist (realEuclideanTakeLeft u) (realEuclideanTakeLeft v) ≤
      dist u v := by
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist u v)).mpr
  intro i
  have hcoordinate :=
    (dist_pi_le_iff (dist_nonneg : 0 ≤ dist u v)).mp
      (le_refl (dist u v)) (Fin.castAdd q i)
  simpa only [realEuclideanTakeLeft] using hcoordinate

/-- The exact semantic from-below part of one-coordinate Sardian
projection. The carrier lift is independent of which appended last equation
was selected: it says only that every new section point is an old section
point after choosing the erased visible coordinate. -/
theorem approximatesFromBelow_projection_of_prefixSection
    {n k : ℕ} (A : Set (RealEuclidean (n + 1)))
    (oldT : Set (RealEuclidean ((n + 1) + k)))
    (newT : Set (RealEuclidean (n + (k + 1))))
    (oldModulus : CharbonnelModulus k)
    (newModulus : CharbonnelModulus (k + 1))
    (hbound : ∀ ε : RealEuclidean ((k + 1) + 1),
      newModulus.IsBounded ε →
        oldModulus.IsBounded (sardianProjectionParameterPrefix ε))
    (hsection : ∀ ε : RealEuclidean ((k + 1) + 1),
      ∀ x : RealEuclidean n,
        realEuclideanAppend x (CharbonnelModulus.parameterTail ε) ∈ newT →
          ∃ z : RealEuclidean 1,
            realEuclideanAppend (realEuclideanAppend x z)
              (CharbonnelModulus.parameterTail
                (sardianProjectionParameterPrefix ε)) ∈ oldT)
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus oldT (closure A)) :
    CharbonnelModulus.ApproximatesFromBelow
      newModulus newT
        (closure (realEuclideanExistentialProjection A)) := by
  intro ε hε x hx
  obtain ⟨z, holdSection⟩ := hsection ε x hx
  obtain ⟨v, hvClosure, hvDist⟩ :=
    hbelow (sardianProjectionParameterPrefix ε)
      (hbound ε hε) (realEuclideanAppend x z) holdSection
  refine ⟨realEuclideanTakeLeft v, ?_, ?_⟩
  · have hvProjected :
        realEuclideanTakeLeft v ∈
          realEuclideanExistentialProjection (closure A) := by
      rw [realEuclideanExistentialProjection_eq_takeLeft_image]
      exact ⟨v, hvClosure, rfl⟩
    exact realEuclideanExistentialProjection_closure_subset_closure A
      hvProjected
  · calc
      dist x (realEuclideanTakeLeft v) =
          dist (realEuclideanTakeLeft (realEuclideanAppend x z))
            (realEuclideanTakeLeft v) := by
              simp only [realEuclideanTakeLeft_append]
      _ ≤ dist (realEuclideanAppend x z) v :=
          dist_realEuclideanTakeLeft_le _ _
      _ < ε 0 := by
          simpa only [sardianProjectionParameterPrefix_zero] using hvDist

end AbelFormalization
