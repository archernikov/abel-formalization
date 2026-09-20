import AbelFormalization.CharbonnelSection53StationaryLimitSupport
import Mathlib.Data.Fintype.EquivFin

/-!
# What successor deletion actually removes in Section 5.3(c)

Deleting the defective base-support union eliminates every defective
vertical component of the preceding ball from the successor's vertical
image. If the successor still has the same globally maximal component
count, its components must arise by splitting components that remain.

These theorems are finite-stage facts. They do not infer that a stationary
chain exists or that full WS5 excludes one.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Pure finite-cardinality form of the replacement step: if two finite
component-index sets have the same size and one old component has no
successor, two successor components must share an old parent. Constructing
the parent map from inclusion of vertical images is a separate topology
step; the assertion here does not assume that map is injective. -/
theorem charbonnelSection53_sameRank_forces_parentCollision
    {Old New : Type*} [Fintype Old] [Fintype New]
    (parent : New → Old)
    (hcount : Fintype.card New = Fintype.card Old)
    (missing : Old) (hmissing : missing ∉ Set.range parent) :
    ∃ a b : New, a ≠ b ∧ parent a = parent b := by
  by_contra hnone
  have hinj : Function.Injective parent := by
    intro a b hab
    by_contra hne
    exact hnone ⟨a, b, hne, hab⟩
  have hsurj : Function.Surjective parent :=
    ((Fintype.bijective_iff_injective_and_card parent).mpr
      ⟨hinj, hcount⟩).2
  exact hmissing (Set.mem_range.mpr (hsurj missing))

/-- A successor ball avoiding `β` cannot meet a defective vertical
component of its predecessor. The subset statement also records that the
successor vertical image remains inside the predecessor image. -/
theorem charbonnelSection53_nextVerticalImage_subset_without_defectiveComponent
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    {Bnext : Set (RealEuclidean n)}
    (hdelete : Bnext ⊆
      charbonnelRelativeClosedBall ω candidate.center candidate.radius \
        charbonnelRelativeDefectiveSupportUnion candidate)
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ))
    (hdefective : charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c ≠
          charbonnelRelativeClosedBall ω candidate.center candidate.radius) :
    charbonnelVerticalImageOver S Bnext ⊆
      charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) \
        realConnectedComponentCarrier
          (charbonnelVerticalImageOver S
            (charbonnelRelativeClosedBall ω candidate.center candidate.radius)) c := by
  intro t htNext
  obtain ⟨y, hyNext, hytS⟩ := htNext
  have hyB : y ∈ charbonnelRelativeClosedBall ω
      candidate.center candidate.radius := (hdelete hyNext).1
  have hyOutside : y ∉ charbonnelRelativeDefectiveSupportUnion candidate :=
    (hdelete hyNext).2
  refine ⟨⟨y, hyB, hytS⟩, ?_⟩
  intro htComponent
  have hySupport : y ∈ charbonnelVerticalComponentBaseSupport S
      (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c :=
    ⟨hyB, t, htComponent, hytS⟩
  apply hyOutside
  unfold charbonnelRelativeDefectiveSupportUnion
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  change y ∈
    (if charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c =
          charbonnelRelativeClosedBall ω candidate.center candidate.radius
      then (∅ : Set (RealEuclidean n))
      else charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c)
  simpa only [if_neg hdefective] using hySupport

/-- In an actual stationary deletion chain, every defective component of
stage `m` disappears from the vertical image at stage `m + 1`. Same-rank
stationarity therefore needs replacement components inside the components
that remain. -/
theorem charbonnelSection53_stationarySuccessor_avoids_defectiveComponent
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ)
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence m) : Set ℝ))
    (hdefective : charbonnelVerticalComponentBaseSupport S
        (charbonnelSection53StationaryBall sequence m) c ≠
          charbonnelSection53StationaryBall sequence m) :
    charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence (m + 1)) ⊆
      charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence m) \
          realConnectedComponentCarrier
            (charbonnelVerticalImageOver S
              (charbonnelSection53StationaryBall sequence m)) c := by
  exact charbonnelSection53_nextVerticalImage_subset_without_defectiveComponent
    (sequence m).1.1 (hdelete m) c hdefective

end AbelFormalization
