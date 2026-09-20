import AbelFormalization.CharbonnelSection53GlobalStratum

/-!
# Charbonnel 5.3(c): deleting defective supports and old component labels

The vertical-image inclusion from a smaller base to an old relative ball
sends each selected component to an old component.  If the smaller base
avoids the union of the old incomplete base supports, that old component
must have full support on the old ball.  This statement concerns the actual
inclusion-induced map, so it does not identify components merely by their
positions in an interval enumeration.

It does not claim that the inclusion map is injective.  Several new
components can map to the same old full-support component; this is the
possible splitting that the stationary-rank argument must control.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Every component over a selected sub-base avoiding `β` maps to an old
component with full support on the old relative ball.  The representative
of the selected component has a base witness in the sub-base.  A defective
old image label would put that witness back in `β`. -/
theorem charbonnelSection53_inclusionMap_avoidsDefectiveLabel
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    {B' : Set (RealEuclidean n)}
    (hB' : B' ⊆
      charbonnelRelativeClosedBall ω candidate.center candidate.radius \
        charbonnelRelativeDefectiveSupportUnion candidate)
    (small : ConnectedComponents
      (charbonnelVerticalImageOver S B' : Set ℝ)) :
    charbonnelVerticalComponentBaseSupport S
      (charbonnelRelativeClosedBall ω candidate.center candidate.radius)
      (charbonnelVerticalComponentInclusionMap S
      (hB'.trans Set.sdiff_subset) small) =
      charbonnelRelativeClosedBall ω candidate.center candidate.radius := by
  classical
  let B := charbonnelRelativeClosedBall ω candidate.center candidate.radius
  let hBC : B' ⊆ B := hB'.trans Set.sdiff_subset
  let old := charbonnelVerticalComponentInclusionMap S hBC small
  let rep := connectedComponentRepresentative
    (charbonnelVerticalImageOver S B') small
  obtain ⟨x, hxB', hxt⟩ := rep.property
  have htSmall : rep.1 ∈
      realConnectedComponentCarrier
        (charbonnelVerticalImageOver S B') small := by
    exact ⟨rep, mem_connectedComponent, rfl⟩
  have htOld : rep.1 ∈
      realConnectedComponentCarrier
        (charbonnelVerticalImageOver S B) old :=
    (realConnectedComponentCarrier_subset_of_inclusionMap_eq
      S hBC
      (show charbonnelVerticalComponentInclusionMap S hBC small = old from rfl))
      htSmall
  have hxSupport :
      x ∈ charbonnelVerticalComponentBaseSupport S B old :=
    ⟨hBC hxB', rep.1, htOld, hxt⟩
  change charbonnelVerticalComponentBaseSupport S B old = B
  by_contra hdefect
  have hxβ : x ∈ charbonnelRelativeDefectiveSupportUnion candidate := by
    unfold charbonnelRelativeDefectiveSupportUnion
    apply Set.mem_iUnion.mpr
    refine ⟨old, ?_⟩
    change x ∈ (if charbonnelVerticalComponentBaseSupport S B old = B
      then (∅ : Set (RealEuclidean n))
      else charbonnelVerticalComponentBaseSupport S B old)
    simpa only [if_neg hdefect] using hxSupport
  exact (hB' hxB').2 hxβ

end AbelFormalization
