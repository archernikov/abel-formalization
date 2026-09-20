import AbelFormalization.CharbonnelSection53DeletedComponentReplacement
import AbelFormalization.CharbonnelSection53DefectiveLabelAvoidance

/-!
# Parent collisions in a stationary Charbonnel deletion chain

At every stationary successor, all defective components of the old vertical
image disappear, while the old and new component types have the same finite
cardinality.  Hence the inclusion-induced parent map cannot be injective:
two distinct new components lie in one surviving old component.

This is the finite-stage branching consequence needed before turning an
infinite stationary chain into a violation of the affine-section component
bound.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Positive minimum defect gives an actual defective component at every
stage of a stationary chain. -/
theorem exists_defectiveComponent_of_stationary_positiveDefect
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (m : ℕ) :
    ∃ c : ConnectedComponents
        (charbonnelVerticalImageOver S
          (charbonnelSection53StationaryBall sequence m) : Set ℝ),
      charbonnelVerticalComponentBaseSupport S
          (charbonnelSection53StationaryBall sequence m) c ≠
        charbonnelSection53StationaryBall sequence m := by
  have hdefect : (sequence m).1.1.defectCount ≠ 0 := by
    intro hzero
    have heq :=
      charbonnelRelativeMinimalDefectGlobalCandidates_defect_eq
        (sequence m) (sequence 0)
    exact hpositive (heq.symm.trans hzero)
  change Nat.card {c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence m) : Set ℝ) //
      charbonnelVerticalComponentBaseSupport S
          (charbonnelSection53StationaryBall sequence m) c ≠
        charbonnelSection53StationaryBall sequence m} ≠ 0 at hdefect
  obtain ⟨⟨c, hc⟩⟩ := (Nat.card_ne_zero.mp hdefect).1
  exact ⟨c, hc⟩

/-- Every successor in a stationary deletion chain has two distinct
components with the same old parent. -/
theorem exists_stationarySuccessorComponent_parentCollision
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    ∃ a b : ConnectedComponents
        (charbonnelVerticalImageOver S
          (charbonnelSection53StationaryBall sequence (m + 1)) : Set ℝ),
      a ≠ b ∧
        charbonnelVerticalComponentInclusionMap S
            ((hdelete m).trans Set.sdiff_subset) a =
          charbonnelVerticalComponentInclusionMap S
            ((hdelete m).trans Set.sdiff_subset) b := by
  let Old := ConnectedComponents
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence m) : Set ℝ)
  let New := ConnectedComponents
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence (m + 1)) : Set ℝ)
  let parent : New → Old :=
    charbonnelVerticalComponentInclusionMap S
      ((hdelete m).trans Set.sdiff_subset)
  letI : Finite Old := ENat.card_lt_top.mp
    ((sequence m).1.1.count_eq.trans_lt (by simp))
  letI : Finite New := ENat.card_lt_top.mp
    ((sequence (m + 1)).1.1.count_eq.trans_lt (by simp))
  letI : Fintype Old := Fintype.ofFinite Old
  letI : Fintype New := Fintype.ofFinite New
  have hOldCard : Fintype.card Old = (sequence m).1.1.count := by
    have hOldENat := (sequence m).1.1.count_eq
    change ENat.card Old = ((sequence m).1.1.count : ℕ∞) at hOldENat
    rw [ENat.card_eq_coe_fintype_card] at hOldENat
    exact ENat.natCast_inj.mp hOldENat
  have hNewCard : Fintype.card New = (sequence (m + 1)).1.1.count := by
    have hNewENat := (sequence (m + 1)).1.1.count_eq
    change ENat.card New = ((sequence (m + 1)).1.1.count : ℕ∞) at hNewENat
    rw [ENat.card_eq_coe_fintype_card] at hNewENat
    exact ENat.natCast_inj.mp hNewENat
  have hCandidateCount : (sequence (m + 1)).1.1.count =
      (sequence m).1.1.count := by
    exact ENat.natCast_inj.mp
      (charbonnelRelativeGlobalMaxCandidates_count_eq
        (sequence (m + 1)).1 (sequence m).1)
  have hcount : Fintype.card New = Fintype.card Old := by
    rw [hNewCard, hOldCard, hCandidateCount]
  obtain ⟨missing, hmissingDefective⟩ :=
    exists_defectiveComponent_of_stationary_positiveDefect
      sequence hpositive m
  have hmissing : missing ∉ Set.range parent := by
    rintro ⟨small, hsmall⟩
    apply hmissingDefective
    have hfull :=
      charbonnelSection53_inclusionMap_avoidsDefectiveLabel
        (sequence m).1.1 (hdelete m) small
    have hfull' :
        charbonnelVerticalComponentBaseSupport S
            (charbonnelSection53StationaryBall sequence m) (parent small) =
          charbonnelSection53StationaryBall sequence m := by
      simpa only [parent, Old, New, charbonnelSection53StationaryBall] using hfull
    exact hsmall ▸ hfull'
  obtain ⟨a, b, hab, hparent⟩ :=
    charbonnelSection53_sameRank_forces_parentCollision
      parent hcount missing hmissing
  exact ⟨a, b, hab, hparent⟩

end AbelFormalization
