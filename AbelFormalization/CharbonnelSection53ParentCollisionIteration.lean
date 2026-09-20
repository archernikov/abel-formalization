import AbelFormalization.CharbonnelSection53ParentCollision

/-!
# Iterating the parent-collision obstruction in Charbonnel 5.3(c)

A positive-defect stationary deletion chain loses a genuine old vertical
component at every stage and replaces it by a collision of two successor
components in one surviving parent.  This file packages that one-step fact
and proves the part of its iteration that follows without an additional
geometric argument: the chain contains infinitely many nonempty, pairwise
disjoint lost branches of the source set.

Pairwise disjoint branches alone do not put arbitrarily many connected
components in one affine section.  The final definition records only that
remaining geometric lift: the first `N + 1` canonical lost branches have
representatives in distinct components of a common affine section.  This
strictly refines the previous broad affine-explosion premise, and it implies
that premise by a cardinality argument.
-/

noncomputable section

open Set Filter

namespace AbelFormalization

set_option autoImplicit false

/-- One stationary successor step, including both the component deleted
from the old image and the two new components which collide in a surviving
old parent. -/
structure CharbonnelSection53SuccessorCollisionCertificate
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) where
  lost : ConnectedComponents
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence m) : Set ℝ)
  lost_defective : charbonnelVerticalComponentBaseSupport S
      (charbonnelSection53StationaryBall sequence m) lost ≠
    charbonnelSection53StationaryBall sequence m
  child₁ : ConnectedComponents
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence (m + 1)) : Set ℝ)
  child₂ : ConnectedComponents
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence (m + 1)) : Set ℝ)
  children_ne : child₁ ≠ child₂
  same_parent :
    charbonnelVerticalComponentInclusionMap S
        ((hdelete m).trans Set.sdiff_subset) child₁ =
      charbonnelVerticalComponentInclusionMap S
        ((hdelete m).trans Set.sdiff_subset) child₂

/-- Every stage of a positive-defect stationary deletion chain has a full
deleted-component/replacement-collision certificate. -/
theorem nonempty_charbonnelSection53_successorCollisionCertificate
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    Nonempty
      (CharbonnelSection53SuccessorCollisionCertificate sequence hdelete m) := by
  obtain ⟨lost, hlost⟩ :=
    exists_defectiveComponent_of_stationary_positiveDefect
      sequence hpositive m
  obtain ⟨left, right, hne, hparent⟩ :=
    exists_stationarySuccessorComponent_parentCollision
      sequence hpositive hdelete m
  exact ⟨{
    lost := lost
    lost_defective := hlost
    child₁ := left
    child₂ := right
    children_ne := hne
    same_parent := hparent }⟩

/-- A canonical certificate, used only to name one lost branch at every
stage.  No mathematical conclusion depends on which certificate choice is
made. -/
def charbonnelSection53_successorCollisionCertificate
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    CharbonnelSection53SuccessorCollisionCertificate sequence hdelete m :=
  Classical.choice
    (nonempty_charbonnelSection53_successorCollisionCertificate
      sequence hpositive hdelete m)

/-- The old component selected as the branch lost at stage `m`. -/
def charbonnelSection53_stationaryLostComponent
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence m) : Set ℝ) :=
  (charbonnelSection53_successorCollisionCertificate
    sequence hpositive hdelete m).lost

/-- The canonical lost old component is genuinely absent from the range of
the successor parent map. -/
theorem charbonnelSection53_stationaryLostComponent_not_mem_parentRange
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    charbonnelSection53_stationaryLostComponent
        sequence hpositive hdelete m ∉
      Set.range (charbonnelVerticalComponentInclusionMap S
        ((hdelete m).trans Set.sdiff_subset)) := by
  let certificate := charbonnelSection53_successorCollisionCertificate
    sequence hpositive hdelete m
  change certificate.lost ∉ Set.range
    (charbonnelVerticalComponentInclusionMap S
      ((hdelete m).trans Set.sdiff_subset))
  rintro ⟨small, hsmall⟩
  apply certificate.lost_defective
  have hfull := charbonnelSection53_inclusionMap_avoidsDefectiveLabel
    (sequence m).1.1 (hdelete m) small
  rw [← hsmall]
  simpa only [charbonnelSection53StationaryBall] using hfull

/-- Equivalently, every stationary successor parent map is noninjective;
the certificate exposes the two distinct colliding children. -/
theorem not_injective_charbonnelSection53_stationarySuccessorParent
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    ¬ Function.Injective (charbonnelVerticalComponentInclusionMap S
      ((hdelete m).trans Set.sdiff_subset)) := by
  let certificate := charbonnelSection53_successorCollisionCertificate
    sequence hpositive hdelete m
  intro hinjective
  exact certificate.children_ne
    (hinjective certificate.same_parent)

/-- The scalar carrier of the old component lost at stage `m`. -/
def charbonnelSection53_stationaryLostCarrier
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) : Set ℝ :=
  realConnectedComponentCarrier
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence m))
    (charbonnelSection53_stationaryLostComponent
      sequence hpositive hdelete m)

/-- The corresponding part of the source set.  It records both the old
base ball and the scalar lost-component label. -/
def charbonnelSection53_stationaryLostBranch
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) : Set (RealEuclidean (n + 1)) :=
  {z | z ∈ S ∧
    charbonnelVerticalBaseCoordinate z ∈
      charbonnelSection53StationaryBall sequence m ∧
    charbonnelVerticalLastCoordinate z ∈
      charbonnelSection53_stationaryLostCarrier
        sequence hpositive hdelete m}

/-- Stationary balls form an antitone sequence. -/
theorem antitone_charbonnelSection53_stationaryBall
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) :
    Antitone (charbonnelSection53StationaryBall sequence) :=
  antitone_nat_of_succ_le (fun m ↦ (hdelete m).trans Set.sdiff_subset)

/-- Every real connected-component carrier lies in its underlying set. -/
theorem realConnectedComponentCarrier_subset_self
    (s : Set ℝ) (c : ConnectedComponents s) :
    realConnectedComponentCarrier s c ⊆ s := by
  intro t ht
  rw [← iUnion_realConnectedComponentCarrier s]
  exact Set.mem_iUnion.mpr ⟨c, ht⟩

/-- A lost scalar carrier is nonempty. -/
theorem charbonnelSection53_stationaryLostCarrier_nonempty
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    (charbonnelSection53_stationaryLostCarrier
      sequence hpositive hdelete m).Nonempty := by
  let c := charbonnelSection53_stationaryLostComponent
    sequence hpositive hdelete m
  let rep := connectedComponentRepresentative
    (charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence m)) c
  exact ⟨rep.1, ⟨rep, mem_connectedComponent, rfl⟩⟩

/-- A canonical scalar height in the branch lost at stage `m`. -/
def charbonnelSection53_stationaryLostHeight
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) : ℝ :=
  Classical.choose
    (charbonnelSection53_stationaryLostCarrier_nonempty
      sequence hpositive hdelete m)

theorem charbonnelSection53_stationaryLostHeight_mem
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    charbonnelSection53_stationaryLostHeight sequence hpositive hdelete m ∈
      charbonnelSection53_stationaryLostCarrier
        sequence hpositive hdelete m :=
  Classical.choose_spec
    (charbonnelSection53_stationaryLostCarrier_nonempty
      sequence hpositive hdelete m)

/-- The successor vertical image is disjoint from the scalar carrier lost
at the preceding stage. -/
theorem disjoint_charbonnelSection53_stationaryLostCarrier_successorImage
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    Disjoint
      (charbonnelSection53_stationaryLostCarrier
        sequence hpositive hdelete m)
      (charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence (m + 1))) := by
  let certificate := charbonnelSection53_successorCollisionCertificate
    sequence hpositive hdelete m
  have havoid :=
    charbonnelSection53_stationarySuccessor_avoids_defectiveComponent
      sequence hdelete m certificate.lost certificate.lost_defective
  rw [Set.disjoint_left]
  intro t htLost htNext
  exact (havoid htNext).2 htLost

/-- Lost scalar carriers at distinct stages are pairwise disjoint.  The
later carrier lies in the next vertical image after the earlier carrier was
deleted. -/
theorem pairwiseDisjoint_charbonnelSection53_stationaryLostCarrier
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) :
    (Set.univ : Set ℕ).PairwiseDisjoint
      (charbonnelSection53_stationaryLostCarrier
        sequence hpositive hdelete) := by
  have hforward : ∀ {i j : ℕ}, i < j →
      Disjoint
        (charbonnelSection53_stationaryLostCarrier
          sequence hpositive hdelete i)
        (charbonnelSection53_stationaryLostCarrier
          sequence hpositive hdelete j) := by
    intro i j hij
    have hjSubset : charbonnelSection53_stationaryLostCarrier
        sequence hpositive hdelete j ⊆
        charbonnelVerticalImageOver S
          (charbonnelSection53StationaryBall sequence (i + 1)) := by
      exact
        (realConnectedComponentCarrier_subset_self _ _).trans
          (charbonnelVerticalImageOver_mono S
            ((antitone_charbonnelSection53_stationaryBall sequence hdelete)
              (Nat.succ_le_iff.mpr hij)))
    exact Set.disjoint_of_subset_right hjSubset
      (disjoint_charbonnelSection53_stationaryLostCarrier_successorImage
        sequence hpositive hdelete i)
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hforward hij
  · exact (hforward hji).symm

/-- The lost heights are all distinct.  This is the purely combinatorial
infinite output of iterating the one-step collision/deletion certificate. -/
theorem injective_charbonnelSection53_stationaryLostHeight
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) :
    Function.Injective
      (charbonnelSection53_stationaryLostHeight
        sequence hpositive hdelete) := by
  intro i j hij
  by_contra hne
  have hdisjoint :=
    pairwiseDisjoint_charbonnelSection53_stationaryLostCarrier
      sequence hpositive hdelete (Set.mem_univ i) (Set.mem_univ j) hne
  have hi := charbonnelSection53_stationaryLostHeight_mem
    sequence hpositive hdelete i
  have hj := charbonnelSection53_stationaryLostHeight_mem
    sequence hpositive hdelete j
  rw [← hij] at hj
  exact (Set.disjoint_left.mp hdisjoint) hi hj

/-- Every lost branch in the ambient source is nonempty. -/
theorem charbonnelSection53_stationaryLostBranch_nonempty
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    (charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete m).Nonempty := by
  obtain ⟨t, htCarrier⟩ :=
    charbonnelSection53_stationaryLostCarrier_nonempty
      sequence hpositive hdelete m
  have htImage : t ∈ charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence m) :=
    realConnectedComponentCarrier_subset_self _ _ htCarrier
  obtain ⟨y, hyBall, hytS⟩ := htImage
  refine ⟨charbonnelAppendLastCoordinate y t, ?_⟩
  refine ⟨hytS, ?_, ?_⟩
  · simpa only [charbonnelVerticalBaseCoordinate,
      charbonnelAppendLastCoordinate, realEuclideanTakeLeft_append]
      using hyBall
  · simpa only [charbonnelVerticalLastCoordinate,
      charbonnelAppendLastCoordinate_last] using htCarrier

/-- The base coordinate of a lost-branch point belongs to the defective
support deleted before the next stage. -/
theorem charbonnelSection53_stationaryLostBranch_base_mem_defectiveSupport
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) {z : RealEuclidean (n + 1)}
    (hz : z ∈ charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete m) :
    charbonnelVerticalBaseCoordinate z ∈
      charbonnelRelativeDefectiveSupportUnion (sequence m).1.1 := by
  let certificate := charbonnelSection53_successorCollisionCertificate
    sequence hpositive hdelete m
  unfold charbonnelRelativeDefectiveSupportUnion
  refine Set.mem_iUnion.mpr ⟨certificate.lost, ?_⟩
  change charbonnelVerticalBaseCoordinate z ∈
    (if charbonnelVerticalComponentBaseSupport S
        (charbonnelSection53StationaryBall sequence m) certificate.lost =
          charbonnelSection53StationaryBall sequence m then
      (∅ : Set (RealEuclidean n))
    else charbonnelVerticalComponentBaseSupport S
      (charbonnelSection53StationaryBall sequence m) certificate.lost)
  simp only [certificate.lost_defective, ↓reduceIte]
  refine ⟨hz.2.1, charbonnelVerticalLastCoordinate z, hz.2.2, ?_⟩
  simpa only [charbonnelVerticalBaseCoordinate,
    charbonnelVerticalLastCoordinate,
    charbonnelAppendLastCoordinate_takeLeft_last] using hz.1

/-- Consequently, no point of the lost branch has base coordinate in the
successor ball. -/
theorem charbonnelSection53_stationaryLostBranch_base_not_mem_successorBall
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) {z : RealEuclidean (n + 1)}
    (hz : z ∈ charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete m) :
    charbonnelVerticalBaseCoordinate z ∉
      charbonnelSection53StationaryBall sequence (m + 1) := by
  intro hzNext
  exact (hdelete m hzNext).2
    (charbonnelSection53_stationaryLostBranch_base_mem_defectiveSupport
      sequence hpositive hdelete m hz)

/-- The ambient lost branches are pairwise disjoint as well. -/
theorem pairwiseDisjoint_charbonnelSection53_stationaryLostBranch
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) :
    (Set.univ : Set ℕ).PairwiseDisjoint
      (charbonnelSection53_stationaryLostBranch
        sequence hpositive hdelete) := by
  intro i _hi j _hj hij
  change Disjoint
    (charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete i)
    (charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete j)
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact (Set.disjoint_left.mp
    (pairwiseDisjoint_charbonnelSection53_stationaryLostCarrier
      sequence hpositive hdelete (Set.mem_univ i) (Set.mem_univ j) hij))
        hzi.2.2 hzj.2.2

/-! ## The exact remaining affine-separation lift -/

/-- The minimal geometric step still needed after collision iteration.
For the first `N + 1` lost branches, it asks for one point from each in a
common affine section, with those points lying in distinct connected
components of that section of `S`.  Nonemptiness and pairwise disjointness
of the branches themselves are theorems above. -/
def CharbonnelSection53LostBranchAffineSeparation
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∀ (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1),
    Tendsto (fun m : ℕ ↦ (sequence m).1.1.radius) atTop (nhds 0) →
    ∀ N : ℕ,
      ∃ (V : AffineSubspace ℝ (RealEuclidean (n + 1)))
        (point : Fin (N + 1) →
          ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
            Set (RealEuclidean (n + 1)))),
        (∀ i, (point i).1 ∈
          charbonnelSection53_stationaryLostBranch
            sequence hpositive hdelete i.1) ∧
        Function.Injective (fun i ↦ ConnectedComponents.mk (point i))

/-- Affine separation of the canonical lost branches gives the earlier
stationary-chain affine-explosion interface. -/
theorem charbonnelSection53_stationaryForcesAffineExplosion_of_lostBranchAffineSeparation
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hseparate : CharbonnelSection53LostBranchAffineSeparation ω S) :
    CharbonnelSection53StationaryForcesAffineExplosion ω S := by
  rintro ⟨sequence, hpositive, hdelete, hradius⟩ N
  obtain ⟨V, point, _hpoint, hinjective⟩ :=
    hseparate sequence hpositive hdelete hradius N
  refine ⟨V, ?_⟩
  have hlower : (N + 1 : ℕ∞) ≤ ENat.card (ConnectedComponents
      ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
        Set (RealEuclidean (n + 1)))) := by
    simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one] using
        ENat.card_le_card_of_injective hinjective
  have hsucc : (N : ℕ∞) < (N + 1 : ℕ∞) := by
    exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self N)
  exact hsucc.trans_le hlower

/-- Thus WS5 excludes a stationary deletion chain once only the explicit
lost-branch affine-separation lift has been supplied. -/
theorem charbonnelSection53_noStationary_of_lostBranchAffineSeparation
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hws5 : CharbonnelUniformAffineSectionComponentBound S)
    (hseparate : CharbonnelSection53LostBranchAffineSeparation ω S) :
    CharbonnelSection53NoStationaryNestedSequence ω S :=
  charbonnelSection53_noStationary_of_affineExplosion hws5
    (charbonnelSection53_stationaryForcesAffineExplosion_of_lostBranchAffineSeparation
      hseparate)

/-- Literal-zero closure members already supply the WS5 half of the last
theorem; the lost-branch affine-separation statement is the sole remaining
input in this route. -/
theorem literalZeroSet_charbonnelClosure_noStationary_of_lostBranchAffineSeparation
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hseparate : CharbonnelSection53LostBranchAffineSeparation ω S) :
    CharbonnelSection53NoStationaryNestedSequence ω S := by
  apply charbonnelSection53_noStationary_of_lostBranchAffineSeparation
    (literalZeroSet_charbonnelClosure_uniformAffineSectionComponentBound
      hG hsmooth hUFF (by omega) hS)
  exact hseparate

end AbelFormalization
