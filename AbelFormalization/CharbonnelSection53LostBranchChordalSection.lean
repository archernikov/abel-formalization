import AbelFormalization.CharbonnelSection53LostBranchAffineLine

/-!
# Chordal affine sections for the lost branches in Charbonnel 5.3(c)

The affine-line argument needs less than a common collinear transversal.
What it actually uses is that, if two selected points are in the same
component of the chosen section, their straight chord lies in the source.
This file isolates that weaker incidence condition.

The stationary deletion iteration itself proves that a chord joining points
from two differently indexed lost branches cannot be contained in the source:
the last-coordinate image of the chord would connect the earlier lost
component to the next vertical image.  Hence any affine section whose
components have the chord property separates all selected lost branches.

Every nondegenerate affine-line section has the chord property by the previous
module, while convex sources have it in every affine section.  Thus the new
selection residual permits noncollinear selected points and is strictly less
restrictive geometrically than the common-line residual.  Constructing such a
section for every finite lost-branch prefix remains the incidence step.
-/

noncomputable section

open Set Filter

namespace AbelFormalization

set_option autoImplicit false

/-! ## The chord obstruction supplied by stationary deletion -/

/-- A straight segment cannot stay in `S` when its endpoints belong to two
lost branches at different stages.  The proof uses only base support,
nesting/deletion, and convexity of the earlier closed ball. -/
theorem not_segment_subset_of_stationaryLostBranch_points
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    {i j : ℕ} (hij : i < j)
    {x y : RealEuclidean (n + 1)}
    (hx : x ∈ charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete i)
    (hy : y ∈ charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete j) :
    ¬ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap x y t ∈ S := by
  intro hchord
  let scalarChord : Set ℝ :=
    AffineMap.lineMap
      (charbonnelVerticalLastCoordinate x)
      (charbonnelVerticalLastCoordinate y) ''
        Set.Icc (0 : ℝ) 1
  have hscalarPreconnected : IsPreconnected scalarChord :=
    isPreconnected_Icc.image _ AffineMap.lineMap_continuous.continuousOn
  have hscalarSubset : scalarChord ⊆
      charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence i) := by
    rintro t ⟨u, hu, rfl⟩
    let z := AffineMap.lineMap x y u
    have hzS : z ∈ S := hchord u hu
    have hxBase := hx.2.1
    have hyBase : charbonnelVerticalBaseCoordinate y ∈
        charbonnelSection53StationaryBall sequence i := by
      exact (antitone_charbonnelSection53_stationaryBall sequence hdelete)
        (Nat.le_of_lt hij) hy.2.1
    have hzBase : charbonnelVerticalBaseCoordinate z ∈
        charbonnelSection53StationaryBall sequence i := by
      refine ⟨?_, ?_⟩
      · exact hbase z hzS
      · rw [charbonnelVerticalBaseCoordinate_lineMap]
        exact (convex_closedBall (sequence i).1.1.center
          (sequence i).1.1.radius).lineMap_mem hxBase.2 hyBase.2 hu
    refine ⟨charbonnelVerticalBaseCoordinate z, hzBase, ?_⟩
    have hzLast :
        AffineMap.lineMap
            (charbonnelVerticalLastCoordinate x)
            (charbonnelVerticalLastCoordinate y) u =
          charbonnelVerticalLastCoordinate z := by
      symm
      exact charbonnelVerticalLastCoordinate_lineMap x y u
    rw [hzLast]
    simpa only [charbonnelVerticalBaseCoordinate,
      charbonnelVerticalLastCoordinate,
      charbonnelAppendLastCoordinate_takeLeft_last] using hzS
  have hxScalar : charbonnelVerticalLastCoordinate x ∈ scalarChord := by
    refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  have hyScalar : charbonnelVerticalLastCoordinate y ∈ scalarChord := by
    refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  let Vi : Set ℝ := charbonnelVerticalImageOver S
    (charbonnelSection53StationaryBall sequence i)
  have hxVi : charbonnelVerticalLastCoordinate x ∈ Vi :=
    realConnectedComponentCarrier_subset_self _ _ hx.2.2
  have hyVi : charbonnelVerticalLastCoordinate y ∈ Vi :=
    hscalarSubset hyScalar
  have hyConnected :
      (⟨charbonnelVerticalLastCoordinate y, hyVi⟩ : Vi) ∈
        connectedComponent
          (⟨charbonnelVerticalLastCoordinate x, hxVi⟩ : Vi) :=
    mem_connectedComponent_of_mem_preconnected_subset
      hxVi hyVi hxScalar hyScalar hscalarSubset hscalarPreconnected
  have hcomponentEq :
      ConnectedComponents.mk
          (⟨charbonnelVerticalLastCoordinate y, hyVi⟩ : Vi) =
        charbonnelSection53_stationaryLostComponent
          sequence hpositive hdelete i := by
    have hyx : ConnectedComponents.mk
        (⟨charbonnelVerticalLastCoordinate y, hyVi⟩ : Vi) =
        ConnectedComponents.mk
          (⟨charbonnelVerticalLastCoordinate x, hxVi⟩ : Vi) :=
      ConnectedComponents.coe_eq_coe'.mpr hyConnected
    exact hyx.trans
      ((mem_realConnectedComponentCarrier_iff_mk_eq Vi
        (charbonnelSection53_stationaryLostComponent
          sequence hpositive hdelete i) hxVi).mp hx.2.2)
  have hyInLost : charbonnelVerticalLastCoordinate y ∈
      charbonnelSection53_stationaryLostCarrier
        sequence hpositive hdelete i :=
    (mem_realConnectedComponentCarrier_iff_mk_eq Vi
      (charbonnelSection53_stationaryLostComponent
        sequence hpositive hdelete i) hyVi).mpr hcomponentEq
  have hyNext : charbonnelVerticalLastCoordinate y ∈
      charbonnelVerticalImageOver S
        (charbonnelSection53StationaryBall sequence (i + 1)) := by
    apply charbonnelVerticalImageOver_mono S
      ((antitone_charbonnelSection53_stationaryBall sequence hdelete)
        (Nat.succ_le_iff.mpr hij))
    exact realConnectedComponentCarrier_subset_self _ _ hy.2.2
  exact (Set.disjoint_left.mp
    (disjoint_charbonnelSection53_stationaryLostCarrier_successorImage
      sequence hpositive hdelete i)) hyInLost hyNext

/-! ## Chordal affine sections -/

/-- In a chordal affine section, two points in the same connected component
have their whole straight chord in the ambient source.  No common-line
condition is imposed on different components or on a selected family. -/
def CharbonnelChordalAffineSection {d : ℕ}
    (S : Set (RealEuclidean d))
    (V : AffineSubspace ℝ (RealEuclidean d)) : Prop :=
  ∀ {x y : ((S ∩ (V : Set (RealEuclidean d))) :
      Set (RealEuclidean d))},
    ConnectedComponents.mk x = ConnectedComponents.mk y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap (x : RealEuclidean d) y t ∈ S

/-- A nondegenerate affine-line section is chordal. -/
theorem charbonnelChordalAffineSection_affineSpan_pair
    {d : ℕ} {S : Set (RealEuclidean d)}
    {a b : RealEuclidean d} (hab : a ≠ b) :
    CharbonnelChordalAffineSection S (affineSpan ℝ {a, b}) := by
  intro x y hcomponent
  exact affineLine_chord_subset_of_connectedComponent_eq hab hcomponent

/-- Convexity is another source of chordal sections and shows that the
condition is not intrinsically one-dimensional. -/
theorem Convex.charbonnelChordalAffineSection
    {d : ℕ} {S : Set (RealEuclidean d)}
    (hS : Convex ℝ S) (V : AffineSubspace ℝ (RealEuclidean d)) :
    CharbonnelChordalAffineSection S V := by
  intro x y _hcomponent t ht
  exact hS.lineMap_mem x.property.1 y.property.1 ht

/-- Points from differently indexed lost branches have distinct components
in any chordal affine section. -/
theorem injective_components_of_stationaryLostBranch_points_in_chordalSection
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    {V : AffineSubspace ℝ (RealEuclidean (n + 1))}
    (hchordal : CharbonnelChordalAffineSection S V)
    {ι : Type*} (index : ι → ℕ)
    (hindex : Function.Injective index)
    (point : ι →
      ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
        Set (RealEuclidean (n + 1))))
    (hpoint : ∀ i, (point i).1 ∈
      charbonnelSection53_stationaryLostBranch
        sequence hpositive hdelete (index i)) :
    Function.Injective (fun i ↦ ConnectedComponents.mk (point i)) := by
  intro i j hcomponents
  apply hindex
  by_contra hindexNe
  rcases lt_or_gt_of_ne hindexNe with hij | hji
  · exact (not_segment_subset_of_stationaryLostBranch_points
      hbase sequence hpositive hdelete hij (hpoint i) (hpoint j))
        (hchordal hcomponents)
  · exact (not_segment_subset_of_stationaryLostBranch_points
      hbase sequence hpositive hdelete hji (hpoint j) (hpoint i))
        (hchordal hcomponents.symm)

/-! ## A weaker finite incidence residual -/

/-- Every finite lost-branch prefix has representatives in one chordal
affine section.  Unlike `CharbonnelSection53LostBranchCollinearSelection`,
the representatives need not be collinear and the section may have any
dimension. -/
def CharbonnelSection53LostBranchChordalSectionSelection
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
        CharbonnelChordalAffineSection S V

/-- Chordal-section selection supplies the exact affine-separation residual. -/
theorem charbonnelSection53_lostBranchAffineSeparation_of_chordalSectionSelection
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (hselection :
      CharbonnelSection53LostBranchChordalSectionSelection ω S) :
    CharbonnelSection53LostBranchAffineSeparation ω S := by
  intro sequence hpositive hdelete hradius N
  obtain ⟨V, point, hpoint, hchordal⟩ :=
    hselection sequence hpositive hdelete hradius N
  refine ⟨V, point, hpoint, ?_⟩
  exact
    injective_components_of_stationaryLostBranch_points_in_chordalSection
      hbase sequence hpositive hdelete hchordal
        (fun i : Fin (N + 1) ↦ i.1) Fin.val_injective point hpoint

/-- The old common-line residual implies the chordal-section residual. -/
theorem charbonnelSection53_lostBranchChordalSectionSelection_of_collinearSelection
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hcollinear : CharbonnelSection53LostBranchCollinearSelection ω S) :
    CharbonnelSection53LostBranchChordalSectionSelection ω S := by
  intro sequence hpositive hdelete hradius N
  obtain ⟨a, b, rawPoint, hab, hpoint, hline⟩ :=
    hcollinear sequence hpositive hdelete hradius N
  let V : AffineSubspace ℝ (RealEuclidean (n + 1)) := affineSpan ℝ {a, b}
  let point : Fin (N + 1) →
      ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
        Set (RealEuclidean (n + 1))) :=
    fun i ↦ ⟨rawPoint i, (hpoint i).1, hline i⟩
  refine ⟨V, point, ?_, ?_⟩
  · intro i
    exact hpoint i
  · exact charbonnelChordalAffineSection_affineSpan_pair hab

end AbelFormalization
