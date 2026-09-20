import AbelFormalization.CharbonnelSection53ParentCollisionIteration
import AbelFormalization.LocalConstraintFiber

/-!
# Affine-line separation of the lost branches in Charbonnel 5.3(c)

The collision iteration produces pairwise disjoint lost scalar components,
but an ambient connected set can in principle join them after leaving the
ball at which one of the components was lost.  This file proves that such a
reconnection is impossible inside a common affine line when `S` is supported
over the relative base.  Indeed, connectedness on a line fills the chord
between two selected points.  Every point of that chord lies in `S`, hence
over the base, and convexity of the ambient closed ball keeps its base
coordinate in the earlier relative ball.  Its last-coordinate chord would
then join two different components of the earlier vertical image.

Consequently, the exact lost-branch affine-separation residual follows from
one incidence statement only: every finite prefix of lost branches admits a
collinear transversal.  The first two branches always have such a
transversal, so the first genuinely nontrivial finite separation is proved
without an additional incidence premise.
-/

noncomputable section

open Set Filter

namespace AbelFormalization

set_option autoImplicit false

/-! ## Elementary affine-line coordinates -/

/-- A scalar coordinate on the affine line through two points, obtained
from any ambient coordinate on which the endpoints differ. -/
def charbonnelAffineLineParameter {d : ℕ} (k : Fin d)
    (a b z : RealEuclidean d) : ℝ :=
  (z k - a k) / (b k - a k)

@[simp]
theorem charbonnelAffineLineParameter_lineMap {d : ℕ} (k : Fin d)
    (a b : RealEuclidean d) (hab : a k ≠ b k) (t : ℝ) :
    charbonnelAffineLineParameter k a b (AffineMap.lineMap a b t) = t := by
  simp only [charbonnelAffineLineParameter,
    AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  field_simp [sub_ne_zero.mpr hab]
  ring

theorem continuous_charbonnelAffineLineParameter {d : ℕ} (k : Fin d)
    (a b : RealEuclidean d) :
    Continuous (charbonnelAffineLineParameter k a b) := by
  have hcoordinate : Continuous (fun z : RealEuclidean d ↦ z k) :=
    continuous_apply k
  exact (hcoordinate.sub continuous_const).div_const (b k - a k)

/-- On a nondegenerate affine line, the coordinate above recovers the
point by the standard line parametrization. -/
theorem lineMap_charbonnelAffineLineParameter_eq_of_mem {d : ℕ}
    (k : Fin d) (a b : RealEuclidean d) (hab : a k ≠ b k)
    {z : RealEuclidean d} (hz : z ∈ affineSpan ℝ {a, b}) :
    AffineMap.lineMap a b (charbonnelAffineLineParameter k a b z) = z := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hz
  obtain ⟨t, rfl⟩ := hz
  rw [charbonnelAffineLineParameter_lineMap k a b hab]

/-- Reparametrizing a line between two of its points gives the expected
affine combination of their parameters. -/
theorem lineMap_lineMap_eq_lineMap_affineCombination {d : ℕ}
    (a b : RealEuclidean d) (r s t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap a b r)
        (AffineMap.lineMap a b s) t =
      AffineMap.lineMap a b ((1 - t) * r + t * s) := by
  funext j
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

@[simp]
theorem charbonnelVerticalBaseCoordinate_lineMap {n : ℕ}
    (a b : RealEuclidean (n + 1)) (t : ℝ) :
    charbonnelVerticalBaseCoordinate (AffineMap.lineMap a b t) =
      AffineMap.lineMap (charbonnelVerticalBaseCoordinate a)
        (charbonnelVerticalBaseCoordinate b) t := by
  funext j
  simp only [charbonnelVerticalBaseCoordinate, realEuclideanTakeLeft,
    AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

@[simp]
theorem charbonnelVerticalLastCoordinate_lineMap {n : ℕ}
    (a b : RealEuclidean (n + 1)) (t : ℝ) :
    charbonnelVerticalLastCoordinate (AffineMap.lineMap a b t) =
      AffineMap.lineMap (charbonnelVerticalLastCoordinate a)
        (charbonnelVerticalLastCoordinate b) t := by
  simp only [charbonnelVerticalLastCoordinate,
    AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

/-- If two points of a set cut by a nondegenerate affine line belong to the
same connected component, their entire chord belongs to the set. -/
theorem affineLine_chord_subset_of_connectedComponent_eq
    {d : ℕ} {S : Set (RealEuclidean d)}
    {a b : RealEuclidean d} (hab : a ≠ b)
    {x y : ((S ∩ (affineSpan ℝ {a, b} : Set (RealEuclidean d))) :
      Set (RealEuclidean d))}
    (hcomponent : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap (x : RealEuclidean d) y t ∈ S := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
  let parameter :
      ((S ∩ (affineSpan ℝ {a, b} : Set (RealEuclidean d))) :
        Set (RealEuclidean d)) → ℝ :=
    fun z ↦ charbonnelAffineLineParameter k a b z
  have hparameter : Continuous parameter :=
    (continuous_charbonnelAffineLineParameter k a b).comp
      continuous_subtype_val
  let rx : ℝ := parameter x
  let ry : ℝ := parameter y
  have hxLine : (x : RealEuclidean d) ∈ affineSpan ℝ {a, b} := x.property.2
  have hyLine : (y : RealEuclidean d) ∈ affineSpan ℝ {a, b} := y.property.2
  have hxRecover : AffineMap.lineMap a b rx = x := by
    exact lineMap_charbonnelAffineLineParameter_eq_of_mem
      k a b hk hxLine
  have hyRecover : AffineMap.lineMap a b ry = y := by
    exact lineMap_charbonnelAffineLineParameter_eq_of_mem
      k a b hk hyLine
  have hyComponent : y ∈ connectedComponent x :=
    ConnectedComponents.coe_eq_coe'.mp hcomponent.symm
  intro t ht
  let r : ℝ := (1 - t) * rx + t * ry
  have hrBetween : r ∈ Set.uIcc rx ry := by
    simpa only [r, AffineMap.lineMap_apply_module, smul_eq_mul] using
      (convex_uIcc rx ry).lineMap_mem Set.left_mem_uIcc
        Set.right_mem_uIcc ht
  have hrImage : r ∈ parameter '' connectedComponent x := by
    rcases le_total rx ry with hxy | hyx
    · rw [Set.uIcc_of_le hxy] at hrBetween
      exact isPreconnected_connectedComponent.intermediate_value
        mem_connectedComponent hyComponent hparameter.continuousOn hrBetween
    · rw [Set.uIcc_comm, Set.uIcc_of_le hyx] at hrBetween
      exact isPreconnected_connectedComponent.intermediate_value
        hyComponent mem_connectedComponent
        hparameter.continuousOn hrBetween
  obtain ⟨z, hzComponent, hzParameter⟩ := hrImage
  have hzLine : (z : RealEuclidean d) ∈ affineSpan ℝ {a, b} := z.property.2
  have hzRecover : AffineMap.lineMap a b r = z := by
    rw [← hzParameter]
    exact lineMap_charbonnelAffineLineParameter_eq_of_mem
      k a b hk hzLine
  have hchord : AffineMap.lineMap (x : RealEuclidean d) y t = z := by
    rw [← hxRecover, ← hyRecover,
      lineMap_lineMap_eq_lineMap_affineCombination]
    exact hzRecover
  rw [hchord]
  exact z.property.1

/-! ## Components represented by real component carriers -/

/-- Membership in a real component carrier is exactly equality of the
corresponding quotient component. -/
theorem mem_realConnectedComponentCarrier_iff_mk_eq
    (s : Set ℝ) (c : ConnectedComponents s) {t : ℝ} (ht : t ∈ s) :
    t ∈ realConnectedComponentCarrier s c ↔
      ConnectedComponents.mk (⟨t, ht⟩ : s) = c := by
  constructor
  · rintro ⟨p, hp, hpt⟩
    have hpComponent : ConnectedComponents.mk p = c :=
      (ConnectedComponents.coe_eq_coe'.mpr hp).trans
        (connectedComponentRepresentative_mk s c)
    have hpeq : p = (⟨t, ht⟩ : s) := by
      apply Subtype.ext
      exact hpt
    simpa only [← hpeq] using hpComponent
  · intro hcomponent
    refine ⟨(⟨t, ht⟩ : s), ?_, rfl⟩
    apply ConnectedComponents.coe_eq_coe'.mp
    exact hcomponent.trans (connectedComponentRepresentative_mk s c).symm

/-! ## Lost branches on one affine line -/

/-- Any selected points from distinct lost branches which lie on one
nondegenerate affine line represent distinct components of that line
section.  Base support keeps every point of the chord in `ω`, while
convexity of the ambient closed ball keeps it in the ball part of the
earlier relative ball. -/
theorem injective_components_of_stationaryLostBranch_points_on_affineLine
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    {ι : Type*} (index : ι → ℕ)
    (hindex : Function.Injective index)
    (a b : RealEuclidean (n + 1)) (hab : a ≠ b)
    (point : ι → RealEuclidean (n + 1))
    (hpoint : ∀ i, point i ∈
      charbonnelSection53_stationaryLostBranch
        sequence hpositive hdelete (index i))
    (hline : ∀ i, point i ∈ affineSpan ℝ {a, b}) :
    Function.Injective (fun i ↦ ConnectedComponents.mk
      (⟨point i, (hpoint i).1, hline i⟩ :
        ((S ∩ (affineSpan ℝ {a, b} : Set (RealEuclidean (n + 1)))) :
          Set (RealEuclidean (n + 1))))) := by
  let sectionPoint : ι →
      ((S ∩ (affineSpan ℝ {a, b} : Set (RealEuclidean (n + 1)))) :
        Set (RealEuclidean (n + 1))) :=
    fun i ↦ ⟨point i, (hpoint i).1, hline i⟩
  have hforward : ∀ {i j : ι}, index i < index j →
      ConnectedComponents.mk (sectionPoint i) =
        ConnectedComponents.mk (sectionPoint j) → False := by
    intro i j hlt hcomponents
    let pi : ((S ∩
        (affineSpan ℝ {a, b} : Set (RealEuclidean (n + 1)))) :
          Set (RealEuclidean (n + 1))) :=
      ⟨point i, (hpoint i).1, hline i⟩
    let pj : ((S ∩
        (affineSpan ℝ {a, b} : Set (RealEuclidean (n + 1)))) :
          Set (RealEuclidean (n + 1))) :=
      ⟨point j, (hpoint j).1, hline j⟩
    have hchord : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap (point i) (point j) t ∈ S := by
      exact affineLine_chord_subset_of_connectedComponent_eq hab
        (x := pi) (y := pj) hcomponents
    let scalarChord : Set ℝ :=
      AffineMap.lineMap
        (charbonnelVerticalLastCoordinate (point i))
        (charbonnelVerticalLastCoordinate (point j)) ''
          Set.Icc (0 : ℝ) 1
    have hscalarPreconnected : IsPreconnected scalarChord :=
      isPreconnected_Icc.image _ AffineMap.lineMap_continuous.continuousOn
    have hscalarSubset : scalarChord ⊆
        charbonnelVerticalImageOver S
          (charbonnelSection53StationaryBall sequence (index i)) := by
      rintro t ⟨u, hu, rfl⟩
      let z := AffineMap.lineMap (point i) (point j) u
      have hzS : z ∈ S := hchord u hu
      have hiBase := (hpoint i).2.1
      have hjBase : charbonnelVerticalBaseCoordinate (point j) ∈
          charbonnelSection53StationaryBall sequence (index i) := by
        exact (antitone_charbonnelSection53_stationaryBall sequence hdelete)
          (Nat.le_of_lt hlt) (hpoint j).2.1
      have hzBase : charbonnelVerticalBaseCoordinate z ∈
          charbonnelSection53StationaryBall sequence (index i) := by
        refine ⟨?_, ?_⟩
        · exact hbase z hzS
        · rw [charbonnelVerticalBaseCoordinate_lineMap]
          exact (convex_closedBall (sequence (index i)).1.1.center
            (sequence (index i)).1.1.radius).lineMap_mem
              hiBase.2 hjBase.2 hu
      refine ⟨charbonnelVerticalBaseCoordinate z, hzBase, ?_⟩
      have hzLast :
          AffineMap.lineMap
              (charbonnelVerticalLastCoordinate (point i))
              (charbonnelVerticalLastCoordinate (point j)) u =
            charbonnelVerticalLastCoordinate z := by
        symm
        exact charbonnelVerticalLastCoordinate_lineMap (point i) (point j) u
      rw [hzLast]
      simpa only [charbonnelVerticalBaseCoordinate,
        charbonnelVerticalLastCoordinate,
        charbonnelAppendLastCoordinate_takeLeft_last] using hzS
    have hiScalar : charbonnelVerticalLastCoordinate (point i) ∈
        scalarChord := by
      refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp [AffineMap.lineMap_apply_module]
    have hjScalar : charbonnelVerticalLastCoordinate (point j) ∈
        scalarChord := by
      refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp [AffineMap.lineMap_apply_module]
    let Vi : Set ℝ := charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence (index i))
    have hiVi : charbonnelVerticalLastCoordinate (point i) ∈ Vi :=
      realConnectedComponentCarrier_subset_self _ _ (hpoint i).2.2
    have hjVi : charbonnelVerticalLastCoordinate (point j) ∈ Vi :=
      hscalarSubset hjScalar
    have hjConnected :
        (⟨charbonnelVerticalLastCoordinate (point j), hjVi⟩ : Vi) ∈
          connectedComponent
            (⟨charbonnelVerticalLastCoordinate (point i), hiVi⟩ : Vi) :=
      mem_connectedComponent_of_mem_preconnected_subset
        hiVi hjVi hiScalar hjScalar hscalarSubset hscalarPreconnected
    have hcomponentEq :
        ConnectedComponents.mk
            (⟨charbonnelVerticalLastCoordinate (point j), hjVi⟩ : Vi) =
          charbonnelSection53_stationaryLostComponent
            sequence hpositive hdelete (index i) := by
      have hji : ConnectedComponents.mk
          (⟨charbonnelVerticalLastCoordinate (point j), hjVi⟩ : Vi) =
          ConnectedComponents.mk
            (⟨charbonnelVerticalLastCoordinate (point i), hiVi⟩ : Vi) :=
        ConnectedComponents.coe_eq_coe'.mpr hjConnected
      exact hji.trans
        ((mem_realConnectedComponentCarrier_iff_mk_eq Vi
          (charbonnelSection53_stationaryLostComponent
            sequence hpositive hdelete (index i)) hiVi).mp (hpoint i).2.2)
    have hjInLost : charbonnelVerticalLastCoordinate (point j) ∈
        charbonnelSection53_stationaryLostCarrier
          sequence hpositive hdelete (index i) :=
      (mem_realConnectedComponentCarrier_iff_mk_eq Vi
        (charbonnelSection53_stationaryLostComponent
          sequence hpositive hdelete (index i)) hjVi).mpr hcomponentEq
    have hjNext : charbonnelVerticalLastCoordinate (point j) ∈
        charbonnelVerticalImageOver S
          (charbonnelSection53StationaryBall sequence (index i + 1)) := by
      apply charbonnelVerticalImageOver_mono S
        ((antitone_charbonnelSection53_stationaryBall sequence hdelete)
          (Nat.succ_le_iff.mpr hlt))
      exact realConnectedComponentCarrier_subset_self _ _ (hpoint j).2.2
    exact (Set.disjoint_left.mp
      (disjoint_charbonnelSection53_stationaryLostCarrier_successorImage
        sequence hpositive hdelete (index i))) hjInLost hjNext
  intro i j hcomponents
  by_contra hij
  have hindexNe : index i ≠ index j := fun h ↦ hij (hindex h)
  rcases lt_or_gt_of_ne hindexNe with hlt | hgt
  · exact hforward hlt hcomponents
  · exact hforward hgt hcomponents.symm

/-! ## The finite collinear-incidence residual -/

/-- The remaining incidence statement after affine-line separation: every
finite prefix of the canonical lost branches has a transversal on one
nondegenerate affine line.  It does not include any connected-component
claim. -/
def CharbonnelSection53LostBranchCollinearSelection
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
      ∃ (a b : RealEuclidean (n + 1))
        (point : Fin (N + 1) → RealEuclidean (n + 1)),
        a ≠ b ∧
        (∀ i, point i ∈ charbonnelSection53_stationaryLostBranch
          sequence hpositive hdelete i.1) ∧
        ∀ i, point i ∈ affineSpan ℝ {a, b}

/-- A collinear transversal over a convex base supplies the exact affine
separation residual from the collision iteration. -/
theorem charbonnelSection53_lostBranchAffineSeparation_of_collinearSelection
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (hcollinear : CharbonnelSection53LostBranchCollinearSelection ω S) :
    CharbonnelSection53LostBranchAffineSeparation ω S := by
  intro sequence hpositive hdelete hradius N
  obtain ⟨a, b, rawPoint, hab, hbranch, hline⟩ :=
    hcollinear sequence hpositive hdelete hradius N
  let V : AffineSubspace ℝ (RealEuclidean (n + 1)) := affineSpan ℝ {a, b}
  let point : Fin (N + 1) →
      ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
        Set (RealEuclidean (n + 1))) :=
    fun i ↦ ⟨rawPoint i, (hbranch i).1, hline i⟩
  refine ⟨V, point, ?_, ?_⟩
  · intro i
    exact hbranch i
  · exact injective_components_of_stationaryLostBranch_points_on_affineLine
      hbase sequence hpositive hdelete (fun i : Fin (N + 1) ↦ i.1)
        Fin.val_injective a b hab rawPoint hbranch hline

/-! ## The first nontrivial finite prefix -/

/-- A canonical point in the lost branch at one stage. -/
def charbonnelSection53_stationaryLostBranchPoint
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) : RealEuclidean (n + 1) :=
  Classical.choose
    (charbonnelSection53_stationaryLostBranch_nonempty
      sequence hpositive hdelete m)

theorem charbonnelSection53_stationaryLostBranchPoint_mem
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (m : ℕ) :
    charbonnelSection53_stationaryLostBranchPoint
        sequence hpositive hdelete m ∈
      charbonnelSection53_stationaryLostBranch
        sequence hpositive hdelete m :=
  Classical.choose_spec
    (charbonnelSection53_stationaryLostBranch_nonempty
      sequence hpositive hdelete m)

/-- The first two canonical lost-branch points are distinct. -/
theorem charbonnelSection53_stationaryLostBranchPoint_zero_ne_one
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) :
    charbonnelSection53_stationaryLostBranchPoint
        sequence hpositive hdelete 0 ≠
      charbonnelSection53_stationaryLostBranchPoint
        sequence hpositive hdelete 1 := by
  intro heq
  have hdisjoint :=
    pairwiseDisjoint_charbonnelSection53_stationaryLostBranch
      sequence hpositive hdelete (Set.mem_univ 0) (Set.mem_univ 1) (by omega)
  exact (Set.disjoint_left.mp hdisjoint)
    (charbonnelSection53_stationaryLostBranchPoint_mem
      sequence hpositive hdelete 0)
    (heq ▸ charbonnelSection53_stationaryLostBranchPoint_mem
      sequence hpositive hdelete 1)

/-- For a base-supported source, the first two lost branches already have
representatives in distinct components of a common affine section.  This is
the `N = 1` instance of the exact residual, proved from the iteration alone. -/
theorem exists_two_stationaryLostBranch_points_affineSeparated
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hpositive : (sequence 0).1.1.defectCount ≠ 0)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) :
    ∃ (V : AffineSubspace ℝ (RealEuclidean (n + 1)))
      (point : Fin 2 →
        ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
          Set (RealEuclidean (n + 1)))),
      (∀ i, (point i).1 ∈
        charbonnelSection53_stationaryLostBranch
          sequence hpositive hdelete i.1) ∧
      Function.Injective (fun i ↦ ConnectedComponents.mk (point i)) := by
  let a := charbonnelSection53_stationaryLostBranchPoint
    sequence hpositive hdelete 0
  let b := charbonnelSection53_stationaryLostBranchPoint
    sequence hpositive hdelete 1
  have hab : a ≠ b :=
    charbonnelSection53_stationaryLostBranchPoint_zero_ne_one
      sequence hpositive hdelete
  let rawPoint : Fin 2 → RealEuclidean (n + 1) := fun i ↦
    Fin.cases a (fun _ ↦ b) i
  have hrawZero : rawPoint 0 = a := rfl
  have hrawOne : rawPoint 1 = b := rfl
  have hbranch : ∀ i : Fin 2, rawPoint i ∈
      charbonnelSection53_stationaryLostBranch
        sequence hpositive hdelete i.1 := by
    intro i
    fin_cases i
    · exact charbonnelSection53_stationaryLostBranchPoint_mem
        sequence hpositive hdelete 0
    · exact charbonnelSection53_stationaryLostBranchPoint_mem
        sequence hpositive hdelete 1
  let V : AffineSubspace ℝ (RealEuclidean (n + 1)) := affineSpan ℝ {a, b}
  have hline : ∀ i : Fin 2, rawPoint i ∈ V := by
    intro i
    apply subset_affineSpan ℝ
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  let point : Fin 2 →
      ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
        Set (RealEuclidean (n + 1))) :=
    fun i ↦ ⟨rawPoint i, (hbranch i).1, hline i⟩
  refine ⟨V, point, ?_, ?_⟩
  · intro i
    exact hbranch i
  · exact injective_components_of_stationaryLostBranch_points_on_affineLine
      hbase sequence hpositive hdelete (fun i : Fin 2 ↦ i.1)
        Fin.val_injective a b hab rawPoint hbranch hline

end AbelFormalization
