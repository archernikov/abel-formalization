import AbelFormalization.CharbonnelSection53GlobalDichotomy

/-!
# The sound limiting support argument in Charbonnel 5.3(c)

The printed proof forms the projection `ω′` of the fibers meeting each of
several disjoint neighborhoods of the limit fiber's components.  For an
arbitrary compact set this projection need not be a neighborhood: an
isolated vertical spike has no nearby support.  In the stationary chain,
however, the next ball avoids `β_m`, the union of *defective* component
supports.  Consequently, a component that meets the limit fiber must have
full support on the preceding ball.  Compactness localizes all late vertical
images near the limit fiber.  These are the elementary pieces behind the
paper's neighborhood claim.

Deletion and compactness do not by themselves imply that the limit fiber
has the same component count as every ball in the global `M` stratum: new
components may collapse into a limit component.  The final theorem below
isolates precisely the needed no-collapse assertion and proves that it
rules out a stationary chain.  No no-collapse fact is asserted from WS5.
-/

noncomputable section

open Set Filter

namespace AbelFormalization

set_option autoImplicit false

/-- The relative closed ball carried by one index of a candidate sequence. -/
def charbonnelSection53StationaryBall
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (m : ℕ) : Set (RealEuclidean n) :=
  charbonnelRelativeClosedBall ω
    (sequence m).1.1.center (sequence m).1.1.radius

/-- Nested positive relative balls in a compact base have a common point.
The limit of their radii is not needed for this existence step. -/
theorem exists_charbonnelSection53_stationaryLimitPoint
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hnested : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m) :
    ∃ x : RealEuclidean n,
      ∀ m, x ∈ charbonnelSection53StationaryBall sequence m := by
  let B : ℕ → Set (RealEuclidean n) :=
    charbonnelSection53StationaryBall sequence
  have hBnonempty : ∀ m, (B m).Nonempty := by
    intro m
    exact charbonnelRelativeClosedBall_nonempty
      (sequence m).1.1.center_mem (sequence m).1.1.radius_pos.le
  have hBclosed : ∀ m, IsClosed (B m) := by
    intro m
    exact charbonnelRelativeClosedBall_isClosed hω.isClosed
      (sequence m).1.1.center (sequence m).1.1.radius
  have hBcompact : IsCompact (B 0) :=
    charbonnelRelativeClosedBall_isCompact hω
      (sequence 0).1.1.center (sequence 0).1.1.radius
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      B hnested hBnonempty hBcompact hBclosed
  exact ⟨x, Set.mem_iInter.mp hx⟩

/-- Radii tending to zero make the common point unique. -/
theorem charbonnelSection53_stationaryLimitPoint_unique
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hradius : Tendsto (fun m : ℕ ↦ (sequence m).1.1.radius)
      atTop (nhds 0))
    {x y : RealEuclidean n}
    (hx : ∀ m, x ∈ charbonnelSection53StationaryBall sequence m)
    (hy : ∀ m, y ∈ charbonnelSection53StationaryBall sequence m) :
    x = y := by
  have hdist (m : ℕ) :
      dist x y ≤ 2 * (sequence m).1.1.radius := by
    have hxm := Metric.mem_closedBall.mp (hx m).2
    have hym := Metric.mem_closedBall.mp (hy m).2
    have htri := dist_triangle x (sequence m).1.1.center y
    rw [dist_comm (sequence m).1.1.center y] at htri
    linarith
  have htwice : Tendsto
      (fun m : ℕ ↦ 2 * (sequence m).1.1.radius)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hradius.const_mul 2
  have hzero : dist x y ≤ 0 := ge_of_tendsto' htwice hdist
  exact dist_eq_zero.mp (le_antisymm hzero (dist_nonneg : 0 ≤ dist x y))

/-- If closed base sets shrink to one point, compactness of `S` puts all
late vertical images into any open neighborhood of that point's fiber.
This is the compactness claim used before the source compares `M′` with
the global ball count `M`. -/
theorem charbonnelSection53_compact_verticalImage_eventually_subset_open
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : IsCompact S)
    (B : ℕ → Set (RealEuclidean n))
    (hBclosed : ∀ m, IsClosed (B m))
    (hBnest : ∀ m, B (m + 1) ⊆ B m)
    {x : RealEuclidean n}
    (hintersection : (⋂ m, B m) = {x})
    {U : Set ℝ} (hU : IsOpen U)
    (hfiber : ∀ t : ℝ,
      charbonnelAppendLastCoordinate x t ∈ S → t ∈ U) :
    ∃ m, charbonnelVerticalImageOver S (B m) ⊆ U := by
  by_contra hnone
  have hbad : ∀ m, ∃ t ∈ charbonnelVerticalImageOver S (B m),
      t ∉ U := by
    intro m
    by_contra hnot
    apply hnone
    refine ⟨m, ?_⟩
    intro t ht
    by_contra htU
    exact hnot ⟨t, ht, htU⟩
  let K : ℕ → Set (RealEuclidean (n + 1)) := fun m ↦
    (S ∩ charbonnelVerticalBaseCoordinate ⁻¹' B m) ∩
      charbonnelVerticalLastCoordinate ⁻¹' Uᶜ
  have hKnonempty : ∀ m, (K m).Nonempty := by
    intro m
    obtain ⟨t, ⟨y, hyB, hytS⟩, htU⟩ := hbad m
    refine ⟨charbonnelAppendLastCoordinate y t, ⟨⟨hytS, ?_⟩, ?_⟩⟩
    · change realEuclideanTakeLeft
        (charbonnelAppendLastCoordinate y t) ∈ B m
      simpa only [charbonnelAppendLastCoordinate,
        realEuclideanTakeLeft_append] using hyB
    · change charbonnelAppendLastCoordinate y t (Fin.last n) ∈ Uᶜ
      simpa only [Set.mem_compl_iff,
        charbonnelAppendLastCoordinate_last] using htU
  have hKclosed : ∀ m, IsClosed (K m) := by
    intro m
    exact (hS.isClosed.inter
      ((hBclosed m).preimage
        continuous_charbonnelVerticalBaseCoordinate)).inter
          (hU.isClosed_compl.preimage
            continuous_charbonnelVerticalLastCoordinate)
  have hKcompact : IsCompact (K 0) :=
    (hS.inter_right
      ((hBclosed 0).preimage
        continuous_charbonnelVerticalBaseCoordinate)).inter_right
          (hU.isClosed_compl.preimage
            continuous_charbonnelVerticalLastCoordinate)
  have hKnest : ∀ m, K (m + 1) ⊆ K m := by
    intro m z hz
    exact ⟨⟨hz.1.1, hBnest m hz.1.2⟩, hz.2⟩
  obtain ⟨z, hzall⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hKnest hKnonempty hKcompact hKclosed
  have hzK (m : ℕ) : z ∈ K m := Set.mem_iInter.mp hzall m
  have hzbaseAll : charbonnelVerticalBaseCoordinate z ∈ ⋂ m, B m :=
    Set.mem_iInter.mpr (fun m ↦ (hzK m).1.2)
  have hzbase : charbonnelVerticalBaseCoordinate z = x := by
    rw [hintersection] at hzbaseAll
    exact Set.mem_singleton_iff.mp hzbaseAll
  have hzFiber :
      charbonnelAppendLastCoordinate x
        (charbonnelVerticalLastCoordinate z) ∈ S := by
    rw [← hzbase]
    change charbonnelAppendLastCoordinate
      (realEuclideanTakeLeft z) (z (Fin.last n)) ∈ S
    simpa only [charbonnelAppendLastCoordinate_takeLeft_last]
      using (hzK 0).1.1
  exact (hzK 0).2 (hfiber _ hzFiber)

/-- Specialization of compact vertical localization to a stationary chain.
The next ball deletion is used only for nesting; shrinking radii establish
the singleton intersection. -/
theorem charbonnelSection53_stationary_verticalImage_eventually_subset_open
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω) (hS : IsCompact S)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (hradius : Tendsto (fun m : ℕ ↦ (sequence m).1.1.radius)
      atTop (nhds 0))
    {x : RealEuclidean n}
    (hx : ∀ m, x ∈ charbonnelSection53StationaryBall sequence m)
    {U : Set ℝ} (hU : IsOpen U)
    (hfiber : ∀ t : ℝ,
      charbonnelAppendLastCoordinate x t ∈ S → t ∈ U) :
    ∃ m, charbonnelVerticalImageOver S
      (charbonnelSection53StationaryBall sequence m) ⊆ U := by
  let B : ℕ → Set (RealEuclidean n) :=
    charbonnelSection53StationaryBall sequence
  have hBclosed : ∀ m, IsClosed (B m) := by
    intro m
    exact charbonnelRelativeClosedBall_isClosed hω.isClosed
      (sequence m).1.1.center (sequence m).1.1.radius
  have hBnest : ∀ m, B (m + 1) ⊆ B m := by
    intro m y hy
    exact (hdelete m hy).1
  have hintersection : (⋂ m, B m) = {x} := by
    ext y
    constructor
    · intro hy
      have hxy := charbonnelSection53_stationaryLimitPoint_unique
        sequence hradius hx (Set.mem_iInter.mp hy)
      simpa only [Set.mem_singleton_iff] using hxy.symm
    · intro hy
      have hxy : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact Set.mem_iInter.mpr hx
  exact charbonnelSection53_compact_verticalImage_eventually_subset_open
    hS B hBclosed hBnest hintersection hU hfiber

/-- A connected set meeting one member of a pairwise disjoint open cover
lies wholly inside that member.  This is the purely topological component
localization used for the source's separated intervals `Ωᵢ`. -/
theorem charbonnelSection53_preconnected_subset_one_disjointOpenCover
    {ι : Type*} (Ω : ι → Set ℝ)
    (hopen : ∀ i, IsOpen (Ω i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Ω i) (Ω j))
    {s : Set ℝ} (hs : IsPreconnected s)
    (hcover : s ⊆ ⋃ i, Ω i)
    (i : ι) (hinter : (s ∩ Ω i).Nonempty) :
    s ⊆ Ω i := by
  let V : Set ℝ := ⋃ j : ι, ⋃ (_ : j ≠ i), Ω j
  have hVopen : IsOpen V :=
    isOpen_iUnion (fun j ↦ isOpen_iUnion (fun _ ↦ hopen j))
  have hVdisjoint : Disjoint (Ω i) V := by
    rw [Set.disjoint_left]
    intro t hti htV
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp htV
    obtain ⟨hji, htj⟩ := Set.mem_iUnion.mp hj
    exact (Set.disjoint_left.mp (hdisjoint i j hji.symm)) hti htj
  have hUVcover : s ⊆ Ω i ∪ V := by
    intro t hts
    obtain ⟨j, htj⟩ := Set.mem_iUnion.mp (hcover hts)
    by_cases hji : j = i
    · subst j
      exact Or.inl htj
    · exact Or.inr (Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨hji, htj⟩⟩)
  exact hs.subset_left_of_subset_union
    (hopen i) hVopen hVdisjoint hUVcover hinter

/-- The projection of the part of `S` whose final coordinate lies in one
chosen open interval. -/
def charbonnelSection53FiberOpenProjection
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (U : Set ℝ) : Set (RealEuclidean n) :=
  {y | ∃ t ∈ U, charbonnelAppendLastCoordinate y t ∈ S}

/-- The source's `ω′` is a relative neighborhood of the limit point **for
a stationary deletion chain**.  Every limit-fiber component meeting one
`Ωᵢ` belongs to a full-supported component of a late ball, and compactness
keeps that entire ball component inside `Ωᵢ`.  The theorem permits other
ball components to collapse into the same `Ωᵢ`; it does not assert `M′=M`. -/
theorem exists_charbonnelSection53_stationaryBall_subset_fiberOpenProjections
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω) (hS : IsCompact S)
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    (hradius : Tendsto (fun m : ℕ ↦ (sequence m).1.1.radius)
      atTop (nhds 0))
    {x : RealEuclidean n}
    (hx : ∀ m, x ∈ charbonnelSection53StationaryBall sequence m)
    {ι : Type*} (Ω : ι → Set ℝ)
    (hopen : ∀ i, IsOpen (Ω i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Ω i) (Ω j))
    (hfiberCover : ∀ t : ℝ,
      charbonnelAppendLastCoordinate x t ∈ S → t ∈ ⋃ i, Ω i)
    (hfiberMeets : ∀ i, ∃ t ∈ Ω i,
      charbonnelAppendLastCoordinate x t ∈ S) :
    ∃ m, charbonnelSection53StationaryBall sequence m ⊆
      ⋂ i, charbonnelSection53FiberOpenProjection S (Ω i) := by
  have hUnionOpen : IsOpen (⋃ i, Ω i) :=
    isOpen_iUnion hopen
  obtain ⟨m, hlate⟩ :=
    charbonnelSection53_stationary_verticalImage_eventually_subset_open
      hω hS sequence hdelete hradius hx hUnionOpen hfiberCover
  let B : Set (RealEuclidean n) :=
    charbonnelSection53StationaryBall sequence m
  let V : Set ℝ := charbonnelVerticalImageOver S B
  have hxnot : x ∉
      charbonnelRelativeDefectiveSupportUnion (sequence m).1.1 :=
    (hdelete m (hx (m + 1))).2
  refine ⟨m, ?_⟩
  intro y hyB
  apply Set.mem_iInter.mpr
  intro i
  obtain ⟨t, htΩ, hxtS⟩ := hfiberMeets i
  have htV : t ∈ V := ⟨x, hx m, hxtS⟩
  have htUnion : t ∈ ⋃ c : ConnectedComponents V,
      realConnectedComponentCarrier V c := by
    rw [iUnion_realConnectedComponentCarrier V]
    exact htV
  obtain ⟨c, htc⟩ := Set.mem_iUnion.mp htUnion
  have hcInside : realConnectedComponentCarrier V c ⊆ Ω i := by
    apply charbonnelSection53_preconnected_subset_one_disjointOpenCover
      Ω hopen hdisjoint
      (isConnected_realConnectedComponentCarrier V c).isPreconnected
    · intro r hr
      have hrV : r ∈ V := by
        rw [← iUnion_realConnectedComponentCarrier V]
        exact Set.mem_iUnion.mpr ⟨c, hr⟩
      exact hlate hrV
    · exact ⟨t, htc, htΩ⟩
  have hxSupport : x ∈ charbonnelVerticalComponentBaseSupport S B c :=
    ⟨hx m, t, htc, hxtS⟩
  have hfull : charbonnelVerticalComponentBaseSupport S B c = B := by
    by_contra hdefective
    apply hxnot
    unfold charbonnelRelativeDefectiveSupportUnion
    refine Set.mem_iUnion.mpr ⟨c, ?_⟩
    change x ∈ (if charbonnelVerticalComponentBaseSupport S B c = B
      then (∅ : Set (RealEuclidean n))
      else charbonnelVerticalComponentBaseSupport S B c)
    simpa only [if_neg hdefective] using hxSupport
  have hySupport : y ∈ charbonnelVerticalComponentBaseSupport S B c := by
    rw [hfull]
    exact hyB
  obtain ⟨_hyB, r, hrComp, hyrS⟩ := hySupport
  exact ⟨r, hcInside hrComp, hyrS⟩

/-- A stationary chain's common point avoids every deleted defective
support union. -/
theorem charbonnelSection53_stationaryLimit_not_mem_defectiveSupport
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdelete : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1)
    {x : RealEuclidean n}
    (hx : ∀ m, x ∈ charbonnelSection53StationaryBall sequence m) :
    ∀ m, x ∉ charbonnelRelativeDefectiveSupportUnion (sequence m).1.1 := by
  intro m
  exact (hdelete m (hx (m + 1))).2

/-- If a point outside `β` lies in one component's base support, that
component cannot be defective: its support equals the whole ball. -/
theorem charbonnelSection53_support_eq_ball_of_outside_defectiveUnion
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    {x : RealEuclidean n}
    (hxnot : x ∉ charbonnelRelativeDefectiveSupportUnion candidate)
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ))
    (hxSupport : x ∈ charbonnelVerticalComponentBaseSupport S
      (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c) :
    charbonnelVerticalComponentBaseSupport S
      (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c =
        charbonnelRelativeClosedBall ω candidate.center candidate.radius := by
  by_contra hdefective
  apply hxnot
  unfold charbonnelRelativeDefectiveSupportUnion
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  simp only [if_neg hdefective]
  exact hxSupport

/-- Meeting every component at a point outside `β` forces zero defect.
This is the exact final finite-cardinality step of the stationary-chain
contradiction. -/
theorem charbonnelSection53_defect_zero_of_limit_hits_all_components
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    {x : RealEuclidean n}
    (hxnot : x ∉ charbonnelRelativeDefectiveSupportUnion candidate)
    (hhit : ∀ c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ),
      x ∈ charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c) :
    candidate.defectCount = 0 := by
  let Bad := {c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ) //
      charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c ≠
          charbonnelRelativeClosedBall ω candidate.center candidate.radius}
  have hbadEmpty : IsEmpty Bad := ⟨fun bad ↦
    bad.2 (charbonnelSection53_support_eq_ball_of_outside_defectiveUnion
      candidate hxnot bad.1 (hhit bad.1))⟩
  change Nat.card Bad = 0
  exact (Nat.card_eq_zero (α := Bad)).mpr (Or.inl hbadEmpty)

/-- The exact component-count stabilization still missing after the
compact/deletion bridges: at one stage of any stationary chain, the limit
base point meets **every** global-stratum component.  A collapsing
dense-spike construction shows this is not a theorem of compactness and a
numerical vertical bound alone.  Its derivation from full WS5/Charbonnel
membership is the remaining source argument. -/
def CharbonnelSection53NoLimitComponentCollapse
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∀ sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
    (∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m \
          charbonnelRelativeDefectiveSupportUnion (sequence m).1.1) →
    Tendsto (fun m : ℕ ↦ (sequence m).1.1.radius) atTop (nhds 0) →
    ∀ x : RealEuclidean n,
      (∀ m, x ∈ charbonnelSection53StationaryBall sequence m) →
        ∃ m, ∀ c : ConnectedComponents
          (charbonnelVerticalImageOver S
            (charbonnelSection53StationaryBall sequence m) : Set ℝ),
          x ∈ charbonnelVerticalComponentBaseSupport S
            (charbonnelSection53StationaryBall sequence m) c

/-- Compact nested-ball intersection and deletion reduce the entire
stationary-chain exclusion to no collapse of global components at the
limit fiber. -/
theorem charbonnelSection53_noStationary_of_noLimitComponentCollapse
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω)
    (hnocollapse : CharbonnelSection53NoLimitComponentCollapse ω S) :
    CharbonnelSection53NoStationaryNestedSequence ω S := by
  rintro ⟨sequence, hpositive, hdelete, hradius⟩
  have hnested : ∀ m,
      charbonnelSection53StationaryBall sequence (m + 1) ⊆
        charbonnelSection53StationaryBall sequence m := by
    intro m x hx
    exact (hdelete m hx).1
  obtain ⟨x, hx⟩ :=
    exists_charbonnelSection53_stationaryLimitPoint hω sequence hnested
  obtain ⟨m, hhit⟩ := hnocollapse sequence hdelete hradius x hx
  have hxnot :=
    charbonnelSection53_stationaryLimit_not_mem_defectiveSupport
      sequence hdelete hx m
  have hzero : (sequence m).1.1.defectCount = 0 :=
    charbonnelSection53_defect_zero_of_limit_hits_all_components
      (sequence m).1.1 hxnot hhit
  have heq :=
    charbonnelRelativeMinimalDefectGlobalCandidates_defect_eq
      (sequence m) (sequence 0)
  exact hpositive (heq.symm.trans hzero)

end AbelFormalization
