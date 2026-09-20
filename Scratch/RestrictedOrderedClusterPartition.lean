import AbelFormalization.RestrictedRepresentativeClusters
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Sort

/-!
# Ordered finite partition into representative clusters

Starting from `RepresentativeClusterSubsequence`, this file turns bounded
pairwise Abel-time gap into an actual finite partition.  Each class is
indexed by the first position where it occurs in the fixed sorted order.
This gives canonical first and last representatives, pointwise interval
bounds, a common cluster width, and divergent signed gaps between ordered
clusters.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

set_option autoImplicit false

variable {m : ℕ} {time : ℕ → Fin m → ℝ}

/-- The bounded-gap equivalence relation as a bundled setoid. -/
def sameClusterSetoid (data : RepresentativeClusterSubsequence time) :
    Setoid (Fin m) where
  r := data.SameCluster
  iseqv := data.sameCluster_equivalence

/-- The finite partition of representative labels into bounded-gap
classes. -/
def clusterFinpartition (data : RepresentativeClusterSubsequence time) :
    Finpartition (Finset.univ : Finset (Fin m)) := by
  classical
  exact Finpartition.ofSetoid data.sameClusterSetoid

@[simp]
theorem mem_clusterFinpartition_part_iff
    (data : RepresentativeClusterSubsequence time) (i j : Fin m) :
    j ∈ data.clusterFinpartition.part i ↔ data.SameCluster i j := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- A position in the fixed sorted order is the leader of its cluster when
no earlier position belongs to the same cluster. -/
def IsClusterLeader (data : RepresentativeClusterSubsequence time)
    (i : Fin m) : Prop :=
  ∀ j : Fin m, j < i →
    ¬ data.SameCluster (data.order j) (data.order i)

/-- All first positions of bounded-gap classes. -/
def clusterLeaderPositions (data : RepresentativeClusterSubsequence time) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter data.IsClusterLeader

/-- The number of bounded-gap classes. -/
def orderedClusterCount (data : RepresentativeClusterSubsequence time) : ℕ :=
  data.clusterLeaderPositions.card

/-- The leader of cluster `c`, in the fixed sorted position coordinates. -/
def orderedClusterLeaderPosition
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : Fin m :=
  (data.clusterLeaderPositions.orderIsoOfFin rfl c :
    data.clusterLeaderPositions)

@[simp]
theorem orderedClusterLeaderPosition_mem
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.orderedClusterLeaderPosition c ∈ data.clusterLeaderPositions :=
  (data.clusterLeaderPositions.orderIsoOfFin rfl c).property

theorem orderedClusterLeaderPosition_isLeader
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.IsClusterLeader (data.orderedClusterLeaderPosition c) := by
  classical
  have h := data.orderedClusterLeaderPosition_mem c
  rw [clusterLeaderPositions, Finset.mem_filter] at h
  exact h.2

/-- Cluster `c`, as a finset of the original representative labels. -/
def orderedCluster (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : Finset (Fin m) :=
  data.clusterFinpartition.part
    (data.order (data.orderedClusterLeaderPosition c))

@[simp]
theorem mem_orderedCluster_iff
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (i : Fin m) :
    i ∈ data.orderedCluster c ↔
      data.SameCluster
        (data.order (data.orderedClusterLeaderPosition c)) i := by
  exact data.mem_clusterFinpartition_part_iff _ _

theorem orderedCluster_nonempty
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    (data.orderedCluster c).Nonempty := by
  refine ⟨data.order (data.orderedClusterLeaderPosition c), ?_⟩
  rw [mem_orderedCluster_iff]
  exact data.sameCluster_equivalence.refl _

/-- Positions in the fixed order belonging to the class of position `i`. -/
def sameClusterPositions (data : RepresentativeClusterSubsequence time)
    (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j =>
    data.SameCluster (data.order i) (data.order j)

@[simp]
theorem mem_sameClusterPositions_iff
    (data : RepresentativeClusterSubsequence time) (i j : Fin m) :
    j ∈ data.sameClusterPositions i ↔
      data.SameCluster (data.order i) (data.order j) := by
  classical
  simp [sameClusterPositions]

theorem sameClusterPositions_nonempty
    (data : RepresentativeClusterSubsequence time) (i : Fin m) :
    (data.sameClusterPositions i).Nonempty := by
  refine ⟨i, ?_⟩
  rw [mem_sameClusterPositions_iff]
  exact data.sameCluster_equivalence.refl _

/-- The first sorted position in the class of position `i`. -/
def firstSameClusterPosition
    (data : RepresentativeClusterSubsequence time) (i : Fin m) : Fin m :=
  (data.sameClusterPositions i).min' (data.sameClusterPositions_nonempty i)

theorem firstSameClusterPosition_mem
    (data : RepresentativeClusterSubsequence time) (i : Fin m) :
    data.firstSameClusterPosition i ∈ data.sameClusterPositions i :=
  Finset.min'_mem _ _

theorem firstSameClusterPosition_le
    (data : RepresentativeClusterSubsequence time) (i : Fin m) :
    data.firstSameClusterPosition i ≤ i :=
  Finset.min'_le _ _ (by
    rw [mem_sameClusterPositions_iff]
    exact data.sameCluster_equivalence.refl _)

theorem firstSameClusterPosition_isLeader
    (data : RepresentativeClusterSubsequence time) (i : Fin m) :
    data.IsClusterLeader (data.firstSameClusterPosition i) := by
  intro j hj hsame
  have hfirst : data.SameCluster (data.order i)
      (data.order (data.firstSameClusterPosition i)) := by
    rw [← mem_sameClusterPositions_iff]
    exact data.firstSameClusterPosition_mem i
  have hjmem : j ∈ data.sameClusterPositions i := by
    rw [mem_sameClusterPositions_iff]
    exact data.sameCluster_equivalence.trans hfirst
      (data.sameCluster_equivalence.symm hsame)
  exact (not_le_of_gt hj) (Finset.min'_le _ _ hjmem)

theorem firstSameClusterPosition_mem_leaders
    (data : RepresentativeClusterSubsequence time) (i : Fin m) :
    data.firstSameClusterPosition i ∈ data.clusterLeaderPositions := by
  classical
  rw [clusterLeaderPositions, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, data.firstSameClusterPosition_isLeader i⟩

/-- Every leader occurs exactly once in the finite increasing enumeration
used to index ordered clusters. -/
theorem exists_orderedClusterLeaderPosition_eq
    (data : RepresentativeClusterSubsequence time) {i : Fin m}
    (hi : i ∈ data.clusterLeaderPositions) :
    ∃ c : Fin data.orderedClusterCount,
      data.orderedClusterLeaderPosition c = i := by
  let e := data.clusterLeaderPositions.orderIsoOfFin rfl
  let x : data.clusterLeaderPositions := ⟨i, hi⟩
  refine ⟨e.symm x, ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply x)

/-- Distinct leader positions represent distinct bounded-gap classes. -/
theorem not_sameCluster_order_of_distinct_leaders
    (data : RepresentativeClusterSubsequence time) {i j : Fin m}
    (hi : i ∈ data.clusterLeaderPositions)
    (hj : j ∈ data.clusterLeaderPositions) (hij : i ≠ j) :
    ¬ data.SameCluster (data.order i) (data.order j) := by
  classical
  have hiLeader : data.IsClusterLeader i := by
    rw [clusterLeaderPositions, Finset.mem_filter] at hi
    exact hi.2
  have hjLeader : data.IsClusterLeader j := by
    rw [clusterLeaderPositions, Finset.mem_filter] at hj
    exact hj.2
  intro hsame
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hjLeader i hijlt hsame
  · exact hiLeader j hjilt (data.sameCluster_equivalence.symm hsame)

/-- The indexed clusters cover every original representative label. -/
theorem exists_mem_orderedCluster
    (data : RepresentativeClusterSubsequence time) (x : Fin m) :
    ∃ c : Fin data.orderedClusterCount, x ∈ data.orderedCluster c := by
  let p : Fin m := data.order.symm x
  let l : Fin m := data.firstSameClusterPosition p
  have hl : l ∈ data.clusterLeaderPositions := by
    exact data.firstSameClusterPosition_mem_leaders p
  obtain ⟨c, hc⟩ := data.exists_orderedClusterLeaderPosition_eq hl
  refine ⟨c, ?_⟩
  rw [mem_orderedCluster_iff, hc]
  have hpl : data.SameCluster (data.order p) (data.order l) := by
    change data.SameCluster (data.order p)
      (data.order (data.firstSameClusterPosition p))
    rw [← mem_sameClusterPositions_iff]
    exact data.firstSameClusterPosition_mem p
  simpa only [p, data.order.apply_symm_apply] using
    data.sameCluster_equivalence.symm hpl

theorem orderedCluster_cover
    (data : RepresentativeClusterSubsequence time) :
    Finset.univ.biUnion data.orderedCluster =
      (Finset.univ : Finset (Fin m)) := by
  classical
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact data.exists_mem_orderedCluster x

/-- The increasing leader enumeration respects the cluster index order. -/
theorem strictMono_orderedClusterLeaderPosition
    (data : RepresentativeClusterSubsequence time) :
    StrictMono data.orderedClusterLeaderPosition := by
  intro c d hcd
  change
    ((data.clusterLeaderPositions.orderIsoOfFin rfl c :
        data.clusterLeaderPositions) : Fin m) <
      ((data.clusterLeaderPositions.orderIsoOfFin rfl d :
        data.clusterLeaderPositions) : Fin m)
  exact (data.clusterLeaderPositions.orderIsoOfFin rfl).strictMono hcd

/-- Different cluster indices have different leader positions. -/
theorem orderedClusterLeaderPosition_ne
    (data : RepresentativeClusterSubsequence time)
    {c d : Fin data.orderedClusterCount} (hcd : c ≠ d) :
    data.orderedClusterLeaderPosition c ≠
      data.orderedClusterLeaderPosition d := by
  intro h
  apply hcd
  apply (data.clusterLeaderPositions.orderIsoOfFin rfl).injective
  exact Subtype.ext h

/-- Different indexed clusters are disjoint. -/
theorem orderedCluster_disjoint
    (data : RepresentativeClusterSubsequence time)
    {c d : Fin data.orderedClusterCount} (hcd : c ≠ d) :
    Disjoint (data.orderedCluster c) (data.orderedCluster d) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxc hxd
  have hcx : data.SameCluster
      (data.order (data.orderedClusterLeaderPosition c)) x :=
    (data.mem_orderedCluster_iff c x).mp hxc
  have hdx : data.SameCluster
      (data.order (data.orderedClusterLeaderPosition d)) x :=
    (data.mem_orderedCluster_iff d x).mp hxd
  have hleaders : data.SameCluster
      (data.order (data.orderedClusterLeaderPosition c))
      (data.order (data.orderedClusterLeaderPosition d)) :=
    data.sameCluster_equivalence.trans hcx
      (data.sameCluster_equivalence.symm hdx)
  exact data.not_sameCluster_order_of_distinct_leaders
    (data.orderedClusterLeaderPosition_mem c)
    (data.orderedClusterLeaderPosition_mem d)
    (data.orderedClusterLeaderPosition_ne hcd) hleaders

/-- Pairwise-disjoint formulation for the whole indexed family. -/
theorem pairwise_disjoint_orderedCluster
    (data : RepresentativeClusterSubsequence time) :
    Pairwise (Disjoint on data.orderedCluster) := by
  intro c d hcd
  exact data.orderedCluster_disjoint hcd

theorem orderedCluster_mem_clusterFinpartition
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.orderedCluster c ∈ data.clusterFinpartition.parts := by
  rw [orderedCluster]
  exact (data.clusterFinpartition.part_mem).mpr (Finset.mem_univ _)

/-- The indexed family is exactly the setoid partition's collection of
equivalence classes, with no omitted or repeated class. -/
theorem image_orderedCluster_eq_clusterFinpartition_parts
    (data : RepresentativeClusterSubsequence time) :
    Finset.univ.image data.orderedCluster = data.clusterFinpartition.parts := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hs
    exact data.orderedCluster_mem_clusterFinpartition c
  · intro hs
    obtain ⟨x, hx⟩ := data.clusterFinpartition.nonempty_of_mem_parts hs
    obtain ⟨c, hxc⟩ := data.exists_mem_orderedCluster x
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_univ _, ?_⟩
    exact data.clusterFinpartition.eq_of_mem_parts
      (data.orderedCluster_mem_clusterFinpartition c) hs hxc hx

/-- Members of one indexed part are related by bounded Abel-time gap. -/
theorem sameCluster_of_mem_orderedCluster
    (data : RepresentativeClusterSubsequence time)
    {c : Fin data.orderedClusterCount} {i j : Fin m}
    (hi : i ∈ data.orderedCluster c) (hj : j ∈ data.orderedCluster c) :
    data.SameCluster i j := by
  have hci := (data.mem_orderedCluster_iff c i).mp hi
  have hcj := (data.mem_orderedCluster_iff c j).mp hj
  exact data.sameCluster_equivalence.trans
    (data.sameCluster_equivalence.symm hci) hcj

/-- Bounded-gap classes are convex in the fixed pointwise sorted order. -/
theorem sameCluster_order_left_of_between
    (data : RepresentativeClusterSubsequence time)
    {i j k : Fin m} (hij : i ≤ j) (hjk : j ≤ k)
    (hik : data.SameCluster (data.order i) (data.order k)) :
    data.SameCluster (data.order i) (data.order j) := by
  rcases hik with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hijTime := data.ordered n hij
  have hjkTime := data.ordered n hjk
  have hikBound := hC ⟨n, rfl⟩
  change
    |time (data.subsequence n) (data.order i) -
      time (data.subsequence n) (data.order j)| ≤ C
  change
    |time (data.subsequence n) (data.order i) -
      time (data.subsequence n) (data.order k)| ≤ C at hikBound
  rw [abs_of_nonpos (sub_nonpos.mpr hijTime)]
  rw [abs_of_nonpos (sub_nonpos.mpr (hijTime.trans hjkTime))] at hikBound
  linarith

/-- The class leader precedes every member of its class in the fixed order. -/
theorem orderedClusterLeaderPosition_le_symm
    (data : RepresentativeClusterSubsequence time)
    {c : Fin data.orderedClusterCount} {x : Fin m}
    (hx : x ∈ data.orderedCluster c) :
    data.orderedClusterLeaderPosition c ≤ data.order.symm x := by
  by_contra hnot
  have hlt : data.order.symm x < data.orderedClusterLeaderPosition c :=
    lt_of_not_ge hnot
  have hleader := data.orderedClusterLeaderPosition_isLeader c
  apply hleader (data.order.symm x) hlt
  have hcx := (data.mem_orderedCluster_iff c x).mp hx
  simpa only [data.order.apply_symm_apply] using
    data.sameCluster_equivalence.symm hcx

/-- Every representative of an earlier cluster occurs before every
representative of a later cluster in the fixed sorted order. -/
theorem orderedCluster_positions_lt
    (data : RepresentativeClusterSubsequence time)
    {c d : Fin data.orderedClusterCount} (hcd : c < d)
    {x y : Fin m} (hx : x ∈ data.orderedCluster c)
    (hy : y ∈ data.orderedCluster d) :
    data.order.symm x < data.order.symm y := by
  have hlcd : data.orderedClusterLeaderPosition c <
      data.orderedClusterLeaderPosition d :=
    data.strictMono_orderedClusterLeaderPosition hcd
  have hlcx : data.orderedClusterLeaderPosition c ≤ data.order.symm x :=
    data.orderedClusterLeaderPosition_le_symm hx
  have hldy : data.orderedClusterLeaderPosition d ≤ data.order.symm y :=
    data.orderedClusterLeaderPosition_le_symm hy
  have hxld : data.order.symm x < data.orderedClusterLeaderPosition d := by
    by_contra hnot
    have hldx : data.orderedClusterLeaderPosition d ≤ data.order.symm x :=
      le_of_not_gt hnot
    have hcx : data.SameCluster
        (data.order (data.orderedClusterLeaderPosition c))
        (data.order (data.order.symm x)) := by
      simpa only [data.order.apply_symm_apply] using
        (data.mem_orderedCluster_iff c x).mp hx
    have hcld := data.sameCluster_order_left_of_between
      hlcd.le hldx hcx
    exact data.not_sameCluster_order_of_distinct_leaders
      (data.orderedClusterLeaderPosition_mem c)
      (data.orderedClusterLeaderPosition_mem d)
      (ne_of_lt hlcd) hcld
  exact hxld.trans_le hldy

/-- The signed time gap from any member of an earlier cluster to any member
of a later cluster tends to positive infinity. -/
theorem tendsto_orderedCluster_gap_atTop
    (data : RepresentativeClusterSubsequence time)
    {c d : Fin data.orderedClusterCount} (hcd : c < d)
    {x y : Fin m} (hx : x ∈ data.orderedCluster c)
    (hy : y ∈ data.orderedCluster d) :
    Tendsto (fun n =>
      time (data.subsequence n) y - time (data.subsequence n) x)
      atTop atTop := by
  have hpos : data.order.symm x < data.order.symm y :=
    data.orderedCluster_positions_lt hcd hx hy
  have hnot : ¬ data.SameCluster x y := by
    intro hxy
    have hcx := (data.mem_orderedCluster_iff c x).mp hx
    have hyc : y ∈ data.orderedCluster c := by
      rw [mem_orderedCluster_iff]
      exact data.sameCluster_equivalence.trans hcx hxy
    exact Finset.disjoint_left.mp (data.orderedCluster_disjoint hcd.ne) hyc hy
  have hnot' : ¬ data.SameCluster
      (data.order (data.order.symm x))
      (data.order (data.order.symm y)) := by
    simpa only [data.order.apply_symm_apply] using hnot
  simpa only [data.order.apply_symm_apply] using
    data.tendsto_ordered_gap_atTop hpos hnot'

/-! ## Canonical endpoint representatives -/

/-- Sorted positions belonging to indexed cluster `c`. -/
def orderedClusterPositions
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : Finset (Fin m) :=
  data.sameClusterPositions (data.orderedClusterLeaderPosition c)

@[simp]
theorem mem_orderedClusterPositions_iff
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (i : Fin m) :
    i ∈ data.orderedClusterPositions c ↔
      data.order i ∈ data.orderedCluster c := by
  rw [orderedClusterPositions, mem_sameClusterPositions_iff,
    mem_orderedCluster_iff]

theorem orderedClusterPositions_nonempty
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    (data.orderedClusterPositions c).Nonempty := by
  refine ⟨data.orderedClusterLeaderPosition c, ?_⟩
  rw [mem_orderedClusterPositions_iff, mem_orderedCluster_iff]
  exact data.sameCluster_equivalence.refl _

/-- The final sorted position occupied by cluster `c`. -/
def orderedClusterLastPosition
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : Fin m :=
  (data.orderedClusterPositions c).max'
    (data.orderedClusterPositions_nonempty c)

theorem orderedClusterLastPosition_mem_positions
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.orderedClusterLastPosition c ∈ data.orderedClusterPositions c :=
  Finset.max'_mem _ _

/-- The first representative label of indexed cluster `c`. -/
def orderedClusterFirst
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : Fin m :=
  data.order (data.orderedClusterLeaderPosition c)

/-- The last representative label of indexed cluster `c`. -/
def orderedClusterLast
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : Fin m :=
  data.order (data.orderedClusterLastPosition c)

theorem orderedClusterFirst_mem
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.orderedClusterFirst c ∈ data.orderedCluster c := by
  rw [orderedClusterFirst, mem_orderedCluster_iff]
  exact data.sameCluster_equivalence.refl _

theorem orderedClusterLast_mem
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.orderedClusterLast c ∈ data.orderedCluster c := by
  rw [orderedClusterLast, ← mem_orderedClusterPositions_iff]
  exact data.orderedClusterLastPosition_mem_positions c

/-- Every member position is at most its cluster's final position. -/
theorem order_symm_le_orderedClusterLastPosition
    (data : RepresentativeClusterSubsequence time)
    {c : Fin data.orderedClusterCount} {x : Fin m}
    (hx : x ∈ data.orderedCluster c) :
    data.order.symm x ≤ data.orderedClusterLastPosition c := by
  apply Finset.le_max'
  rw [mem_orderedClusterPositions_iff]
  simpa only [data.order.apply_symm_apply] using hx

/-- The actual Abel-time value of the first member of a cluster. -/
def orderedClusterMinTime
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (n : ℕ) : ℝ :=
  time (data.subsequence n) (data.orderedClusterFirst c)

/-- The actual Abel-time value of the last member of a cluster. -/
def orderedClusterMaxTime
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (n : ℕ) : ℝ :=
  time (data.subsequence n) (data.orderedClusterLast c)

/-- The chosen endpoints are pointwise extrema: every cluster member lies
between their time values. -/
theorem orderedCluster_time_mem_interval
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (n : ℕ) {x : Fin m}
    (hx : x ∈ data.orderedCluster c) :
    data.orderedClusterMinTime c n ≤ time (data.subsequence n) x ∧
      time (data.subsequence n) x ≤ data.orderedClusterMaxTime c n := by
  have hfirst : data.orderedClusterLeaderPosition c ≤ data.order.symm x :=
    data.orderedClusterLeaderPosition_le_symm hx
  have hlast : data.order.symm x ≤ data.orderedClusterLastPosition c :=
    data.order_symm_le_orderedClusterLastPosition hx
  constructor
  · simpa only [orderedClusterMinTime, orderedClusterFirst,
      data.order.apply_symm_apply] using data.ordered n hfirst
  · simpa only [orderedClusterMaxTime, orderedClusterLast,
      data.order.apply_symm_apply] using data.ordered n hlast

/-- One real constant bounds the width of every indexed cluster at every
term of the selected sequence. -/
theorem exists_uniform_orderedCluster_width
    (data : RepresentativeClusterSubsequence time) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c n,
      data.orderedClusterMaxTime c n - data.orderedClusterMinTime c n ≤ C := by
  obtain ⟨C, hC0, hC⟩ := data.exists_uniform_sameCluster_bound
  refine ⟨C, hC0, ?_⟩
  intro c n
  have hsame : data.SameCluster
      (data.orderedClusterFirst c) (data.orderedClusterLast c) :=
    data.sameCluster_of_mem_orderedCluster
      (data.orderedClusterFirst_mem c) (data.orderedClusterLast_mem c)
  have hbound := hC _ _ hsame n
  have horder : data.orderedClusterMinTime c n ≤
      data.orderedClusterMaxTime c n :=
    (data.orderedCluster_time_mem_interval c n
      (data.orderedClusterLast_mem c)).1
  change
    |data.orderedClusterMinTime c n - data.orderedClusterMaxTime c n| ≤ C
    at hbound
  rw [abs_of_nonpos (sub_nonpos.mpr horder)] at hbound
  linarith

/-- A natural common width gives the exact interval form consumed by the
near-integer pair-selection theorem. -/
theorem exists_nat_orderedCluster_interval
    (data : RepresentativeClusterSubsequence time) :
    ∃ D : ℕ, ∀ c n x, x ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤ time (data.subsequence n) x ∧
        time (data.subsequence n) x ≤
          data.orderedClusterMinTime c n + (D : ℝ) := by
  obtain ⟨C, hC0, hwidth⟩ := data.exists_uniform_orderedCluster_width
  refine ⟨Nat.ceil C, ?_⟩
  intro c n x hx
  have hinter := data.orderedCluster_time_mem_interval c n hx
  have hCceil : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
  exact ⟨hinter.1, by
    have := hwidth c n
    linarith⟩

/-- If every original time coordinate diverges, so does every chosen
cluster minimum along the selected subsequence. -/
theorem orderedClusterMinTime_tendsto_atTop
    (data : RepresentativeClusterSubsequence time)
    (htime : ∀ i, Tendsto (fun n => time n i) atTop atTop)
    (c : Fin data.orderedClusterCount) :
    Tendsto (data.orderedClusterMinTime c) atTop atTop := by
  change Tendsto
    ((fun n => time n (data.orderedClusterFirst c)) ∘ data.subsequence)
    atTop atTop
  exact (htime (data.orderedClusterFirst c)).comp
    data.strictMono_subsequence.tendsto_atTop

/-- Endpoint form of cross-cluster separation: the next cluster's minimum
minus the previous cluster's maximum tends to positive infinity. -/
theorem tendsto_orderedCluster_endpoint_gap_atTop
    (data : RepresentativeClusterSubsequence time)
    {c d : Fin data.orderedClusterCount} (hcd : c < d) :
    Tendsto (fun n =>
      data.orderedClusterMinTime d n - data.orderedClusterMaxTime c n)
      atTop atTop := by
  simpa only [orderedClusterMinTime, orderedClusterMaxTime] using
    data.tendsto_orderedCluster_gap_atTop hcd
      (data.orderedClusterLast_mem c) (data.orderedClusterFirst_mem d)

/-- One theorem collecting the finite ordered-partition interface needed by
the separated-cluster and near-integer branches. -/
theorem exists_orderedCluster_partition_width
    (data : RepresentativeClusterSubsequence time) :
    ∃ D : ℕ,
      (∀ c, (data.orderedCluster c).Nonempty) ∧
      Pairwise (Disjoint on data.orderedCluster) ∧
      Finset.univ.biUnion data.orderedCluster =
        (Finset.univ : Finset (Fin m)) ∧
      (∀ c n x, x ∈ data.orderedCluster c →
        data.orderedClusterMinTime c n ≤ time (data.subsequence n) x ∧
          time (data.subsequence n) x ≤
            data.orderedClusterMinTime c n + (D : ℝ)) ∧
      ∀ c d, c < d →
        Tendsto (fun n =>
          data.orderedClusterMinTime d n -
            data.orderedClusterMaxTime c n) atTop atTop := by
  obtain ⟨D, hinterval⟩ := data.exists_nat_orderedCluster_interval
  exact ⟨D, data.orderedCluster_nonempty,
    data.pairwise_disjoint_orderedCluster, data.orderedCluster_cover,
    hinterval, fun _ _ hcd => data.tendsto_orderedCluster_endpoint_gap_atTop hcd⟩

/-- In the all-unbounded case, the packaged cluster minima also diverge to
positive infinity, exactly as required by pair selection. -/
theorem exists_orderedCluster_partition_width_of_tendsto
    (data : RepresentativeClusterSubsequence time)
    (htime : ∀ i, Tendsto (fun n => time n i) atTop atTop) :
    ∃ D : ℕ,
      (∀ c, (data.orderedCluster c).Nonempty) ∧
      Pairwise (Disjoint on data.orderedCluster) ∧
      Finset.univ.biUnion data.orderedCluster =
        (Finset.univ : Finset (Fin m)) ∧
      (∀ c, Tendsto (data.orderedClusterMinTime c) atTop atTop) ∧
      (∀ c n x, x ∈ data.orderedCluster c →
        data.orderedClusterMinTime c n ≤ time (data.subsequence n) x ∧
          time (data.subsequence n) x ≤
            data.orderedClusterMinTime c n + (D : ℝ)) ∧
      ∀ c d, c < d →
        Tendsto (fun n =>
          data.orderedClusterMinTime d n -
            data.orderedClusterMaxTime c n) atTop atTop := by
  obtain ⟨D, hnonempty, hdisjoint, hcover, hinterval, hgap⟩ :=
    data.exists_orderedCluster_partition_width
  exact ⟨D, hnonempty, hdisjoint, hcover,
    fun c => data.orderedClusterMinTime_tendsto_atTop htime c,
    hinterval, hgap⟩




end RepresentativeClusterSubsequence
end AbelFormalization
