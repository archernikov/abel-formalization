import AbelFormalization.DiagonalSeparatedSubsequence
import AbelFormalization.RepresentativeClusterSubsequenceRestriction

/-!
# Restrict the all-unbounded setup to its diagonal separated subsequence

The diagonal selection is initially expressed as a subsequence of the
indices stored in `RepresentativeClusterSubsequence`.  This file makes that
selected sequence ambient, transports the unchanged ordered clusters, and
identifies its separation sets with the corresponding preimages.  Thus the
diagonal sequence satisfies every fixed separation rank eventually.  A
rank-dependent finite tail satisfies that rank at every natural index.
-/

noncomputable section
set_option autoImplicit false

open Filter Function Set
open scoped Topology

namespace AbelFormalization

/-- Restricting both the ambient sequence and its cluster data pulls the
literal separation set back along the same index map. -/
theorem restrictedAllUnboundedSeparationSet_restrictToFurtherSubsequence
    {A : ℝ → ℝ} {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (N : ℕ) :
    restrictedAllUnboundedSeparationSet
        (fun n ↦ x (data.subsequence (phi n)))
        (data.restrictToFurtherSubsequence phi hphi) N =
      phi ⁻¹' restrictedAllUnboundedSeparationSet x data N := by
  classical
  let e := data.restrictToFurtherSubsequenceClusterEquiv phi hphi
  ext n
  constructor
  · intro hn c i hi j hj hij
    let c' := e.symm c
    have hc' :
        data.restrictToFurtherSubsequenceClusterEquiv phi hphi c' = c := by
      change e (e.symm c) = c
      exact e.apply_symm_apply c
    have hi' : i ∈
        (data.restrictToFurtherSubsequence phi hphi).orderedCluster
          c' := by
      rw [
        RepresentativeClusterSubsequence.restrictToFurtherSubsequence_orderedCluster,
        hc']
      exact hi
    have hj' : j ∈
        (data.restrictToFurtherSubsequence phi hphi).orderedCluster
          c' := by
      rw [
        RepresentativeClusterSubsequence.restrictToFurtherSubsequence_orderedCluster,
        hc']
      exact hj
    have hsep := hn c' i hi' j hj' hij
    simpa only [
      RepresentativeClusterSubsequence.restrictToFurtherSubsequence_subsequence,
      RepresentativeClusterSubsequence.restrictToFurtherSubsequence_orderedClusterMinTime,
      hc', id_eq] using hsep
  · intro hn c i hi j hj hij
    have hi' : i ∈ data.orderedCluster (e c) := by
      simpa only [
        RepresentativeClusterSubsequence.restrictToFurtherSubsequence_orderedCluster]
        using hi
    have hj' : j ∈ data.orderedCluster (e c) := by
      simpa only [
        RepresentativeClusterSubsequence.restrictToFurtherSubsequence_orderedCluster]
        using hj
    have hsep := hn (e c) i hi' j hj' hij
    simpa only [
      RepresentativeClusterSubsequence.restrictToFurtherSubsequence_subsequence,
      RepresentativeClusterSubsequence.restrictToFurtherSubsequence_orderedClusterMinTime,
      id_eq] using hsep

theorem mem_restrictedAllUnboundedSeparationSet_restrictToFurtherSubsequence_iff
    {A : ℝ → ℝ} {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (N n : ℕ) :
    n ∈ restrictedAllUnboundedSeparationSet
        (fun k ↦ x (data.subsequence (phi k)))
        (data.restrictToFurtherSubsequence phi hphi) N ↔
      phi n ∈ restrictedAllUnboundedSeparationSet x data N := by
  rw [restrictedAllUnboundedSeparationSet_restrictToFurtherSubsequence]
  rfl

namespace RepresentativeClusterSubsequence

/-- Divergence of cluster minima is preserved by a further restriction. -/
theorem restrictToFurtherSubsequence_orderedClusterMinTime_tendsto_atTop
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hmin : ∀ c, Tendsto (data.orderedClusterMinTime c) atTop atTop)
    (c : Fin (data.restrictToFurtherSubsequence phi hphi).orderedClusterCount) :
    Tendsto
      ((data.restrictToFurtherSubsequence phi hphi).orderedClusterMinTime c)
      atTop atTop := by
  change Tendsto (fun n ↦
    (data.restrictToFurtherSubsequence phi hphi).orderedClusterMinTime c n)
    atTop atTop
  have h :=
    (hmin (data.restrictToFurtherSubsequenceClusterEquiv phi hphi c)).comp
      hphi.tendsto_atTop
  change Tendsto (fun n ↦ data.orderedClusterMinTime
    (data.restrictToFurtherSubsequenceClusterEquiv phi hphi c) (phi n))
    atTop atTop at h
  simpa only [restrictToFurtherSubsequence_orderedClusterMinTime] using h

/-- Divergence of gaps between ordered-cluster endpoints is preserved by a
further restriction. -/
theorem restrictToFurtherSubsequence_orderedClusterEndpointGap_tendsto_atTop
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hgap : ∀ c d, c < d → Tendsto (fun n ↦
      data.orderedClusterMinTime d n - data.orderedClusterMaxTime c n)
        atTop atTop)
    {c d : Fin (data.restrictToFurtherSubsequence phi hphi).orderedClusterCount}
    (hcd : c < d) :
    Tendsto (fun n ↦
      (data.restrictToFurtherSubsequence phi hphi).orderedClusterMinTime d n -
      (data.restrictToFurtherSubsequence phi hphi).orderedClusterMaxTime c n)
      atTop atTop := by
  have hcd' :
      data.restrictToFurtherSubsequenceClusterEquiv phi hphi c <
        data.restrictToFurtherSubsequenceClusterEquiv phi hphi d :=
    (data.restrictToFurtherSubsequenceClusterEquiv phi hphi).lt_iff_lt.mpr hcd
  have h :=
    (hgap
      (data.restrictToFurtherSubsequenceClusterEquiv phi hphi c)
      (data.restrictToFurtherSubsequenceClusterEquiv phi hphi d) hcd').comp
      hphi.tendsto_atTop
  change Tendsto (fun n ↦
    data.orderedClusterMinTime
        (data.restrictToFurtherSubsequenceClusterEquiv phi hphi d) (phi n) -
      data.orderedClusterMaxTime
        (data.restrictToFurtherSubsequenceClusterEquiv phi hphi c) (phi n))
    atTop atTop at h
  simpa only [
    restrictToFurtherSubsequence_orderedClusterMinTime,
    restrictToFurtherSubsequence_orderedClusterMaxTime] using h

/-- A uniform cluster interval estimate is preserved pointwise by a further
restriction. -/
theorem restrictToFurtherSubsequence_orderedCluster_interval
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (width : ℕ)
    (hinterval : ∀ c n i, i ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤ time (data.subsequence n) i ∧
        time (data.subsequence n) i ≤
          data.orderedClusterMinTime c n + (width : ℝ))
    (c : Fin (data.restrictToFurtherSubsequence phi hphi).orderedClusterCount)
    (n : ℕ) (i : Fin m)
    (hi : i ∈ (data.restrictToFurtherSubsequence phi hphi).orderedCluster c) :
    (data.restrictToFurtherSubsequence phi hphi).orderedClusterMinTime c n ≤
        time (data.subsequence (phi n)) i ∧
      time (data.subsequence (phi n)) i ≤
        (data.restrictToFurtherSubsequence phi hphi).orderedClusterMinTime c n +
          (width : ℝ) := by
  have hi' : i ∈ data.orderedCluster
      (data.restrictToFurtherSubsequenceClusterEquiv phi hphi c) := by
    simpa only [restrictToFurtherSubsequence_orderedCluster] using hi
  simpa only [restrictToFurtherSubsequence_orderedClusterMinTime] using
    hinterval
      (data.restrictToFurtherSubsequenceClusterEquiv phi hphi c) (phi n) i hi'

end RepresentativeClusterSubsequence

/-- The canonical diagonal subsequence, with the previously stored cluster
subsequence absorbed into the ambient sequence. -/
def IsAbel.diagonalSeparatedAmbientSequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) :
    ℕ → RestrictedSource m p a :=
  fun n ↦ x (data.subsequence
    (hA.diagonalSeparatedSubsequence x data hinfinite n))

@[simp]
theorem IsAbel.diagonalSeparatedAmbientSequence_apply
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) (n : ℕ) :
    hA.diagonalSeparatedAmbientSequence x data hinfinite n =
      x (data.subsequence
        (hA.diagonalSeparatedSubsequence x data hinfinite n)) :=
  rfl

/-- The unchanged ordered-cluster data on the diagonal ambient sequence. -/
def IsAbel.diagonalSeparatedClusterData
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) :
    RepresentativeClusterSubsequence
      (fun n i ↦ A
        (((hA.diagonalSeparatedAmbientSequence x data hinfinite n).1.1 i))) :=
  data.restrictToFurtherSubsequence
    (hA.diagonalSeparatedSubsequence x data hinfinite)
    (hA.diagonalSeparatedSubsequence_strictMono x data hinfinite)

@[simp]
theorem IsAbel.diagonalSeparatedClusterData_subsequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) :
    (hA.diagonalSeparatedClusterData x data hinfinite).subsequence = id := by
  simp only [IsAbel.diagonalSeparatedClusterData,
    RepresentativeClusterSubsequence.restrictToFurtherSubsequence_subsequence]

/-- Injectivity on the originally selected cluster subsequence survives the
diagonal reindexing. -/
theorem IsAbel.diagonalSeparatedAmbientSequence_injective
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    (hxinj : Injective (fun n ↦ x (data.subsequence n))) :
    Injective (hA.diagonalSeparatedAmbientSequence x data hinfinite) := by
  exact hxinj.comp
    (hA.diagonalSeparatedSubsequence_strictMono x data hinfinite).injective

/-- Any pointwise property of the originally selected sequence survives the
diagonal reindexing.  In particular this transports regular-zero membership. -/
theorem IsAbel.diagonalSeparatedAmbientSequence_mem
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    {Z : Set (RestrictedSource m p a)}
    (hxmem : ∀ n, x (data.subsequence n) ∈ Z) (n : ℕ) :
    hA.diagonalSeparatedAmbientSequence x data hinfinite n ∈ Z :=
  hxmem _

/-- Any limit along the originally selected sequence survives the diagonal
reindexing. -/
theorem IsAbel.tendsto_diagonalSeparatedAmbientSequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    {beta : Type*} {l : Filter beta}
    (f : RestrictedSource m p a → beta)
    (hf : Tendsto (fun n ↦ f (x (data.subsequence n))) atTop l) :
    Tendsto
      (fun n ↦ f (hA.diagonalSeparatedAmbientSequence x data hinfinite n))
      atTop l := by
  change Tendsto
    ((fun n ↦ f (x (data.subsequence n))) ∘
      hA.diagonalSeparatedSubsequence x data hinfinite) atTop l
  exact hf.comp
    (hA.diagonalSeparatedSubsequence_strictMono x data hinfinite).tendsto_atTop

/-- Separation-set membership on the diagonal ambient sequence is exactly
membership of the selected old index. -/
theorem IsAbel.mem_diagonalSeparatedAmbientSeparationSet_iff
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    (N n : ℕ) :
    n ∈ restrictedAllUnboundedSeparationSet
        (hA.diagonalSeparatedAmbientSequence x data hinfinite)
        (hA.diagonalSeparatedClusterData x data hinfinite) N ↔
      hA.diagonalSeparatedSubsequence x data hinfinite n ∈
        restrictedAllUnboundedSeparationSet x data N := by
  change n ∈ restrictedAllUnboundedSeparationSet
      (fun k ↦ x (data.subsequence
        (hA.diagonalSeparatedSubsequence x data hinfinite k)))
      (data.restrictToFurtherSubsequence
        (hA.diagonalSeparatedSubsequence x data hinfinite)
        (hA.diagonalSeparatedSubsequence_strictMono x data hinfinite)) N ↔ _
  exact
    mem_restrictedAllUnboundedSeparationSet_restrictToFurtherSubsequence_iff
      x data (hA.diagonalSeparatedSubsequence x data hinfinite)
        (hA.diagonalSeparatedSubsequence_strictMono x data hinfinite) N n

/-- The `n`th term of the diagonal ambient sequence satisfies separation
rank `n`. -/
theorem IsAbel.diagonalSeparatedAmbientSequence_mem_own_rank
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) (n : ℕ) :
    n ∈ restrictedAllUnboundedSeparationSet
      (hA.diagonalSeparatedAmbientSequence x data hinfinite)
      (hA.diagonalSeparatedClusterData x data hinfinite) n := by
  rw [hA.mem_diagonalSeparatedAmbientSeparationSet_iff]
  exact diagonalSubsequenceOfInfiniteSets_mem
    (restrictedAllUnboundedSeparationSet x data) hinfinite n

/-- A term satisfies every separation rank no larger than its diagonal
index. -/
theorem IsAbel.diagonalSeparatedAmbientSequence_mem_of_rank_le
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    {N n : ℕ} (hNn : N ≤ n) :
    n ∈ restrictedAllUnboundedSeparationSet
      (hA.diagonalSeparatedAmbientSequence x data hinfinite)
      (hA.diagonalSeparatedClusterData x data hinfinite) N := by
  exact (hA.restrictedAllUnboundedSeparationSet_antitone
      (hA.diagonalSeparatedAmbientSequence x data hinfinite)
      (hA.diagonalSeparatedClusterData x data hinfinite)) hNn
    (hA.diagonalSeparatedAmbientSequence_mem_own_rank x data hinfinite n)

/-- Every fixed separation rank holds eventually on the single diagonal
ambient sequence. -/
theorem IsAbel.diagonalSeparatedAmbientSequence_eventually_mem
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) (N : ℕ) :
    ∀ᶠ n in atTop, n ∈ restrictedAllUnboundedSeparationSet
      (hA.diagonalSeparatedAmbientSequence x data hinfinite)
      (hA.diagonalSeparatedClusterData x data hinfinite) N := by
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hA.diagonalSeparatedAmbientSequence_mem_of_rank_le
    x data hinfinite hn

/-- Dropping the first `N` diagonal terms turns rank-`N` membership into a
pointwise statement. -/
theorem IsAbel.diagonalSeparatedAmbientSequence_tail_mem
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    (N n : ℕ) :
    N + n ∈ restrictedAllUnboundedSeparationSet
      (hA.diagonalSeparatedAmbientSequence x data hinfinite)
      (hA.diagonalSeparatedClusterData x data hinfinite) N :=
  hA.diagonalSeparatedAmbientSequence_mem_of_rank_le x data hinfinite
    (Nat.le_add_right N n)

/-- The original diagonal map with its first `N` values discarded. -/
def IsAbel.diagonalSeparatedRankTailSubsequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite)
    (N n : ℕ) : ℕ :=
  hA.diagonalSeparatedSubsequence x data hinfinite (N + n)

theorem IsAbel.diagonalSeparatedRankTailSubsequence_strictMono
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite) (N : ℕ) :
    StrictMono (hA.diagonalSeparatedRankTailSubsequence x data hinfinite N) := by
  intro n k hnk
  exact hA.diagonalSeparatedSubsequence_strictMono x data hinfinite
    (Nat.add_lt_add_left hnk N)

/-- The diagonal ambient sequence after dropping the first `N` terms. -/
def IsAbel.diagonalSeparatedRankTailSequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite)
    (N : ℕ) : ℕ → RestrictedSource m p a :=
  fun n ↦ x (data.subsequence
    (hA.diagonalSeparatedRankTailSubsequence x data hinfinite N n))

/-- The unchanged ordered clusters on the rank-`N` diagonal tail. -/
def IsAbel.diagonalSeparatedRankTailData
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite)
    (N : ℕ) :
    RepresentativeClusterSubsequence
      (fun n i ↦ A
        (((hA.diagonalSeparatedRankTailSequence x data hinfinite N n).1.1 i))) :=
  data.restrictToFurtherSubsequence
    (hA.diagonalSeparatedRankTailSubsequence x data hinfinite N)
    (hA.diagonalSeparatedRankTailSubsequence_strictMono x data hinfinite N)

@[simp]
theorem IsAbel.diagonalSeparatedRankTailData_subsequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite) (N : ℕ) :
    (hA.diagonalSeparatedRankTailData x data hinfinite N).subsequence = id := by
  simp only [IsAbel.diagonalSeparatedRankTailData,
    RepresentativeClusterSubsequence.restrictToFurtherSubsequence_subsequence]

/-- The rank-dependent tail satisfies its chosen separation rank at every
natural index. -/
theorem IsAbel.diagonalSeparatedRankTailSequence_mem
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite)
    (N n : ℕ) :
    n ∈ restrictedAllUnboundedSeparationSet
      (hA.diagonalSeparatedRankTailSequence x data hinfinite N)
      (hA.diagonalSeparatedRankTailData x data hinfinite N) N := by
  rw [show n ∈ restrictedAllUnboundedSeparationSet
        (hA.diagonalSeparatedRankTailSequence x data hinfinite N)
        (hA.diagonalSeparatedRankTailData x data hinfinite N) N ↔
      hA.diagonalSeparatedRankTailSubsequence x data hinfinite N n ∈
        restrictedAllUnboundedSeparationSet x data N by
    change n ∈ restrictedAllUnboundedSeparationSet
        (fun k ↦ x (data.subsequence
          (hA.diagonalSeparatedRankTailSubsequence x data hinfinite N k)))
        (data.restrictToFurtherSubsequence
          (hA.diagonalSeparatedRankTailSubsequence x data hinfinite N)
          (hA.diagonalSeparatedRankTailSubsequence_strictMono
            x data hinfinite N)) N ↔ _
    exact
      mem_restrictedAllUnboundedSeparationSet_restrictToFurtherSubsequence_iff
        x data
        (hA.diagonalSeparatedRankTailSubsequence x data hinfinite N)
        (hA.diagonalSeparatedRankTailSubsequence_strictMono
          x data hinfinite N) N n]
  exact (hA.restrictedAllUnboundedSeparationSet_antitone x data)
    (Nat.le_add_right N n)
    (diagonalSubsequenceOfInfiniteSets_mem
      (restrictedAllUnboundedSeparationSet x data) hinfinite (N + n))

/-- Pointwise properties, including regular-zero membership, survive the
rank-tail reindexing. -/
theorem IsAbel.diagonalSeparatedRankTailSequence_mem_set
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite)
    {Z : Set (RestrictedSource m p a)}
    (hxmem : ∀ n, x (data.subsequence n) ∈ Z) (N n : ℕ) :
    hA.diagonalSeparatedRankTailSequence x data hinfinite N n ∈ Z :=
  hxmem _

/-- Limits along the originally selected sequence survive every rank-tail
reindexing. -/
theorem IsAbel.tendsto_diagonalSeparatedRankTailSequence
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ M,
      (restrictedAllUnboundedSeparationSet x data M).Infinite)
    {beta : Type*} {l : Filter beta}
    (f : RestrictedSource m p a → beta)
    (hf : Tendsto (fun n ↦ f (x (data.subsequence n))) atTop l)
    (N : ℕ) :
    Tendsto
      (fun n ↦ f (hA.diagonalSeparatedRankTailSequence
        x data hinfinite N n)) atTop l := by
  change Tendsto
    ((fun n ↦ f (x (data.subsequence n))) ∘
      hA.diagonalSeparatedRankTailSubsequence x data hinfinite N) atTop l
  exact hf.comp
    (hA.diagonalSeparatedRankTailSubsequence_strictMono
      x data hinfinite N).tendsto_atTop

end AbelFormalization
