import AbelFormalization.RestrictedBaseZeroCase
import AbelFormalization.RestrictedAllUnboundedSeparatedSetup

/-!
# Outer representative-count induction from the separated branch

The geometric and compactness modules reduce an infinite base regular-zero
set to an all-unbounded ordered-cluster sequence.  The existing dichotomy
then either supplies an infinite simultaneous-separation set or a pair-merge
subsequence, and the lower representative-count theorem already excludes the
second alternative.

This module leaves the quantitative argument as one proposition: every
separated ordered-cluster setup at a fixed rank is contradictory.  It proves
the full outer induction from that proposition, treating one representative
separately because the pair-merge theorem starts with two representatives.
-/

noncomputable section
set_option autoImplicit false

open Filter Function Set
open scoped Topology

namespace AbelFormalization

/-- The exact separated-branch callback at rank `N`.  Its arguments are only
the system data and the ordered-cluster facts returned by
`exists_restrictedAllUnboundedBranchSetupDichotomy`; the quantitative proof
is responsible for deriving `False` from the final infinitude hypothesis. -/
def RestrictedAllUnboundedSeparatedContradictionAtRank
    (A : ℝ → ℝ) (N : ℕ) : Prop :=
  ∀ {q : ℕ} {ι : Type} [Finite ι] {p a : ℕ}
    (box : RestrictedBox p)
    (representative : ι → Fin (q + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra box)
    (R : ℝ)
    (_hDomain :
      restrictedBaseClosedDomain (m := q + 1) (a := a) box R ⊆
        restrictedAbelJetDomain (a := a) box representative offset)
    (F : Fin (((q + 1) + p) + a) →
      RestrictedSource (q + 1) p a → ℝ)
    (_hF : ∀ r, F r ∈ restrictedExpressionBase box
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource (q + 1) p a)
    (w₀ : RestrictedBoxSpace p)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (width : ℕ)
    (_hsubsequence : StrictMono data.subsequence)
    (_hinjective : Function.Injective
      (fun n ↦ x (data.subsequence n)))
    (_hzero : ∀ n, x (data.subsequence n) ∈
      regularZeroSet (restrictedBaseOpenDomain box R) (constraintMap F))
    (_hbox : w₀ ∈ box.closedBox)
    (_hbox_tendsto : Tendsto
      (fun n ↦ (x (data.subsequence n)).1.2) atTop (nhds w₀))
    (_hrepresentative_tendsto : ∀ i, Tendsto
      (fun n ↦ (x (data.subsequence n)).1.1 i) atTop atTop)
    (_hcluster_nonempty : ∀ c, (data.orderedCluster c).Nonempty)
    (_hcluster_disjoint : Pairwise (Disjoint on data.orderedCluster))
    (_hcluster_cover : Finset.univ.biUnion data.orderedCluster =
      (Finset.univ : Finset (Fin (q + 1))))
    (_hminimum_tendsto : ∀ c,
      Tendsto (data.orderedClusterMinTime c) atTop atTop)
    (_hcluster_interval : ∀ c n i, i ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤
          A ((x (data.subsequence n)).1.1 i) ∧
        A ((x (data.subsequence n)).1.1 i) ≤
          data.orderedClusterMinTime c n + (width : ℝ))
    (_hcross_cluster : ∀ c d, c < d →
      ∀ i, i ∈ data.orderedCluster c →
      ∀ j, j ∈ data.orderedCluster d →
        Tendsto (fun n ↦
          A ((x (data.subsequence n)).1.1 j) -
            A ((x (data.subsequence n)).1.1 i)) atTop atTop)
    (_hcluster_gap : ∀ c d, c < d →
      Tendsto (fun n ↦ data.orderedClusterMinTime d n -
        data.orderedClusterMaxTime c n) atTop atTop)
    (_hseparated :
      (restrictedAllUnboundedSeparationSet x data N).Infinite),
    False

/-- Strong quantitative callback: the separated branch is contradictory at
every rank.  The outer induction below can in fact use any one fixed-rank
specialization. -/
def RestrictedAllUnboundedSeparatedContradiction
    (A : ℝ → ℝ) : Prop :=
  ∀ N, RestrictedAllUnboundedSeparatedContradictionAtRank A N

/-- The one-representative outer step.  The branch dichotomy's pair
alternative would contain two distinct elements of `Fin 1`, so only the
separated branch remains. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_one_of_separated
    {A : ℝ → ℝ} (hA : IsAbel A) (N : ℕ)
    (hseparated : RestrictedAllUnboundedSeparatedContradictionAtRank A N) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 1 := by
  intro ι _ p box representative offset a R hDomain F hF
  by_contra hfinite
  obtain ⟨x, w₀, data, width, hsubsequence, hinjective, hzero, hbox,
      hbox_tendsto, hrepresentative_tendsto, hcluster_nonempty,
      hcluster_disjoint, hcluster_cover, hminimum_tendsto,
      hcluster_interval, hcross_cluster, hcluster_gap, hdichotomy⟩ :=
    hA.exists_restrictedAllUnboundedBranchSetupDichotomy
      hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_zero
      box representative offset R hDomain F hF hfinite N
  have huniv : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  rcases hdichotomy Set.univ huniv with hinfinite | hpair
  · have hinfinite' :
        (restrictedAllUnboundedSeparationSet x data N).Infinite := by
      simpa only [Set.univ_inter] using hinfinite
    exact hseparated box representative offset R hDomain F hF x w₀ data
      width hsubsequence hinjective hzero hbox hbox_tendsto
      hrepresentative_tendsto hcluster_nonempty hcluster_disjoint
      hcluster_cover hminimum_tendsto hcluster_interval hcross_cluster
      hcluster_gap hinfinite'
  · obtain ⟨_c, i, j, _k, _K, _φ, _hi, _hj, hij, _hk, _hK,
        _hφ, _hφmem, _hsubφ, _hinjectiveφ, _hzeroφ, _hbox_tendstoφ,
        _hrepresentative_tendstoφ, _horient, _hdelta, _hlog⟩ := hpair
    exact hij (Fin.ext (by omega))

/-- The ordinary positive outer step.  The established separated-setup
theorem has already eliminated the pair branch with
`false_of_restrictedPairMergeBranch_q_add_two`, leaving exactly the callback
arguments above. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_q_add_two_of_separated
    {A : ℝ → ℝ} (hA : IsAbel A) {q : ℕ}
    (hlower : RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 1))
    (N : ℕ)
    (hseparated : RestrictedAllUnboundedSeparatedContradictionAtRank A N) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 2) := by
  intro ι _ p box representative offset a R hDomain F hF
  by_contra hfinite
  obtain ⟨x, w₀, data, width, hsubsequence, hinjective, hzero, hbox,
      hbox_tendsto, hrepresentative_tendsto, hcluster_nonempty,
      hcluster_disjoint, hcluster_cover, hminimum_tendsto,
      hcluster_interval, hcross_cluster, hcluster_gap, hinfinite⟩ :=
    hA.exists_restrictedAllUnboundedSeparatedSetup_q_add_two
      hlower box representative offset R hDomain F hF hfinite N
  exact hseparated box representative offset R hDomain F hF x w₀ data
    width hsubsequence hinjective hzero hbox hbox_tendsto
    hrepresentative_tendsto hcluster_nonempty hcluster_disjoint
    hcluster_cover hminimum_tendsto hcluster_interval hcross_cluster
    hcluster_gap hinfinite

/-- Any one fixed-rank separated contradiction closes the full outer
representative-count induction. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_separatedAtRank
    {A : ℝ → ℝ} (hA : IsAbel A) (N : ℕ)
    (hseparated : RestrictedAllUnboundedSeparatedContradictionAtRank A N) :
    ∀ m, RestrictedBaseRegularZeroFiniteForRepresentativeCount A m := by
  have hzero : RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 :=
    hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_zero
  have hone : RestrictedBaseRegularZeroFiniteForRepresentativeCount A 1 :=
    hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_one_of_separated
      N hseparated
  have hpositive : ∀ q,
      RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 1) := by
    intro q
    induction q with
    | zero => exact hone
    | succ q ih =>
        exact
          hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_q_add_two_of_separated
            ih N hseparated
  intro m
  cases m with
  | zero => exact hzero
  | succ q => exact hpositive q

/-- The strong all-ranks callback specializes at rank zero and therefore
closes the full base-level outer induction. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_separated
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hseparated : RestrictedAllUnboundedSeparatedContradiction A) :
    ∀ m, RestrictedBaseRegularZeroFiniteForRepresentativeCount A m :=
  hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_separatedAtRank
    0 (hseparated 0)

/-- Once the separated branch supplies every base representative count, the
existing inner induction propagates the conclusion through every finite
exponential-list level. -/
theorem IsAbel.restrictedRegularZeroFiniteForRepresentativeCount_all_levels_of_separated
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hseparated : RestrictedAllUnboundedSeparatedContradiction A) :
    ∀ m level, RestrictedRegularZeroFiniteForRepresentativeCount A m level := by
  intro m
  exact hA.restrictedRegularZeroFiniteForRepresentativeCount_all_of_base
    (hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_separated
      hseparated m)

/-! ## A fixed setup with separation available at every later rank -/

/-- The flexible separated-branch callback used by the quantitative trace.

Unlike `RestrictedAllUnboundedSeparatedContradictionAtRank`, this proposition
first fixes one normalized sequence and its ordered clusters.  Only then does
it assume that the same setup has an infinite separation set for every rank.
Consequently the quantitative proof may inspect the finite algebraic descent
and choose its required separation rank afterwards.

Every argument preceding `hseparated` is a component of
`exists_restrictedAllUnboundedNormalizedClusterSetup`; no extra geometric
input is bundled into this callback.
-/
def RestrictedAllUnboundedNormalizedSeparatedContradiction
    (A : ℝ → ℝ) : Prop :=
  ∀ {m : ℕ} {ι : Type} [Finite ι] {p a : ℕ}
    (box : RestrictedBox p)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra box)
    (R : ℝ)
    (_hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) box R ⊆
        restrictedAbelJetDomain (a := a) box representative offset)
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (_hF : ∀ r, F r ∈ restrictedExpressionBase box
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource (m + 1) p a)
    (w₀ : RestrictedBoxSpace p)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (width : ℕ)
    (_hsubsequence : data.subsequence = id)
    (_hinjective : Function.Injective x)
    (_hzero : ∀ n, x n ∈
      regularZeroSet (restrictedBaseOpenDomain box R) (constraintMap F))
    (_hbox : w₀ ∈ box.closedBox)
    (_hbox_tendsto : Tendsto
      (fun n ↦ (x n).1.2) atTop (nhds w₀))
    (_hrepresentative_tendsto : ∀ i, Tendsto
      (fun n ↦ (x n).1.1 i) atTop atTop)
    (_hcluster_nonempty : ∀ c, (data.orderedCluster c).Nonempty)
    (_hcluster_disjoint : Pairwise (Disjoint on data.orderedCluster))
    (_hcluster_cover : Finset.univ.biUnion data.orderedCluster =
      (Finset.univ : Finset (Fin (m + 1))))
    (_hminimum_tendsto : ∀ c,
      Tendsto (data.orderedClusterMinTime c) atTop atTop)
    (_hcluster_interval : ∀ c n i, i ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤ A ((x n).1.1 i) ∧
        A ((x n).1.1 i) ≤
          data.orderedClusterMinTime c n + (width : ℝ))
    (_hcross_cluster : ∀ c d, c < d →
      ∀ i, i ∈ data.orderedCluster c →
      ∀ j, j ∈ data.orderedCluster d →
        Tendsto (fun n ↦
          A ((x n).1.1 j) - A ((x n).1.1 i)) atTop atTop)
    (_hcluster_gap : ∀ c d, c < d →
      Tendsto (fun n ↦ data.orderedClusterMinTime d n -
        data.orderedClusterMaxTime c n) atTop atTop)
    (_hseparated : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite),
    False

/-- For a normalized one-representative setup every separation condition is
vacuous: two indices of `Fin 1` cannot be distinct. -/
theorem restrictedAllUnboundedSeparationSet_infinite_fin_one
    {A : ℝ → ℝ} {p a : ℕ}
    (x : ℕ → RestrictedSource 1 p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (N : ℕ) :
    (restrictedAllUnboundedSeparationSet x data N).Infinite := by
  have hset : restrictedAllUnboundedSeparationSet x data N = Set.univ := by
    ext n
    simp only [restrictedAllUnboundedSeparationSet, Set.mem_ofPred_eq,
      Set.mem_univ, iff_true]
    intro c i _hi j _hj hij
    exact (hij (Fin.ext (by omega))).elim
  rw [hset]
  exact Set.infinite_univ

/-- The flexible callback closes the one-representative outer step using one
normalized setup and vacuous all-rank separation. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_one_of_normalizedSeparated
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hseparated : RestrictedAllUnboundedNormalizedSeparatedContradiction A) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 1 := by
  intro ι _ p box representative offset a R hDomain F hF
  by_contra hfinite
  obtain ⟨x, w₀, data, width, hsubsequence, hinjective, hzero, hbox,
      hbox_tendsto, hrepresentative_tendsto, hcluster_nonempty,
      hcluster_disjoint, hcluster_cover, hminimum_tendsto,
      hcluster_interval, hcross_cluster, hcluster_gap⟩ :=
    hA.exists_restrictedAllUnboundedNormalizedClusterSetup
      hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_zero
      box representative offset R hDomain F hF hfinite
  exact hseparated box representative offset R hDomain F hF x w₀ data
    width hsubsequence hinjective hzero hbox hbox_tendsto
    hrepresentative_tendsto hcluster_nonempty hcluster_disjoint
    hcluster_cover hminimum_tendsto hcluster_interval hcross_cluster
    hcluster_gap
    (fun N ↦ restrictedAllUnboundedSeparationSet_infinite_fin_one x data N)

/-- The flexible callback closes the ordinary positive outer step.  The
normalized sequence and cluster data are chosen once; lower-count finiteness
then rules out the pair branch separately at every subsequently chosen rank.
-/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_q_add_two_of_normalizedSeparated
    {A : ℝ → ℝ} (hA : IsAbel A) {q : ℕ}
    (hlower : RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 1))
    (hseparated : RestrictedAllUnboundedNormalizedSeparatedContradiction A) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 2) := by
  intro ι _ p box representative offset a R hDomain F hF
  by_contra hfinite
  obtain ⟨x, w₀, data, width, hsubsequence, hinjective, hzero, hbox,
      hbox_tendsto, hrepresentative_tendsto, hcluster_nonempty,
      hcluster_disjoint, hcluster_cover, hminimum_tendsto,
      hcluster_interval, hcross_cluster, hcluster_gap⟩ :=
    hA.exists_restrictedAllUnboundedNormalizedClusterSetup
      hlower box representative offset R hDomain F hF hfinite
  have hinjective' : Function.Injective
      (fun n ↦ x (data.subsequence n)) := by
    simpa only [hsubsequence, id_eq] using hinjective
  have hzero' : ∀ n, x (data.subsequence n) ∈
      regularZeroSet (restrictedBaseOpenDomain box R) (constraintMap F) := by
    simpa only [hsubsequence, id_eq] using hzero
  have hbox_tendsto' : Tendsto
      (fun n ↦ (x (data.subsequence n)).1.2) atTop (nhds w₀) := by
    simpa only [hsubsequence, id_eq] using hbox_tendsto
  have hrepresentative_tendsto' : ∀ i, Tendsto
      (fun n ↦ (x (data.subsequence n)).1.1 i) atTop atTop := by
    simpa only [hsubsequence, id_eq] using hrepresentative_tendsto
  have hcluster_interval' : ∀ c n i, i ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤
          A ((x (data.subsequence n)).1.1 i) ∧
        A ((x (data.subsequence n)).1.1 i) ≤
          data.orderedClusterMinTime c n + (width : ℝ) := by
    simpa only [hsubsequence, id_eq] using hcluster_interval
  have hallSeparated : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite := by
    intro N
    exact hA.restrictedAllUnboundedSeparationSet_infinite_q_add_two
      hlower box representative offset R hDomain F hF x w₀ data width
      hinjective' hzero' hbox hbox_tendsto' hrepresentative_tendsto'
      hminimum_tendsto hcluster_interval' N
  exact hseparated box representative offset R hDomain F hF x w₀ data
    width hsubsequence hinjective hzero hbox hbox_tendsto
    hrepresentative_tendsto hcluster_nonempty hcluster_disjoint
    hcluster_cover hminimum_tendsto hcluster_interval hcross_cluster
    hcluster_gap hallSeparated

/-- The flexible all-rank callback closes every base representative count.
-/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_normalizedSeparated
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hseparated : RestrictedAllUnboundedNormalizedSeparatedContradiction A) :
    ∀ m, RestrictedBaseRegularZeroFiniteForRepresentativeCount A m := by
  have hzero : RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 :=
    hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_zero
  have hone : RestrictedBaseRegularZeroFiniteForRepresentativeCount A 1 :=
    hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_one_of_normalizedSeparated
      hseparated
  have hpositive : ∀ q,
      RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 1) := by
    intro q
    induction q with
    | zero => exact hone
    | succ q ih =>
        exact
          hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_q_add_two_of_normalizedSeparated
            ih hseparated
  intro m
  cases m with
  | zero => exact hzero
  | succ q => exact hpositive q

/-- Once the flexible callback supplies every base representative count, the
existing inner induction propagates it through all exponential-list levels.
-/
theorem IsAbel.restrictedRegularZeroFiniteForRepresentativeCount_all_levels_of_normalizedSeparated
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hseparated : RestrictedAllUnboundedNormalizedSeparatedContradiction A) :
    ∀ m level, RestrictedRegularZeroFiniteForRepresentativeCount A m level := by
  intro m
  exact hA.restrictedRegularZeroFiniteForRepresentativeCount_all_of_base
    (hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_normalizedSeparated
      hseparated m)

end AbelFormalization
