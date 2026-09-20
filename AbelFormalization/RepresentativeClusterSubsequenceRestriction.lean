import AbelFormalization.RestrictedOrderedClusterPartition

/-!
# Restrict cluster data to its selected subsequence

The regular-zero compactness setup records its conclusions along the
subsequence stored in `RepresentativeClusterSubsequence`.  Later analytic
arguments are more convenient when that selected sequence is made into the
ambient sequence and the stored subsequence is the identity.  This module
performs that normalization without choosing any further subsequence or
recomputing the ordered cluster partition.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

variable {m : ℕ} {time : ℕ → Fin m → ℝ}

/-- Regard the sequence already selected by `data.subsequence` as the ambient
sequence.  The cluster order and every bounded/divergent gap choice are
retained definitionally. -/
def restrictToSubsequence
    (data : RepresentativeClusterSubsequence time) :
    RepresentativeClusterSubsequence
      (fun n i ↦ time (data.subsequence n) i) where
  subsequence := id
  strictMono_subsequence := strictMono_id
  order := data.order
  ordered := data.ordered
  gap_classified := data.gap_classified

@[simp]
theorem restrictToSubsequence_subsequence
    (data : RepresentativeClusterSubsequence time) :
    data.restrictToSubsequence.subsequence = id :=
  rfl

@[simp]
theorem restrictToSubsequence_order
    (data : RepresentativeClusterSubsequence time) :
    data.restrictToSubsequence.order = data.order :=
  rfl

@[simp]
theorem restrictToSubsequence_sameCluster
    (data : RepresentativeClusterSubsequence time) :
    data.restrictToSubsequence.SameCluster = data.SameCluster :=
  rfl

@[simp]
theorem restrictToSubsequence_clusterLeaderPositions
    (data : RepresentativeClusterSubsequence time) :
    data.restrictToSubsequence.clusterLeaderPositions =
      data.clusterLeaderPositions :=
  rfl

@[simp]
theorem restrictToSubsequence_orderedClusterCount
    (data : RepresentativeClusterSubsequence time) :
    data.restrictToSubsequence.orderedClusterCount =
      data.orderedClusterCount :=
  rfl

@[simp]
theorem restrictToSubsequence_orderedCluster
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.restrictToSubsequence.orderedClusterCount) :
    data.restrictToSubsequence.orderedCluster c =
      data.orderedCluster c :=
  rfl

@[simp]
theorem restrictToSubsequence_orderedClusterMinTime
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.restrictToSubsequence.orderedClusterCount) (n : ℕ) :
    data.restrictToSubsequence.orderedClusterMinTime c n =
      data.orderedClusterMinTime c n :=
  rfl

@[simp]
theorem restrictToSubsequence_orderedClusterMaxTime
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.restrictToSubsequence.orderedClusterCount) (n : ℕ) :
    data.restrictToSubsequence.orderedClusterMaxTime c n =
      data.orderedClusterMaxTime c n :=
  rfl

/-- Restrict the sequence already selected by `data` along one further
strictly increasing map.  The new ambient sequence incorporates both
subsequence maps and the stored subsequence is normalized to the identity. -/
def restrictToFurtherSubsequence
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    RepresentativeClusterSubsequence
      (fun n i ↦ time (data.subsequence (φ n)) i) where
  subsequence := id
  strictMono_subsequence := strictMono_id
  order := data.order
  ordered := by
    intro n
    simpa only [id_eq] using data.ordered (φ n)
  gap_classified := by
    intro i j
    rcases data.gap_classified i j with hbounded | hdiverges
    · left
      rcases hbounded with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hC ⟨φ n, rfl⟩
    · right
      change Tendsto
        (fun n ↦ |time (data.subsequence (φ n)) i -
          time (data.subsequence (φ n)) j|) atTop atTop
      exact hdiverges.comp hφ.tendsto_atTop

@[simp]
theorem restrictToFurtherSubsequence_subsequence
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (data.restrictToFurtherSubsequence φ hφ).subsequence = id :=
  rfl

@[simp]
theorem restrictToFurtherSubsequence_order
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (data.restrictToFurtherSubsequence φ hφ).order = data.order :=
  rfl

@[simp]
theorem restrictToFurtherSubsequence_sameCluster
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (data.restrictToFurtherSubsequence φ hφ).SameCluster =
      data.SameCluster := by
  funext i j
  apply propext
  constructor
  · intro hrestricted
    rcases data.gap_classified i j with hbounded | hdiverges
    · exact hbounded
    · have hdiverges' : Tendsto
          (fun n ↦ |time (data.subsequence (φ n)) i -
            time (data.subsequence (φ n)) j|) atTop atTop :=
        hdiverges.comp hφ.tendsto_atTop
      have hnot := not_bddAbove_of_tendsto_atTop hdiverges'
      exact (hnot hrestricted).elim
  · intro horiginal
    rcases horiginal with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hC ⟨φ n, rfl⟩

@[simp]
theorem restrictToFurtherSubsequence_clusterLeaderPositions
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (data.restrictToFurtherSubsequence φ hφ).clusterLeaderPositions =
      data.clusterLeaderPositions := by
  classical
  apply Finset.ext
  intro i
  simp only [clusterLeaderPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, IsClusterLeader, restrictToFurtherSubsequence_order]
  rw [restrictToFurtherSubsequence_sameCluster]

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterCount
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount =
      data.orderedClusterCount := by
  simp only [orderedClusterCount,
    restrictToFurtherSubsequence_clusterLeaderPositions]

/-- The canonical order isomorphism identifying the unchanged cluster
indices after a further restriction. -/
def restrictToFurtherSubsequenceClusterEquiv
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount ≃o
      Fin data.orderedClusterCount :=
  Fin.castOrderIso
    (restrictToFurtherSubsequence_orderedClusterCount data φ hφ)

private theorem finset_orderIsoOfFin_cast_eq
    {α : Type*} [LinearOrder α] (s t : Finset α) (h : s = t)
    (c : Fin s.card) :
    ((s.orderIsoOfFin rfl c : s) : α) =
      ((t.orderIsoOfFin rfl (Fin.cast (congrArg Finset.card h) c) : t) : α) := by
  subst t
  rfl

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterLeaderPosition
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterLeaderPosition c =
      data.orderedClusterLeaderPosition
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) := by
  let hleaders :=
    restrictToFurtherSubsequence_clusterLeaderPositions data φ hφ
  have hc : data.restrictToFurtherSubsequenceClusterEquiv φ hφ c =
      Fin.cast (congrArg Finset.card hleaders) c := by
    apply Fin.ext
    rfl
  unfold orderedClusterLeaderPosition
  rw [hc]
  exact finset_orderIsoOfFin_cast_eq
    (data.restrictToFurtherSubsequence φ hφ).clusterLeaderPositions
    data.clusterLeaderPositions hleaders c

@[simp]
theorem restrictToFurtherSubsequence_orderedCluster
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount) :
    (data.restrictToFurtherSubsequence φ hφ).orderedCluster c =
      data.orderedCluster
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) := by
  classical
  apply Finset.ext
  intro i
  rw [mem_orderedCluster_iff, mem_orderedCluster_iff]
  simp only [restrictToFurtherSubsequence_order,
    restrictToFurtherSubsequence_orderedClusterLeaderPosition]
  rw [restrictToFurtherSubsequence_sameCluster]

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterPositions
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterPositions c =
      data.orderedClusterPositions
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) := by
  classical
  apply Finset.ext
  intro i
  rw [mem_orderedClusterPositions_iff, mem_orderedClusterPositions_iff]
  simp only [restrictToFurtherSubsequence_order,
    restrictToFurtherSubsequence_orderedCluster]

private theorem finset_max'_eq_of_eq
    {α : Type*} [LinearOrder α] (s t : Finset α)
    (hs : s.Nonempty) (ht : t.Nonempty) (h : s = t) :
    s.max' hs = t.max' ht := by
  subst t
  rfl

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterLastPosition
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterLastPosition c =
      data.orderedClusterLastPosition
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) := by
  apply finset_max'_eq_of_eq
  exact restrictToFurtherSubsequence_orderedClusterPositions data φ hφ c

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterFirst
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterFirst c =
      data.orderedClusterFirst
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) := by
  simp only [orderedClusterFirst, restrictToFurtherSubsequence_order,
    restrictToFurtherSubsequence_orderedClusterLeaderPosition]

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterLast
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterLast c =
      data.orderedClusterLast
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) := by
  simp only [orderedClusterLast, restrictToFurtherSubsequence_order,
    restrictToFurtherSubsequence_orderedClusterLastPosition]

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterMinTime
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount)
    (n : ℕ) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterMinTime c n =
      data.orderedClusterMinTime
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) (φ n) := by
  simp only [orderedClusterMinTime,
    restrictToFurtherSubsequence_subsequence, id_eq,
    restrictToFurtherSubsequence_orderedClusterFirst]

@[simp]
theorem restrictToFurtherSubsequence_orderedClusterMaxTime
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (c : Fin (data.restrictToFurtherSubsequence φ hφ).orderedClusterCount)
    (n : ℕ) :
    (data.restrictToFurtherSubsequence φ hφ).orderedClusterMaxTime c n =
      data.orderedClusterMaxTime
        (data.restrictToFurtherSubsequenceClusterEquiv φ hφ c) (φ n) := by
  simp only [orderedClusterMaxTime,
    restrictToFurtherSubsequence_subsequence, id_eq,
    restrictToFurtherSubsequence_orderedClusterLast]

end RepresentativeClusterSubsequence
end AbelFormalization
