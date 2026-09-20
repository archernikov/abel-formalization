import AbelFormalization.ClusterBalancing
import AbelFormalization.RestrictedRepresentativeSubsequence
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Subsequence extraction of ordered representative clusters

This module formalizes the finite subsequence step at the start of the
all-unbounded branch.  It fixes one ordering of the Abel times and classifies
every pairwise absolute gap as bounded or divergent.  Bounded gap is then an
equivalence relation, its classes have one uniform finite width, and distinct
classes in the fixed order have a signed gap tending to positive infinity.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- A finite family of real sequences admits one common subsequence along
which every member is either bounded above or tends to positive infinity. -/
theorem exists_strictMono_subsequence_finite_family_classified
    {ι : Type} [Fintype ι] (u : ℕ → ι → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i,
      BddAbove (Set.range (fun n ↦ u (φ n) i)) ∨
        Tendsto (fun n ↦ u (φ n) i) atTop atTop := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨φ, hφ, hclass⟩ :=
    exists_strictMono_subsequence_representatives_classified
      (fun n j ↦ u n (e.symm j))
  refine ⟨φ, hφ, ?_⟩
  intro i
  simpa only [e.symm_apply_apply] using hclass (e i)

/-- Two coordinates belong to the same asymptotic cluster when their
absolute difference is bounded along the whole selected sequence. -/
def BoundedGapRelation {ι : Type} (time : ℕ → ι → ℝ) (i j : ι) : Prop :=
  BddAbove (Set.range (fun n ↦ |time n i - time n j|))

theorem boundedGapRelation_refl {ι : Type} (time : ℕ → ι → ℝ) :
    ∀ i, BoundedGapRelation time i i := by
  intro i
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp

theorem boundedGapRelation_symm {ι : Type} (time : ℕ → ι → ℝ) :
    ∀ i j, BoundedGapRelation time i j → BoundedGapRelation time j i := by
  intro i j hij
  simpa only [BoundedGapRelation, abs_sub_comm] using hij

theorem boundedGapRelation_trans {ι : Type} (time : ℕ → ι → ℝ) :
    ∀ i j k, BoundedGapRelation time i j → BoundedGapRelation time j k →
      BoundedGapRelation time i k := by
  intro i j k hij hjk
  rcases hij with ⟨Cij, hCij⟩
  rcases hjk with ⟨Cjk, hCjk⟩
  refine ⟨Cij + Cjk, ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    |time n i - time n k| =
        |(time n i - time n j) + (time n j - time n k)| := by
          congr 1
          ring
    _ ≤ |time n i - time n j| + |time n j - time n k| := abs_add_le _ _
    _ ≤ Cij + Cjk := add_le_add
      (hCij ⟨n, rfl⟩) (hCjk ⟨n, rfl⟩)

/-- Bounded pairwise gap is an equivalence relation for every family of real
sequences. -/
theorem boundedGapRelation_equivalence {ι : Type} (time : ℕ → ι → ℝ) :
    Equivalence (BoundedGapRelation time) := by
  refine ⟨boundedGapRelation_refl time, ?_, ?_⟩
  · intro i j hij
    exact boundedGapRelation_symm time _ _ hij
  · intro i j k hij hjk
    exact boundedGapRelation_trans time _ _ _ hij hjk

/-- The fixed data produced by the representative-cluster subsequence. -/
structure RepresentativeClusterSubsequence {m : ℕ}
    (time : ℕ → Fin m → ℝ) where
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  order : Equiv.Perm (Fin m)
  ordered : ∀ n, Monotone (fun i ↦ time (subsequence n) (order i))
  gap_classified : ∀ i j,
    BoundedGapRelation (fun n k ↦ time (subsequence n) k) i j ∨
      Tendsto (fun n ↦
        |time (subsequence n) i - time (subsequence n) j|) atTop atTop

/-- Fix the coordinate order and all bounded/divergent pairwise-gap choices
on one strictly increasing subsequence. -/
theorem exists_representativeClusterSubsequence {m : ℕ}
    (time : ℕ → Fin m → ℝ) :
    Nonempty (RepresentativeClusterSubsequence time) := by
  classical
  let sorting : ℕ → Equiv.Perm (Fin m) := fun n ↦ Tuple.sort (time n)
  obtain ⟨φ, order, hφ, hsorting⟩ :=
    exists_strictMono_subsequence_const_of_finite sorting
  let firstTime : ℕ → Fin m → ℝ := fun n i ↦ time (φ n) i
  obtain ⟨ψ, hψ, hgap⟩ :=
    exists_strictMono_subsequence_finite_family_classified
      (fun n (ij : Fin m × Fin m) ↦
        |firstTime n ij.1 - firstTime n ij.2|)
  let χ : ℕ → ℕ := φ ∘ ψ
  refine ⟨{
    subsequence := χ
    strictMono_subsequence := hφ.comp hψ
    order := order
    ordered := ?_
    gap_classified := ?_ }⟩
  · intro n
    have hsort := Tuple.monotone_sort (time (φ (ψ n)))
    have heq : Tuple.sort (time (φ (ψ n))) = order := hsorting (ψ n)
    rw [heq] at hsort
    intro i j hij
    have h := hsort hij
    change time (φ (ψ n)) (order i) ≤ time (φ (ψ n)) (order j) at h
    exact h
  · intro i j
    have hij := hgap (i, j)
    simpa only [BoundedGapRelation, χ, firstTime, Function.comp_apply] using hij

namespace RepresentativeClusterSubsequence

variable {m : ℕ} {time : ℕ → Fin m → ℝ}

/-- The selected cluster relation on the original representative labels. -/
def SameCluster (data : RepresentativeClusterSubsequence time) :
    Fin m → Fin m → Prop :=
  BoundedGapRelation (fun n i ↦ time (data.subsequence n) i)

/-- The selected cluster relation is an equivalence relation. -/
theorem sameCluster_equivalence
    (data : RepresentativeClusterSubsequence time) :
    Equivalence data.SameCluster :=
  boundedGapRelation_equivalence _

/-- Distinct ordered clusters have a signed Abel-time gap tending to positive
infinity. -/
theorem tendsto_ordered_gap_atTop
    (data : RepresentativeClusterSubsequence time)
    {i j : Fin m} (hij : i < j)
    (hclusters : ¬ data.SameCluster (data.order i) (data.order j)) :
    Tendsto (fun n ↦
      time (data.subsequence n) (data.order j) -
        time (data.subsequence n) (data.order i)) atTop atTop := by
  rcases data.gap_classified (data.order i) (data.order j) with hbounded | hgap
  · exact (hclusters hbounded).elim
  · convert hgap using 1
    funext n
    rw [abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (data.ordered n hij.le)

/-- A single constant bounds every gap within every selected cluster. -/
theorem exists_uniform_sameCluster_bound
    (data : RepresentativeClusterSubsequence time) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j, data.SameCluster i j → ∀ n,
      |time (data.subsequence n) i - time (data.subsequence n) j| ≤ C := by
  classical
  have hexists : ∀ i j : Fin m, ∃ C : ℝ,
      data.SameCluster i j → ∀ n,
        |time (data.subsequence n) i - time (data.subsequence n) j| ≤ C := by
    intro i j
    by_cases hij : data.SameCluster i j
    · rcases hij with ⟨C, hC⟩
      refine ⟨C, fun _ n ↦ hC ⟨n, rfl⟩⟩
    · exact ⟨0, fun h ↦ (hij h).elim⟩
  choose bound hbound using hexists
  let C : ℝ := ∑ i : Fin m, ∑ j : Fin m, max 0 (bound i j)
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    exact Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ le_max_left _ _
  · intro i j hij n
    calc
      |time (data.subsequence n) i - time (data.subsequence n) j| ≤
          bound i j := hbound i j hij n
      _ ≤ max 0 (bound i j) := le_max_right _ _
      _ ≤ ∑ j' : Fin m, max 0 (bound i j') := by
        exact Finset.single_le_sum
          (fun j' _ ↦ le_max_left (0 : ℝ) (bound i j'))
          (Finset.mem_univ j)
      _ ≤ C := by
        dsimp only [C]
        exact Finset.single_le_sum
          (fun i' _ ↦ Finset.sum_nonneg fun j' _ ↦
            le_max_left (0 : ℝ) (bound i' j'))
          (Finset.mem_univ i)

end RepresentativeClusterSubsequence

end AbelFormalization
