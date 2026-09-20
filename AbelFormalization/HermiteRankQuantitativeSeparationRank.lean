import AbelFormalization.HermiteRankIndividualSeparationData

/-!
# One separation rank for the finite preprocessed trace

The simultaneous transfer at operation `r` asks for the margin `r + 6`.
There are finitely many retained simultaneous operations in every ordered
cluster.  Summing their successor counts and adding five gives one natural
rank which dominates every required margin and also the individual-step
margin five.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

/-- Successor count of the simultaneous operations retained at one cluster:
the distinguished first operation plus all extra operations. -/
abbrev clusterSimultaneousOperationCount
    (c : Fin data.orderedClusterCount) : ℕ :=
  (boundary.preprocessed.descent.clusterStage c).certificate.terminalized.extraSteps + 1

/-- A single separation rank large enough for every quantitative operation
in the finite ordered-cluster descent. -/
def quantitativeSeparationRank : ℕ :=
  5 + ∑ c : Fin data.orderedClusterCount,
    boundary.clusterSimultaneousOperationCount D representative offset radius
      Fsys x w₀ hw₀ data c

theorem five_le_quantitativeSeparationRank :
    5 ≤ boundary.quantitativeSeparationRank D representative offset radius Fsys
      x w₀ hw₀ data := by
  unfold quantitativeSeparationRank
  omega

/-- Every operation-specific simultaneous margin is bounded by the common
rank. -/
theorem simultaneousMargin_le_quantitativeSeparationRank
    (c : Fin data.orderedClusterCount)
    (r : Fin (boundary.clusterSimultaneousOperationCount D representative
      offset radius Fsys x w₀ hw₀ data c)) :
    r.val + 6 ≤
      boundary.quantitativeSeparationRank D representative offset radius Fsys
        x w₀ hw₀ data := by
  let count : Fin data.orderedClusterCount → ℕ := fun d ↦
    boundary.clusterSimultaneousOperationCount D representative offset radius
      Fsys x w₀ hw₀ data d
  have hcount : count c ≤ ∑ d : Fin data.orderedClusterCount, count d := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)
  have hr0 : r.val < count c := by
    simpa only [count] using r.isLt
  have hr : r.val + 1 ≤ count c := Nat.succ_le_of_lt hr0
  unfold quantitativeSeparationRank
  change r.val + 6 ≤ 5 + ∑ d : Fin data.orderedClusterCount, count d
  omega

/-- Pointwise membership in the separation set at the common rank supplies
the concrete separation record with all individual margins discharged. -/
def quantitativeIndividualSeparationData
    (hall : ∀ n, n ∈ restrictedAllUnboundedSeparationSet x data
      (boundary.quantitativeSeparationRank D representative offset radius Fsys
        x w₀ hw₀ data)) :
    boundary.IndividualSeparationData D representative offset radius Fsys x
      w₀ hw₀ data :=
  boundary.individualSeparationDataOfMemSeparationSet D representative offset
    radius Fsys x w₀ hw₀ data
    (boundary.quantitativeSeparationRank D representative offset radius Fsys x
      w₀ hw₀ data)
    (boundary.five_le_quantitativeSeparationRank D representative offset radius
      Fsys x w₀ hw₀ data) hall

/-- The real-valued margin required by any simultaneous operation follows
from the common separation-rank construction. -/
theorem quantitativeIndividualSeparationData_simultaneousMargin
    (hall : ∀ n, n ∈ restrictedAllUnboundedSeparationSet x data
      (boundary.quantitativeSeparationRank D representative offset radius Fsys
        x w₀ hw₀ data))
    (c : Fin data.orderedClusterCount)
    (r : Fin (boundary.clusterSimultaneousOperationCount D representative
      offset radius Fsys x w₀ hw₀ data c)) :
    (((r.val + 6 : ℕ) : ℝ)) ≤
      (boundary.quantitativeIndividualSeparationData D representative offset
        radius Fsys x w₀ hw₀ data hall).N c := by
  change (((r.val + 6 : ℕ) : ℝ)) ≤
    (boundary.quantitativeSeparationRank D representative offset radius Fsys x
      w₀ hw₀ data : ℝ)
  exact_mod_cast boundary.simultaneousMargin_le_quantitativeSeparationRank D
    representative offset radius Fsys x w₀ hw₀ data c r

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
