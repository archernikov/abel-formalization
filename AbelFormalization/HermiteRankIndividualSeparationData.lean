import AbelFormalization.HermiteRankPreprocessedIndividualQuantitativeInputs
import AbelFormalization.RestrictedAllUnboundedBranchDichotomy

/-!
# Separation data for the concrete Hermite trace

The separated branch supplies the reciprocal inverse-Abel gap with constant
one.  This file packages that literal inequality in the quantitative record
used by every individual and simultaneous operation.  Keeping the constructor
separate avoids rebuilding any Hermite or algebraic descent data after a
separated subsequence has been selected.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter

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

/-- A pointwise reciprocal inverse-Abel separation estimate packages directly
as the common separation record for the preprocessed Hermite trace. -/
def individualSeparationDataOfRawTime
    (N : ℕ) (hN : 5 ≤ N)
    (hseparated : ∀ n (c : Fin data.orderedClusterCount)
      (i k : Fin (data.orderedClusterTailSize c + 1)), i ≠ k →
        (inverse A (data.orderedClusterMinTime c n - (N : ℝ)))⁻¹ ≤
          integerDistance
            (data.orderedClusterRawTime n c i -
              data.orderedClusterRawTime n c k)) :
    boundary.IndividualSeparationData D representative offset radius Fsys x
      w₀ hw₀ data where
  separationConstant := fun _ ↦ 1
  N := fun _ ↦ N
  separationConstant_pos := fun _ ↦ one_pos
  five_le_N := fun _ ↦ by exact_mod_cast hN
  separated := by
    intro c
    filter_upwards with n
    intro i k hik
    simpa only [one_div] using
      hseparated (boundary.preprocessed.balancingSubsequence n) c i k hik

/-- If every index lies in the manuscript's simultaneous separation set,
the constant-one quantitative separation record is available immediately. -/
def individualSeparationDataOfMemSeparationSet
    (N : ℕ) (hN : 5 ≤ N)
    (hall : ∀ n, n ∈ restrictedAllUnboundedSeparationSet x data N) :
    boundary.IndividualSeparationData D representative offset radius Fsys x
      w₀ hw₀ data := by
  apply boundary.individualSeparationDataOfRawTime D representative offset
    radius Fsys x w₀ hw₀ data N hN
  intro n c i k hik
  have h := hall n c
    (data.orderedClusterEnumeration c i)
    (data.orderedClusterEnumeration_mem c i)
    (data.orderedClusterEnumeration c k)
    (data.orderedClusterEnumeration_mem c k)
  have henum : data.orderedClusterEnumeration c i ≠
      data.orderedClusterEnumeration c k := by
    intro heq
    apply hik
    have hsubtype :
        ((data.orderedCluster c).equivFin).symm
            (finCongr (data.orderedClusterTailSize_add_one c) i) =
          ((data.orderedCluster c).equivFin).symm
            (finCongr (data.orderedClusterTailSize_add_one c) k) := by
      exact Subtype.ext heq
    have hfin := ((data.orderedCluster c).equivFin).symm.injective hsubtype
    exact (finCongr (data.orderedClusterTailSize_add_one c)).injective hfin
  simpa only [RepresentativeClusterSubsequence.orderedClusterRawTime] using
    h henum

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
