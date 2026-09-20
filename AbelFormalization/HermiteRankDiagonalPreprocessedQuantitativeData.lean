import AbelFormalization.HermiteRankQuantitativeSeparationRank
import AbelFormalization.RestrictedAllUnboundedDiagonalRestriction
import AbelFormalization.HermiteRankPreprocessedIndividualMixedBoundary
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeTail

/-!
# The preprocessed Hermite trace on the all-rank diagonal restriction

The separation rank needed by the finite preprocessed trace is known only
after the Hermite/rank boundary and its algebraic descent have been chosen.
The all-rank diagonal sequence removes this apparent circularity: first build
the boundary on that one sequence, then specialize its eventual separation
property to the boundary's newly chosen quantitative rank.

The quantitative hierarchy only asks for separation eventually along the
fixed balancing subsequence.  Accordingly, no rank-dependent ambient tail and
no reconstruction of the Hermite boundary is needed.  This file packages the
resulting boundary-dependent separation data and discharges the common margin
for every individual and simultaneous operation.  The genuinely analytic
finite change-of-generators records remain explicit inputs.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open Filter Function Set
open scoped Topology

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

/-- Eventual membership in one separation set is sufficient for the concrete
constant-one separation record.  The eventual statement is pulled back along
the fixed balancing subsequence chosen inside the preprocessed boundary. -/
def individualSeparationDataOfEventuallyMemSeparationSet
    (N : ℕ) (hN : 5 ≤ N)
    (hall : ∀ᶠ n in atTop,
      n ∈ restrictedAllUnboundedSeparationSet x data N) :
    boundary.IndividualSeparationData D representative offset radius Fsys x
      w₀ hw₀ data where
  separationConstant := fun _ ↦ 1
  N := fun _ ↦ N
  separationConstant_pos := fun _ ↦ one_pos
  five_le_N := fun _ ↦ by exact_mod_cast hN
  separated := by
    intro c
    have hselected : ∀ᶠ n in atTop,
        boundary.preprocessed.balancingSubsequence n ∈
          restrictedAllUnboundedSeparationSet x data N :=
      boundary.preprocessed.balancingSubsequence_strictMono.tendsto_atTop.eventually
        hall
    filter_upwards [hselected] with n hn
    intro i k hik
    have h := hn c
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
    simpa only [one_div,
      RepresentativeClusterSubsequence.orderedClusterRawTime] using h henum

/-- Specialize eventual separation to the single rank dominating the whole
finite preprocessed transfer trace. -/
def quantitativeIndividualSeparationDataOfEventuallyMem
    (hall : ∀ᶠ n in atTop,
      n ∈ restrictedAllUnboundedSeparationSet x data
        (boundary.quantitativeSeparationRank D representative offset radius
          Fsys x w₀ hw₀ data)) :
    boundary.IndividualSeparationData D representative offset radius Fsys x
      w₀ hw₀ data :=
  boundary.individualSeparationDataOfEventuallyMemSeparationSet D
    representative offset radius Fsys x w₀ hw₀ data
    (boundary.quantitativeSeparationRank D representative offset radius Fsys x
      w₀ hw₀ data)
    (boundary.five_le_quantitativeSeparationRank D representative offset radius
      Fsys x w₀ hw₀ data) hall

/-- Every simultaneous operation-specific margin is discharged by the
eventual all-rank separation record. -/
theorem quantitativeIndividualSeparationDataOfEventuallyMem_simultaneousMargin
    (hall : ∀ᶠ n in atTop,
      n ∈ restrictedAllUnboundedSeparationSet x data
        (boundary.quantitativeSeparationRank D representative offset radius
          Fsys x w₀ hw₀ data))
    (c : Fin data.orderedClusterCount)
    (r : Fin (boundary.clusterSimultaneousOperationCount D representative
      offset radius Fsys x w₀ hw₀ data c)) :
    (((r.val + 6 : ℕ) : ℝ)) ≤
      (boundary.quantitativeIndividualSeparationDataOfEventuallyMem D
        representative offset radius Fsys x w₀ hw₀ data hall).N c := by
  change (((r.val + 6 : ℕ) : ℝ)) ≤
    (boundary.quantitativeSeparationRank D representative offset radius Fsys x
      w₀ hw₀ data : ℝ)
  exact_mod_cast boundary.simultaneousMargin_le_quantitativeSeparationRank D
    representative offset radius Fsys x w₀ hw₀ data c r

/-- The largest simultaneous margin at a cluster, in the exact form consumed
by the finite reverse simultaneous segment. -/
theorem quantitativeIndividualSeparationDataOfEventuallyMem_terminalMargin
    (hall : ∀ᶠ n in atTop,
      n ∈ restrictedAllUnboundedSeparationSet x data
        (boundary.quantitativeSeparationRank D representative offset radius
          Fsys x w₀ hw₀ data))
    (c : Fin data.orderedClusterCount) :
    ((((boundary.simultaneousNumericStage D representative offset radius Fsys
        x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ)) ≤
      (boundary.quantitativeIndividualSeparationDataOfEventuallyMem D
        representative offset radius Fsys x w₀ hw₀ data hall).N c := by
  simpa only using
    boundary.quantitativeIndividualSeparationDataOfEventuallyMem_simultaneousMargin
      D representative offset radius Fsys x w₀ hw₀ data hall c
      ⟨(boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data c).certificate.terminalized.extraSteps,
        Nat.lt_succ_self _⟩

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

/-- A single diagonal restriction together with the preprocessed Hermite/rank
boundary built on it.  The proof of all-rank infinitude is stored first
because the actual diagonal sequence and cluster data depend on that choice. -/
structure DiagonalHermiteRankPreprocessedQuantitativeData
    (hA : IsAbel A)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (radius : ℝ)
    (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (x : ℕ → RestrictedSource m p a)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))) where
  separationSet_infinite : ∀ N,
    (restrictedAllUnboundedSeparationSet x data N).Infinite
  boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
    D representative offset radius Fsys
    (hA.diagonalSeparatedAmbientSequence x data separationSet_infinite)
    w₀ hw₀
    (hA.diagonalSeparatedClusterData x data separationSet_infinite)

/-- Construct the diagonal preprocessed boundary from one fixed
all-unbounded setup whose separation sets are infinite at every rank. -/
theorem IsAbel.nonempty_diagonalHermiteRankPreprocessedQuantitativeData
    (hA : IsAbel A)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (radius : ℝ)
    (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, Fsys i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hx : ∀ n, x (data.subsequence n) ∈ regularZeroSet
      (restrictedBaseOpenDomain D radius) (constraintMap Fsys))
    (hxrepresentative : ∀ i,
      Tendsto (fun n ↦ (x (data.subsequence n)).1.1 i) atTop atTop)
    (hxlim : Tendsto (fun n ↦ (x (data.subsequence n)).1.2)
      atTop (nhds w₀))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) :
    Nonempty (DiagonalHermiteRankPreprocessedQuantitativeData hA D
      representative offset radius Fsys x w₀ hw₀ data) := by
  obtain ⟨boundary⟩ :=
    hA.exists_restrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
      D representative offset radius Fsys hF
      (hA.diagonalSeparatedAmbientSequence x data hinfinite)
      (fun n ↦ hA.diagonalSeparatedAmbientSequence_mem x data hinfinite hx n)
      (fun i ↦ hA.tendsto_diagonalSeparatedAmbientSequence x data hinfinite
        (fun y ↦ y.1.1 i) (hxrepresentative i))
      w₀ hw₀
      (hA.tendsto_diagonalSeparatedAmbientSequence x data hinfinite
        (fun y ↦ y.1.2) hxlim)
      (hA.diagonalSeparatedClusterData x data hinfinite)
  exact ⟨{
    separationSet_infinite := hinfinite
    boundary := boundary
  }⟩

/-- Exact adapter for the normalized setup used by
`RestrictedAllUnboundedNormalizedSeparatedContradiction`. -/
theorem IsAbel.nonempty_diagonalHermiteRankPreprocessedQuantitativeData_of_normalized
    (hA : IsAbel A)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (radius : ℝ)
    (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, Fsys i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hsubsequence : data.subsequence = id)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D radius) (constraintMap Fsys))
    (hxrepresentative : ∀ i,
      Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) :
    Nonempty (DiagonalHermiteRankPreprocessedQuantitativeData hA D
      representative offset radius Fsys x w₀ hw₀ data) := by
  apply hA.nonempty_diagonalHermiteRankPreprocessedQuantitativeData D
    representative offset radius Fsys hF x w₀ hw₀ data
  · simpa only [hsubsequence, id_eq] using hx
  · intro i
    simpa only [hsubsequence, id_eq] using hxrepresentative i
  · simpa only [hsubsequence, id_eq] using hxlim
  · exact hinfinite

namespace DiagonalHermiteRankPreprocessedQuantitativeData

variable (hA : IsAbel A)
variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (diagonal : DiagonalHermiteRankPreprocessedQuantitativeData hA D
  representative offset radius Fsys x w₀ hw₀ data)

/-- The one diagonal ambient sequence on which all subsequent choices are
made. -/
abbrev ambientSequence : ℕ → RestrictedSource m p a :=
  hA.diagonalSeparatedAmbientSequence x data diagonal.separationSet_infinite

/-- The unchanged ordered clusters, normalized to the identity subsequence,
on the diagonal ambient sequence. -/
abbrev clusterData : RepresentativeClusterSubsequence
    (fun n i ↦ A (((diagonal.ambientSequence hA D representative offset radius
      Fsys x w₀ hw₀ data n).1.1 i))) :=
  hA.diagonalSeparatedClusterData x data diagonal.separationSet_infinite

@[simp]
theorem clusterData_subsequence :
    (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
      data).subsequence = id :=
  hA.diagonalSeparatedClusterData_subsequence x data
    diagonal.separationSet_infinite

/-- The boundary-dependent common separation rank holds eventually on the
single diagonal ambient sequence. -/
theorem eventually_mem_quantitativeSeparationRank :
    ∀ᶠ n in atTop,
      n ∈ restrictedAllUnboundedSeparationSet
        (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
          hw₀ data)
        (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
          data)
        (diagonal.boundary.quantitativeSeparationRank D representative offset
          radius Fsys
          (diagonal.ambientSequence hA D representative offset radius Fsys x
            w₀ hw₀ data)
          w₀ hw₀
          (diagonal.clusterData hA D representative offset radius Fsys x w₀
            hw₀ data)) := by
  exact hA.diagonalSeparatedAmbientSequence_eventually_mem x data
    diagonal.separationSet_infinite _

/-- Canonical quantitative separation data for the diagonal boundary. -/
noncomputable def separation :
    diagonal.boundary.IndividualSeparationData D representative offset radius
      Fsys
      (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
        hw₀ data)
      w₀ hw₀
      (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
        data) :=
  diagonal.boundary.quantitativeIndividualSeparationDataOfEventuallyMem D
    representative offset radius Fsys
    (diagonal.ambientSequence hA D representative offset radius Fsys x w₀ hw₀
      data)
    w₀ hw₀
    (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
      data)
    (diagonal.eventually_mem_quantitativeSeparationRank hA D representative
      offset radius Fsys x w₀ hw₀ data)

/-- Exact value of the separation exponent at every cluster. -/
@[simp]
theorem separation_N
    (c : Fin (diagonal.clusterData hA D representative offset radius Fsys x
      w₀ hw₀ data).orderedClusterCount) :
    (diagonal.separation hA D representative offset radius Fsys x w₀ hw₀
        data).N c =
      diagonal.boundary.quantitativeSeparationRank D representative offset
        radius Fsys
        (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
          hw₀ data)
        w₀ hw₀
        (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
          data) :=
  rfl

/-- The maximal simultaneous margin at a cluster is now fully concrete. -/
theorem terminalSimultaneousMargin
    (c : Fin (diagonal.clusterData hA D representative offset radius Fsys x
      w₀ hw₀ data).orderedClusterCount) :
    ((((diagonal.boundary.simultaneousNumericStage D representative offset
        radius Fsys
        (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
          hw₀ data)
        w₀ hw₀
        (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
          data) c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ)) ≤
      (diagonal.separation hA D representative offset radius Fsys x w₀ hw₀
        data).N c := by
  exact
    diagonal.boundary.quantitativeIndividualSeparationDataOfEventuallyMem_terminalMargin
      D representative offset radius Fsys
      (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
        hw₀ data)
      w₀ hw₀
      (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
        data)
      (diagonal.eventually_mem_quantitativeSeparationRank hA D representative
        offset radius Fsys x w₀ hw₀ data) c

/-- The recursively mixed individual boundary on the diagonal sequence, with
all Hermite thresholds and coordinate bounds already discharged. -/
noncomputable def individualMixedBoundaryCompatibility
    (c : Fin (diagonal.clusterData hA D representative offset radius Fsys x
      w₀ hw₀ data).orderedClusterCount) :=
  diagonal.boundary.individualMixedNumericBoundaryCompatibility D
    representative offset radius Fsys
    (diagonal.ambientSequence hA D representative offset radius Fsys x w₀ hw₀
      data)
    w₀ hw₀
    (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
      data) hA c

/-- The mixed individual jet error estimate with diagonal separation supplied
by the canonical all-rank package. -/
theorem individualMixedTraceJets_error_superpolynomialDecay
    (c : Fin (diagonal.clusterData hA D representative offset radius Fsys x
      w₀ hw₀ data).orderedClusterCount)
    (j : Fin (diagonal.boundary.preprocessed.fixedSteps c).length)
    (i : Fin 1)
    (r : Fin ((diagonal.clusterData hA D representative offset radius Fsys x
      w₀ hw₀ data).orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount diagonal.boundary.S) c
        (diagonal.boundary.preprocessed.fixedSteps c) j i)) :
    Asymptotics.SuperpolynomialDecay atTop
      ((diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
        data).orderedClusterBalancingPrefixScale A
        (diagonal.boundary.individualQuantitativeSubsequence D representative
          offset radius Fsys
          (diagonal.ambientSequence hA D representative offset radius Fsys x
            w₀ hw₀ data)
          w₀ hw₀
          (diagonal.clusterData hA D representative offset radius Fsys x w₀
            hw₀ data) hA)
        c (diagonal.boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦
        (diagonal.boundary.individualMixedTraceJets D representative offset
          radius Fsys
          (diagonal.ambientSequence hA D representative offset radius Fsys x
            w₀ hw₀ data)
          w₀ hw₀
          (diagonal.clusterData hA D representative offset radius Fsys x w₀
            hw₀ data) hA c j n i).error r) :=
  diagonal.boundary.individualMixedTraceJets_error_superpolynomialDecay D
    representative offset radius Fsys
    (diagonal.ambientSequence hA D representative offset radius Fsys x w₀ hw₀
      data)
    w₀ hw₀
    (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
      data)
    (diagonal.separation hA D representative offset radius Fsys x w₀ hw₀ data)
    hA c j i r

/-- Build the complete simultaneous numeric segment on the diagonal common
tail.  Only the finite analytic representatives and change matrices remain
as an explicit input. -/
noncomputable def simultaneousNumericSegment
    (c : Fin (diagonal.clusterData hA D representative offset radius Fsys x
      w₀ hw₀ data).orderedClusterCount)
    (segment : diagonal.boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData
      D representative offset radius Fsys
      (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
        hw₀ data)
      w₀ hw₀
      (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
        data) hA c) :
    diagonal.boundary.HermiteSimultaneousQuantitativeNumericSegmentData D
      representative offset radius Fsys
      (diagonal.ambientSequence hA D representative offset radius Fsys x w₀
        hw₀ data)
      w₀ hw₀
      (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
        data) hA c :=
  diagonal.boundary.hermiteSimultaneousQuantitativeNumericSegmentData D
    representative offset radius Fsys
    (diagonal.ambientSequence hA D representative offset radius Fsys x w₀ hw₀
      data)
    w₀ hw₀
    (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀
      data)
    (diagonal.separation hA D representative offset radius Fsys x w₀ hw₀ data)
    hA c
    (diagonal.terminalSimultaneousMargin hA D representative offset radius
      Fsys x w₀ hw₀ data c)
    segment

end DiagonalHermiteRankPreprocessedQuantitativeData
end AbelFormalization
