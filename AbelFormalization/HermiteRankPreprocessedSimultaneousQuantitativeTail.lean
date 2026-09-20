import AbelFormalization.HermiteRankPreprocessedSimultaneousNumericData
import AbelFormalization.QuantitativeReindexing

/-!
# A common quantitative tail for the Hermite simultaneous segment

The individual part of the ordered-cluster trace already discards one global
prefix.  A simultaneous Hermite jet has an additional finite central
threshold, and that threshold need not hold on the unshifted selected
sequence.  This module chooses one further tail for every cluster, every
retained simultaneous operation, and every active block.

The resulting cofinal index is literally
`n + individualQuantitativeTail + simultaneousQuantitativeTail`.  Thus the
simultaneous segment and the individual terminal boundary use one common
selected balancing sequence, up to the explicitly named further tail.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology BigOperators

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
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

/-- Every post-log center of every simultaneous operation diverges on the
selected balancing sequence. -/
theorem simultaneousNumericPostLogScale_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) :
    Tendsto
      (boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r i) atTop atTop := by
  let e := data.orderedClusterBalancingToActiveEquiv c
  let shift : ℝ := ((r + 1 : ℕ) : ℝ)
  apply hA.inverse_tendsto_atTop.comp
  have hmin := boundary.selectedClusterMinTime_tendsto_atTop D representative
    offset radius Fsys x w₀ hw₀ data hA c
  have hminShift : Tendsto (fun n ↦
      data.orderedClusterMinTime c
        (boundary.preprocessed.balancingSubsequence n) - shift)
      atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hmin.eventually (eventually_ge_atTop (b + shift))] with n hn
    linarith
  apply tendsto_atTop_mono' atTop _ hminShift
  filter_upwards [] with n
  have hbase := (boundary.preprocessed.plans n c).base_le_final
    (boundary.preprocessed.fixedOrder c (e.symm i))
  have hsteps := boundary.preprocessed.plans_steps n c
  dsimp only [simultaneousNumericPostLogScale, simultaneousPostLogScale,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale,
    RepresentativeClusterSubsequence.orderedClusterPostBalancingFinalOrderTime]
  change data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence n) - shift ≤
    clusterShiftedTimes
      (data.orderedClusterRawTime
        (boundary.preprocessed.balancingSubsequence n) c)
      (boundary.preprocessed.fixedSteps c)
      (boundary.preprocessed.fixedOrder c (e.symm i)) - shift
  rw [← hsteps]
  exact sub_le_sub_right hbase shift

/-- Dependent finite index of all simultaneous Hermite centers in the whole
ordered-cluster trace. -/
abbrev SimultaneousJetIndex :=
  Sigma fun c : Fin data.orderedClusterCount ↦
    Sigma fun _r : Fin ((boundary.simultaneousNumericStage D representative
      offset radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1) ↦
      Fin (data.orderedCluster c).card

/-- All simultaneous centers as one finite dependent family. -/
def simultaneousPostLogScaleFamily
    (cri : boundary.SimultaneousJetIndex D representative offset radius Fsys x
      w₀ hw₀ data) (n : ℕ) : ℝ :=
  boundary.simultaneousNumericPostLogScale D representative offset radius Fsys
    x w₀ hw₀ data cri.1 cri.2.1.val cri.2.2 n

/-- Every member of the dependent simultaneous family diverges. -/
theorem simultaneousPostLogScaleFamily_tendsto_atTop
    (hA : IsAbel A)
    (cri : boundary.SimultaneousJetIndex D representative offset radius Fsys x
      w₀ hw₀ data) :
    Tendsto (boundary.simultaneousPostLogScaleFamily D representative offset
      radius Fsys x w₀ hw₀ data cri) atTop atTop := by
  exact boundary.simultaneousNumericPostLogScale_tendsto_atTop D representative
    offset radius Fsys x w₀ hw₀ data hA cri.1 cri.2.1.val cri.2.2

/-- The simultaneous center family after the already chosen global
individual tail. -/
def simultaneousPostLogScaleFamilyAfterIndividualTail
    (hA : IsAbel A)
    (cri : boundary.SimultaneousJetIndex D representative offset radius Fsys x
      w₀ hw₀ data) (n : ℕ) : ℝ :=
  boundary.simultaneousPostLogScaleFamily D representative offset radius Fsys x
    w₀ hw₀ data cri
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)

/-- Discarding the individual tail preserves divergence of every
simultaneous center. -/
theorem simultaneousPostLogScaleFamilyAfterIndividualTail_tendsto_atTop
    (hA : IsAbel A)
    (cri : boundary.SimultaneousJetIndex D representative offset radius Fsys x
      w₀ hw₀ data) :
    Tendsto
      (boundary.simultaneousPostLogScaleFamilyAfterIndividualTail D
        representative offset radius Fsys x w₀ hw₀ data hA cri)
      atTop atTop := by
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let reindex : ℕ → ℕ := fun n ↦ n + Ntail
  have hreindex : Tendsto reindex atTop atTop := by
    simpa only [reindex, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  exact (boundary.simultaneousPostLogScaleFamily_tendsto_atTop D representative
    offset radius Fsys x w₀ hw₀ data hA cri).comp hreindex

/-- One further finite tail puts every simultaneous Hermite center beyond
the common real-Hermite threshold, after the global individual tail. -/
theorem exists_simultaneousQuantitativeTail (hA : IsAbel A) :
    ∃ N : ℕ, ∀ n
      (cri : boundary.SimultaneousJetIndex D representative offset radius Fsys
        x w₀ hw₀ data),
      (boundary.commonRealHermiteData D representative offset radius Fsys x
          w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScaleFamily D representative offset radius
          Fsys x w₀ hw₀ data cri
          ((n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA) + N) := by
  obtain ⟨N, hN⟩ := exists_uniform_nat_tail_gt
    (boundary.simultaneousPostLogScaleFamilyAfterIndividualTail D
      representative offset radius Fsys x w₀ hw₀ data hA)
    (boundary.simultaneousPostLogScaleFamilyAfterIndividualTail_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA)
    (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
      hw₀ data hA).u0
  refine ⟨N, ?_⟩
  intro n cri
  have h := hN n cri
  simpa only [simultaneousPostLogScaleFamilyAfterIndividualTail,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Chosen additional simultaneous tail, uniform over every cluster,
operation, and active block. -/
def simultaneousQuantitativeTail (hA : IsAbel A) : ℕ :=
  Classical.choose (boundary.exists_simultaneousQuantitativeTail D
    representative offset radius Fsys x w₀ hw₀ data hA)

/-- The selected index shared by all simultaneous quantitative data. -/
def simultaneousQuantitativeReindex (hA : IsAbel A) (n : ℕ) : ℕ :=
  (n + boundary.individualQuantitativeTail D representative offset radius Fsys
    x w₀ hw₀ data hA) +
      boundary.simultaneousQuantitativeTail D representative offset radius Fsys
        x w₀ hw₀ data hA

/-- The shared simultaneous reindexing is cofinal. -/
theorem simultaneousQuantitativeReindex_tendsto_atTop (hA : IsAbel A) :
    Tendsto (boundary.simultaneousQuantitativeReindex D representative offset
      radius Fsys x w₀ hw₀ data hA) atTop atTop := by
  let N := boundary.individualQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA +
    boundary.simultaneousQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA
  unfold simultaneousQuantitativeReindex
  simpa only [Nat.add_assoc, N] using tendsto_add_atTop_nat N

/-- Every center at the selected simultaneous index exceeds the Hermite
threshold, with no threshold premise left to downstream segment data. -/
theorem simultaneousQuantitativePostLogScale_gt
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
        hw₀ data hA).u0 <
      boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r.val i
        (boundary.simultaneousQuantitativeReindex D representative offset
          radius Fsys x w₀ hw₀ data hA n) := by
  exact Classical.choose_spec
    (boundary.exists_simultaneousQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA) n ⟨c, r, i⟩

/-- Raw times of a cluster on the common individual-plus-simultaneous tail. -/
def simultaneousQuantitativeRawTime
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ :=
  fun n ↦ boundary.simultaneousNumericRawTime D representative offset radius
    Fsys x w₀ hw₀ data c
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)

/-- Post-log centers on the common quantitative tail. -/
abbrev simultaneousQuantitativePostLogScale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :=
  data.orderedClusterSimultaneousPostLogScale c A
    (boundary.simultaneousQuantitativeRawTime D representative offset radius
      Fsys x w₀ hw₀ data hA c)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c) r

/-- Boundary scales on the common quantitative tail. -/
abbrev simultaneousQuantitativeBoundaryScale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :=
  data.orderedClusterSimultaneousBoundaryScale c A
    (boundary.simultaneousQuantitativeRawTime D representative offset radius
      Fsys x w₀ hw₀ data hA c)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c) r

/-! ## Op-sensitive real jets on an arbitrary cofinal reindexing -/

/-- Pull the selected raw-time vector back along an arbitrary index map. -/
def simultaneousReindexedRawTime
    (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) :
    ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ :=
  fun n ↦ boundary.simultaneousNumericRawTime D representative offset radius
    Fsys x w₀ hw₀ data c (φ n)

/-- Simultaneous post-log centers after an arbitrary reindexing. -/
abbrev simultaneousReindexedPostLogScale
    (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ) :=
  data.orderedClusterSimultaneousPostLogScale c A
    (boundary.simultaneousReindexedRawTime D representative offset radius Fsys
      x w₀ hw₀ data c φ)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c) r

/-- Simultaneous boundary scales after an arbitrary reindexing. -/
abbrev simultaneousReindexedBoundaryScale
    (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ) :=
  data.orderedClusterSimultaneousBoundaryScale c A
    (boundary.simultaneousReindexedRawTime D representative offset radius Fsys
      x w₀ hw₀ data c φ)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c) r

theorem simultaneousReindexedPostLogScale_apply
    (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    boundary.simultaneousReindexedPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c φ r i n =
      boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r i (φ n) :=
  rfl

/-- Fresh Hermite jets on a reindexed simultaneous center sequence.  This is
the primitive used only for blocks untouched by the individual balancing
list at the first simultaneous operation. -/
def simultaneousReindexedFreshRealJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousReindexedPostLogScale D representative offset
        radius Fsys x w₀ hw₀ data c φ r i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i) := by
  intro n i
  exact castRealCentralJetSubstitutionData
    ((boundary.commonRealHermiteData D representative offset radius Fsys x w₀
      hw₀ data hA).fullHermite.paperRankRealJetSequence
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
        (boundary.simultaneousSelectedBlock D representative offset radius Fsys
          x w₀ hw₀ data c)
        (boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r) hu
        (fun q ↦ (boundary.selectedTranslatedParameter D representative offset
          radius Fsys x w₀ hw₀ data (φ q)).2)
        (fun q k ↦ boundary.selectedTranslatedOffset_bound D representative
          offset radius Fsys x w₀ hw₀ data (φ q) k) n i)
    rfl
    (by
      simpa only [terminalTotalDerivativeCount] using
        (paperRankHermiteHigherCount_add_one boundary.S).symm)

/-- A final-order active block was already converted to exact derivatives by
the individual segment precisely when its original balancing coordinate
occurs in the fixed step list. -/
def simultaneousBlockTouchedByIndividualSteps
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedCluster c).card) : Prop :=
  boundary.preprocessed.fixedOrder c
      ((data.orderedClusterBalancingToActiveEquiv c).symm i) ∈
    boundary.preprocessed.fixedSteps c

/-- Op-sensitive simultaneous jets after an arbitrary reindexing.  Operation
zero uses the recursively mixed individual terminal state: touched blocks
are exact and untouched blocks retain their Hermite jets.  Every positive
operation uses exact derivatives in all blocks. -/
def simultaneousReindexedOperationJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousReindexedPostLogScale D representative offset
        radius Fsys x w₀ hw₀ data c φ r i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i) := by
  intro n i
  by_cases hr : r = 0
  · by_cases htouched : boundary.simultaneousBlockTouchedByIndividualSteps D
        representative offset radius Fsys x w₀ hw₀ data c i
    · exact hA.realDerivativeJetSubstitutionData (hA.inverse_pos _)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S) i)
    · exact boundary.simultaneousReindexedFreshRealJetSequence D representative
        offset radius Fsys x w₀ hw₀ data hA c φ r hu n i
  · exact hA.realDerivativeJetSubstitutionData (hA.inverse_pos _)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i)

/-- The op-sensitive jet family on the automatically chosen common tail. -/
def simultaneousQuantitativeOperationJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r.val i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i) :=
  boundary.simultaneousReindexedOperationJetSequence D representative offset
    radius Fsys x w₀ hw₀ data hA c
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA) r.val
    (fun n i ↦ boundary.simultaneousQuantitativePostLogScale_gt D
      representative offset radius Fsys x w₀ hw₀ data hA c r i n)

/-- At every positive simultaneous operation, the source coordinates are
literal derivatives at the pre-log point. -/
theorem simultaneousReindexedOperationJetSequence_sourceJet_of_pos
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (hr : 0 < r)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n)
    (n : ℕ) (i : Fin (data.orderedCluster c).card)
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)) :
    (boundary.simultaneousReindexedOperationJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c φ r hu n i).sourceJet q =
      iteratedDeriv (q.val + 1) A
        (E (boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n)) := by
  simp [simultaneousReindexedOperationJetSequence, ne_of_gt hr]
  unfold simultaneousReindexedPostLogScale
    RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale
  push_cast
  rfl

/-- At the first operation, every block touched by the individual balancing
list already carries exact derivative coordinates. -/
theorem simultaneousReindexedOperationJetSequence_first_sourceJet_of_touched
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ 0 i n)
    (n : ℕ) (i : Fin (data.orderedCluster c).card)
    (htouched : boundary.simultaneousBlockTouchedByIndividualSteps D
      representative offset radius Fsys x w₀ hw₀ data c i)
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)) :
    (boundary.simultaneousReindexedOperationJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c φ 0 hu n i).sourceJet q =
      iteratedDeriv (q.val + 1) A
        (E (boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ 0 i n)) := by
  simp [simultaneousReindexedOperationJetSequence, htouched]

/-- At the first operation, an untouched block retains the corresponding
fresh Hermite source coordinate. -/
theorem simultaneousReindexedOperationJetSequence_first_eq_fresh_of_untouched
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ 0 i n)
    (n : ℕ) (i : Fin (data.orderedCluster c).card)
    (htouched : ¬ boundary.simultaneousBlockTouchedByIndividualSteps D
      representative offset radius Fsys x w₀ hw₀ data c i) :
    boundary.simultaneousReindexedOperationJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c φ 0 hu n i =
      boundary.simultaneousReindexedFreshRealJetSequence D representative
        offset radius Fsys x w₀ hw₀ data hA c φ 0 hu n i := by
  simp [simultaneousReindexedOperationJetSequence, htouched]

/-- Positive simultaneous operations have identically zero jet error. -/
theorem simultaneousReindexedOperationJetSequence_error_of_pos
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (hr : 0 < r)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n)
    (n : ℕ) (i : Fin (data.orderedCluster c).card)
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)) :
    (boundary.simultaneousReindexedOperationJetSequence D representative offset
      radius Fsys x w₀ hw₀ data hA c φ r hu n i).error q = 0 := by
  simp [simultaneousReindexedOperationJetSequence, ne_of_gt hr]

/-- Balancing and separation estimates survive every cofinal reindexing of
the selected simultaneous sequence. -/
theorem simultaneousReindexedTransferHierarchies
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (r : ℕ)
    (hN : (((r + 6 : ℕ) : ℝ)) ≤ separation.N c) :
    FiniteRealJetTransferHierarchies (data.orderedCluster c).card
      (boundary.simultaneousReindexedPostLogScale D representative offset
        radius Fsys x w₀ hw₀ data c φ r)
      (boundary.simultaneousReindexedBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data c φ (r + 1))
      (boundary.simultaneousReindexedBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data c φ r) := by
  exact hA.orderedClusterSimultaneousStep_transferHierarchies data c
    (boundary.simultaneousReindexedRawTime D representative offset radius Fsys
      x w₀ hw₀ data c φ)
    (fun n ↦ data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence (φ n)))
    (fun n ↦ boundary.preprocessed.plans (φ n) c)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c)
    (fun n ↦ boundary.preprocessed.plans_steps (φ n) c)
    (fun n ↦ boundary.preprocessed.plans_finalOrder (φ n) c) r
    (separation.separationConstant_pos c) hN
    ((boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c).comp hφ)
    (hφ.eventually (separation.separated c))

/-- The fresh reindexed Hermite error obeys the same superpolynomial estimate
as the unshifted construction. -/
theorem simultaneousReindexedFreshRealJetSequence_error_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n)
    (R : ℕ → ℝ) {tail : ℕ}
    (card_eq : tail + 1 = (data.orderedCluster c).card)
    (hierarchy : BalancedRealJetTransferHierarchy tail
      (fun i n ↦ boundary.simultaneousReindexedPostLogScale D representative
        offset radius Fsys x w₀ hw₀ data c φ r (finCongr card_eq i) n) R)
    (i : Fin (data.orderedCluster c).card)
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.simultaneousReindexedFreshRealJetSequence D
        representative offset radius Fsys x w₀ hw₀ data hA c φ r hu n i).error q) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  let q' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
    Fin.cast (paperRankHermiteHigherCount_add_one boundary.S) q
  have hseparated : ∀ k, Tendsto
      (fun n ↦ boundary.simultaneousReindexedPostLogScale D representative
        offset radius Fsys x w₀ hw₀ data c φ r k n / Real.log (R n))
      atTop atTop := by
    intro k
    let k' : Fin (tail + 1) := (finCongr card_eq).symm k
    have hk := tendsto_scaleCoordinate_div_log_atTop_of_strictAnti
      (fun q n ↦ boundary.simultaneousReindexedPostLogScale D representative
        offset radius Fsys x w₀ hw₀ data c φ r (finCongr card_eq q) n)
      R hierarchy.order hierarchy.scale_ge_two
      hierarchy.smallest_div_log_scale k'
    simpa only [k', Equiv.apply_symm_apply] using hk
  have herror := H.paperRankRealJetSequence_error_superpolynomialDecay
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
    (boundary.simultaneousSelectedBlock D representative offset radius Fsys x
      w₀ hw₀ data c)
    (boundary.simultaneousReindexedPostLogScale D representative offset radius
      Fsys x w₀ hw₀ data c φ r) hu
    (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data (φ n)).2)
    (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative offset
      radius Fsys x w₀ hw₀ data (φ n) k)
    R hierarchy.scale_ge_two hseparated i q'
  apply herror.congr
  intro n
  simp [simultaneousReindexedFreshRealJetSequence, q']

/-- The op-sensitive mixed/exact jet family has superpolynomial error: only
untouched blocks at operation zero invoke the Hermite estimate. -/
theorem simultaneousReindexedOperationJetSequence_error_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (φ : ℕ → ℕ) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ r i n)
    (R : ℕ → ℝ) {tail : ℕ}
    (card_eq : tail + 1 = (data.orderedCluster c).card)
    (hierarchy : BalancedRealJetTransferHierarchy tail
      (fun i n ↦ boundary.simultaneousReindexedPostLogScale D representative
        offset radius Fsys x w₀ hw₀ data c φ r (finCongr card_eq i) n) R)
    (i : Fin (data.orderedCluster c).card)
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.simultaneousReindexedOperationJetSequence D
        representative offset radius Fsys x w₀ hw₀ data hA c φ r hu n i).error q) := by
  by_cases hr : r = 0
  · subst r
    by_cases htouched : boundary.simultaneousBlockTouchedByIndividualSteps D
        representative offset radius Fsys x w₀ hw₀ data c i
    · apply (Asymptotics.superpolynomialDecay_zero atTop R).congr
      intro n
      simp [simultaneousReindexedOperationJetSequence, htouched]
    · have herror :=
        boundary.simultaneousReindexedFreshRealJetSequence_error_superpolynomialDecay_of_hierarchy
          D representative offset radius Fsys x w₀ hw₀ data hA c φ 0 hu R
          card_eq hierarchy i q
      apply herror.congr
      intro n
      simp [simultaneousReindexedOperationJetSequence, htouched]
  · apply (Asymptotics.superpolynomialDecay_zero atTop R).congr
    intro n
    simp [simultaneousReindexedOperationJetSequence, hr]

/-! ## Concrete finite coefficients on the common tail -/

/-- The canonical support-local source coefficient values pulled back along
the common individual-plus-simultaneous tail. -/
def simultaneousQuantitativeSourceCoefficientValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (n : ℕ) : ℝ :=
  boundary.simultaneousSourceCoefficientValue D representative offset radius
    Fsys x w₀ hw₀ data c r coefficients q e
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)

/-- Analyticity bounds every supported canonical coefficient on the common
tail from bounds for the reindexed smaller-prefix symbols. -/
theorem simultaneousQuantitativeSourceCoefficientValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (hscale : ∀ᶠ n in atTop,
      1 ≤ boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1) n)
    (hsmaller : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (fun n ↦ boundary.simultaneousSmallerPrefixSequenceValue D representative
        offset radius Fsys x w₀ hw₀ data c r.val z
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n)))
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (he : e ∈ (((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q).support) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (boundary.simultaneousQuantitativeSourceCoefficientValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r coefficients q e) := by
  let φ := boundary.simultaneousQuantitativeReindex D representative offset
    radius Fsys x w₀ hw₀ data hA
  let scale := boundary.simultaneousQuantitativeBoundaryScale D representative
    offset radius Fsys x w₀ hw₀ data hA c (r.val + 1)
  refine (coefficients.polynomialValueAlong_hasPolynomialUpperBound
    (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data (φ n)).2)
    ((boundary.selectedTranslatedParameter_box_tendsto_zero D representative
      offset radius Fsys x w₀ hw₀ data).comp
        (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
          offset radius Fsys x w₀ hw₀ data hA))
    (fun z n ↦ boundary.simultaneousSmallerPrefixSequenceValue D representative
      offset radius Fsys x w₀ hw₀ data c r.val z (φ n))
    scale hscale hsmaller ⟨q, ⟨e, he⟩⟩).congr ?_
  intro n
  rw [simultaneousQuantitativeSourceCoefficientValue,
    simultaneousSourceCoefficientValue, dite_eq_left he]
  rfl

/-! ## One-step numeric data on the common tail -/

/-- The two finite evaluated changes of generators around one op-sensitive
simultaneous step on the common quantitative tail.  The threshold premise of
the unshifted record is absent: it is discharged by
`simultaneousQuantitativePostLogScale_gt`. -/
structure SimultaneousQuantitativeFiniteAnalyticChangeData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r) where
  afterValue : Fin (((boundary.simultaneousNumericTrace D representative
    offset radius Fsys x w₀ hw₀ data c).simultaneousDisplayed r).central.count + 1) →
      ℕ → ℝ
  centralCoefficient :
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed r).central.count + 1) →
    Fin ((boundary.simultaneousNumericTrace D representative offset radius Fsys
      x w₀ hw₀ data c).simultaneous.transferCertificate r).count → ℕ → ℝ
  beforeValue : Fin (((boundary.simultaneousNumericTrace D representative
    offset radius Fsys x w₀ hw₀ data c).simultaneousDisplayed r).source.count + 1) →
      ℕ → ℝ
  sourceCoefficient :
    Fin ((boundary.simultaneousNumericTrace D representative offset radius Fsys
      x w₀ hw₀ data c).simultaneous.transferCertificate r).count →
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed r).source.count + 1) →
      ℕ → ℝ
  central_identity : ∀ᶠ n in atTop, ∀ b,
    afterValue b n =
      ∑ q, centralCoefficient b q n *
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
          A
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q) n
  central_coefficient_bound : ∀ b q,
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (centralCoefficient b q)
  source_identity : ∀ᶠ n in atTop, ∀ q,
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (boundary.simultaneousQuantitativeOperationJetSequence D
            representative offset radius Fsys x w₀ hw₀ data hA c r)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q) n =
      ∑ k, sourceCoefficient q k n * beforeValue k n
  source_coefficient_bound : ∀ q k,
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r.val)
      (sourceCoefficient q k)

/-- The generic numeric one-step package at the common quantitative tail. -/
abbrev HermiteSimultaneousQuantitativeNumericData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :=
  RepresentativeClusterSubsequence.OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData.SimultaneousNumericQuantitativeData
    (boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c) A
    (boundary.simultaneousQuantitativeRawTime D representative offset radius
      Fsys x w₀ hw₀ data hA c) r

/-- Construct one op-sensitive simultaneous numeric step on the common tail.
The balancing hierarchy, threshold, support-local coefficient bounds, and
mixed/exact jet decay are all derived internally. -/
noncomputable def hermiteSimultaneousQuantitativeNumericData
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (hN : (((r.val + 6 : ℕ) : ℝ)) ≤ separation.N c)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (hsmaller : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (fun n ↦ boundary.simultaneousSmallerPrefixSequenceValue D representative
        offset radius Fsys x w₀ hw₀ data c r.val z
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n)))
    (hmain : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (finiteRealJetMainAssignment A
        (boundary.simultaneousQuantitativePostLogScale D representative offset
          radius Fsys x w₀ hw₀ data hA c r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S)) z))
    (change : boundary.SimultaneousQuantitativeFiniteAnalyticChangeData D
      representative offset radius Fsys x w₀ hw₀ data hA c r coefficients) :
    boundary.HermiteSimultaneousQuantitativeNumericData D representative offset
      radius Fsys x w₀ hw₀ data hA c r := by
  let φ := boundary.simultaneousQuantitativeReindex D representative offset
    radius Fsys x w₀ hw₀ data hA
  let hierarchies := boundary.simultaneousReindexedTransferHierarchies D
    representative offset radius Fsys x w₀ hw₀ data separation hA c φ
    (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA) r.val hN
  have hscale : ∀ᶠ n in atTop,
      1 ≤ boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1) n :=
    hierarchies.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  refine {
    coefficientValue := boundary.simultaneousQuantitativeSourceCoefficientValue
      D representative offset radius Fsys x w₀ hw₀ data hA c r coefficients
    jets := boundary.simultaneousQuantitativeOperationJetSequence D
      representative offset radius Fsys x w₀ hw₀ data hA c r
    afterValue := change.afterValue
    centralCoefficient := change.centralCoefficient
    beforeValue := change.beforeValue
    sourceCoefficient := change.sourceCoefficient
    coefficient_bound := ?_
    main_bound := hmain
    jet_error := ?_
    central_identity := change.central_identity
    central_coefficient_bound := change.central_coefficient_bound
    source_identity := change.source_identity
    source_coefficient_bound := change.source_coefficient_bound
  }
  · intro q e he
    exact boundary.simultaneousQuantitativeSourceCoefficientValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c r coefficients
      hscale hsmaller q e he
  · intro i q
    rcases hierarchies with ⟨tail, card_eq, hierarchy, _domination⟩
    exact boundary.simultaneousReindexedOperationJetSequence_error_superpolynomialDecay_of_hierarchy
      D representative offset radius Fsys x w₀ hw₀ data hA c φ r.val
      (fun n i ↦ boundary.simultaneousQuantitativePostLogScale_gt D
        representative offset radius Fsys x w₀ hw₀ data hA c r i n)
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1)) card_eq hierarchy i q

/-! ## Finite reverse segment on the common tail -/

/-- Finite analytic data for the complete op-sensitive simultaneous segment
on the automatically chosen common tail.  There is no `hu` field: the common
tail proves the Hermite threshold for every operation and coordinate. -/
structure SimultaneousQuantitativeFiniteAnalyticSegmentData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) where
  coefficients :
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
      boundary.SimultaneousSourceCoefficientData D representative offset radius
        Fsys x w₀ hw₀ data c r
  smaller_bound :
    ∀ (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (fun n ↦ boundary.simultaneousSmallerPrefixSequenceValue D
          representative offset radius Fsys x w₀ hw₀ data c r.val z
            (boundary.simultaneousQuantitativeReindex D representative offset
              radius Fsys x w₀ hw₀ data hA n))
  main_bound :
    ∀ (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (finiteRealJetMainAssignment A
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S)) z)
  change :
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
      boundary.SimultaneousQuantitativeFiniteAnalyticChangeData D representative
        offset radius Fsys x w₀ hw₀ data hA c r (coefficients r)
  adjacentCoefficient :
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) →
      Fin (((boundary.simultaneousNumericTrace D representative offset radius
        Fsys x w₀ hw₀ data c).simultaneousDisplayed i.succ).source.count + 1) →
      Fin (((boundary.simultaneousNumericTrace D representative offset radius
        Fsys x w₀ hw₀ data c).simultaneousDisplayed i.castSucc).central.count + 1) →
        ℕ → ℝ
  adjacent_coefficient_bound : ∀ i k b,
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (i.val + 1))
      (adjacentCoefficient i k b)
  adjacent_identity : ∀ i, ∀ᶠ n in atTop, ∀ k,
    (change i.succ).beforeValue k n =
      ∑ b, adjacentCoefficient i k b n *
        (change i.castSucc).afterValue b n

/-- Generic numeric segment data specialized to the shared common tail. -/
abbrev HermiteSimultaneousQuantitativeNumericSegmentData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :=
  RepresentativeClusterSubsequence.OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData.SimultaneousNumericSegmentQuantitativeData
    (boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c) A
    (boundary.simultaneousQuantitativeRawTime D representative offset radius
      Fsys x w₀ hw₀ data hA c)

/-- Assemble the complete op-sensitive numeric segment on the common tail.
The construction handles zero extra retained operations through the same
dependent finite family. -/
noncomputable def hermiteSimultaneousQuantitativeNumericSegmentData
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hN : (((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ) ≤
        separation.N c)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA c) :
    boundary.HermiteSimultaneousQuantitativeNumericSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA c := by
  let step :
      (r : Fin ((boundary.simultaneousNumericStage D representative offset
        radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
        boundary.HermiteSimultaneousQuantitativeNumericData D representative
          offset radius Fsys x w₀ hw₀ data hA c r := fun r ↦
    boundary.hermiteSimultaneousQuantitativeNumericData D representative offset
      radius Fsys x w₀ hw₀ data separation hA c r (by
        calc
          ((r.val + 6 : ℕ) : ℝ) ≤
              (((boundary.simultaneousNumericStage D representative offset
                radius Fsys x w₀ hw₀ data
                c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ) := by
            exact_mod_cast Nat.add_le_add_right
              (Nat.le_of_lt_succ r.isLt) 6
          _ ≤ separation.N c := hN)
      (segment.coefficients r) (segment.smaller_bound r)
      (segment.main_bound r) (segment.change r)
  refine {
    step := step
    adjacentCoefficient := segment.adjacentCoefficient
    adjacent_coefficient_bound := segment.adjacent_coefficient_bound
    adjacent_identity := ?_
  }
  intro i
  simpa only [step, hermiteSimultaneousQuantitativeNumericData] using
    segment.adjacent_identity i

/-- Propagate a terminal lower bound backwards through every simultaneous
operation on the common individual-plus-simultaneous tail.  This includes
the first mixed operation and every later exact operation, and also covers
`extraSteps = 0`. -/
theorem hermiteSimultaneousQuantitativeFirstBeforeValue_lower_of_terminalAfterValue_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hN : (((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ) ≤
        separation.N c)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA c)
    (hterminal : HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
      (segment.change (Fin.last
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps)).afterValue) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      (segment.change
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue := by
  let φ := boundary.simultaneousQuantitativeReindex D representative offset
    radius Fsys x w₀ hw₀ data hA
  let numeric := boundary.hermiteSimultaneousQuantitativeNumericSegmentData D
    representative offset radius Fsys x w₀ hw₀ data separation hA c hN segment
  have hterminal' : HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
      (numeric.step (Fin.last
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps)).afterValue := by
    simpa only [numeric, hermiteSimultaneousQuantitativeNumericSegmentData,
      hermiteSimultaneousQuantitativeNumericData] using hterminal
  have hresult := (boundary.simultaneousNumericTrace D representative offset
    radius Fsys x w₀ hw₀ data c).firstBeforeValue_lower_of_terminalAfterValue_lower_numeric
      hA
      (boundary.simultaneousQuantitativeRawTime D representative offset radius
        Fsys x w₀ hw₀ data hA c)
      (fun n ↦ data.orderedClusterMinTime c
        (boundary.preprocessed.balancingSubsequence (φ n)))
      (fun n ↦ boundary.preprocessed.plans (φ n) c)
      (fun n ↦ boundary.preprocessed.plans_steps (φ n) c)
      (fun n ↦ boundary.preprocessed.plans_finalOrder (φ n) c)
      (separation.separationConstant_pos c) hN
      ((boundary.selectedClusterMinTime_tendsto_atTop D representative offset
        radius Fsys x w₀ hw₀ data hA c).comp
          (boundary.simultaneousQuantitativeReindex_tendsto_atTop D
            representative offset radius Fsys x w₀ hw₀ data hA))
      ((boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA).eventually
          (separation.separated c)) numeric hterminal'
  simpa only [numeric, hermiteSimultaneousQuantitativeNumericSegmentData,
    hermiteSimultaneousQuantitativeNumericData] using hresult

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
