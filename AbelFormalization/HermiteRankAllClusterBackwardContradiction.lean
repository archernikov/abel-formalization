import AbelFormalization.HermiteRankBottomTerminalSimultaneousCompatibility
import AbelFormalization.HermiteRankPreprocessedIndividualAnalyticData
import AbelFormalization.HermiteRankIndividualSimultaneousFiniteFamilyCompatibility
import AbelFormalization.HermiteRankNonbottomClusterCanonicalCompatibility
import AbelFormalization.HermiteRankTopIndividualBoundaryCompatibility

/-!
# Backward propagation through every ordered Hermite cluster

The recovered quantitative modules now provide all finite analytic data and
all representative comparisons canonically.  This module composes them.  A
localized bottom lower bound is propagated through cluster zero, then across
each adjacent cluster boundary and backwards through the next simultaneous
and individual segments.  At the highest cluster the resulting boundary-zero
lower bound contradicts the vanishing selected padded top-prefix family.

The general theorem retains only the numerical simultaneous margin required
by the separation estimates.  For the diagonal boundary that margin is
automatic, so the final diagonal theorem has no compatibility or analytic
data premises.
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

/-! ## Canonical one-cluster and bottom inputs -/

/-- Canonical Noetherian terminal localization for the last displayed step
of ordered cluster zero. -/
noncomputable def bottomTerminalLocalizationData :
    boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData :=
  Classical.choice
    boundary.preprocessed.bottomLastDisplayed.nonempty_terminalLocalizationData

/-- The one-cluster theorem with its individual analytic trace,
simultaneous analytic segment, and intervening finite-family seam filled by
their canonical constructors. -/
theorem individualMixedInitialBoundary_lower_of_terminalSimultaneous_lower_auto
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hN : (((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ) ≤
        separation.N c)
    (hterminal : HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
      (((boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA c).change
        (Fin.last
          (boundary.simultaneousNumericStage D representative offset radius
            Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps)).afterValue)) :
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0) := by
  exact
    boundary.individualMixedInitialBoundary_lower_of_terminalSimultaneous_lower
      D representative offset radius Fsys x w₀ hw₀ data separation hA c hN
      (boundary.individualMixedFiniteAnalyticTraceData D representative offset
        radius Fsys x w₀ hw₀ data hA c)
      (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA c)
      (boundary.individualSimultaneousFiniteFamilyCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c)
      hterminal

/-- The canonical bottom localization and simultaneous analytic segment give
the first simultaneous before-family lower bound without any representative
compatibility input. -/
theorem bottomSimultaneousQuantitativeFirstBeforeValue_lower_canonical
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hN : (((boundary.bottomTerminalExtraSteps D representative offset radius
      Fsys x w₀ hw₀ data + 6 : ℕ) : ℝ)) ≤
        separation.N (bottomTerminalCluster x data)) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data) 0)
      (((boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA
          (bottomTerminalCluster x data)).change
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.firstCentralStepIndex).beforeValue) := by
  exact boundary.bottomSimultaneousQuantitativeFirstBeforeValue_lower_auto D
    representative offset radius Fsys x w₀ hw₀ data separation hA hN
    (boundary.bottomTerminalLocalizationData D representative offset radius Fsys
      x w₀ hw₀ data)

/-- The fully canonical bottom seed, followed by all simultaneous and
individual steps of ordered cluster zero. -/
theorem bottomClusterIndividualMixedInitialBoundary_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hN : (((boundary.bottomTerminalExtraSteps D representative offset radius
      Fsys x w₀ hw₀ data + 6 : ℕ) : ℝ)) ≤
        separation.N (bottomTerminalCluster x data)) :
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data) 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data) 0) := by
  apply
    boundary.individualMixedInitialBoundary_lower_of_terminalSimultaneous_lower_auto
      D representative offset radius Fsys x w₀ hw₀ data separation hA
      (bottomTerminalCluster x data) hN
  exact boundary.bottomSimultaneousQuantitativeTerminalAfterValue_lower_auto D
    representative offset radius Fsys x w₀ hw₀ data hA
    (boundary.bottomTerminalLocalizationData D representative offset radius Fsys
      x w₀ hw₀ data)

/-! ## Adjacent-cluster propagation -/

/-- Cross one nonbottom terminal seam and then propagate backwards through
the upper cluster's simultaneous and individual segments. -/
theorem nextClusterIndividualMixedInitialBoundary_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (hN : ((((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
        data c hc)).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ)) ≤
        separation.N
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc))
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc) 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc) 0) := by
  apply
    boundary.individualMixedInitialBoundary_lower_of_terminalSimultaneous_lower_auto
      D representative offset radius Fsys x w₀ hw₀ data separation hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
        data c hc) hN
  have hterminal :=
    boundary.nextTerminalSimultaneousAfter_lower_of_individualMixedInitial_lower_auto
      D representative offset radius Fsys x w₀ hw₀ data hA c hc hincoming
  simpa only [nextTerminalScale, nextTerminalExtraSteps,
    nextTerminalOperation] using hterminal

/-! ## Finite propagation and the top contradiction -/

/-- The highest ordered cluster, defined using positivity of the ordered
cluster count. -/
def topOrderedCluster
    (_boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
      D representative offset radius Fsys x w₀ hw₀ data) :
    Fin data.orderedClusterCount :=
  ⟨data.orderedClusterCount - 1, by
    have hcount := data.orderedClusterCount_pos_of_nonempty
    omega⟩

/-- The canonical highest cluster has the terminal index equation consumed
by the top-prefix contradiction. -/
@[simp]
theorem topOrderedCluster_val_add_one :
    (boundary.topOrderedCluster D representative offset radius Fsys x w₀ hw₀
        data).val + 1 = data.orderedClusterCount := by
  unfold topOrderedCluster
  simp only [Fin.val_mk]
  have hcount := data.orderedClusterCount_pos_of_nonempty
  omega

/-- The bottom seed propagates to the boundary-zero family of every ordered
cluster.  All finite analytic data and all inter-family comparisons are
constructed internally. -/
theorem individualMixedInitialBoundary_lower_all_clusters
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hmargin : ∀ c : Fin data.orderedClusterCount,
      ((((boundary.simultaneousNumericStage D representative offset radius Fsys
        x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ)) ≤
          separation.N c) :
    ∀ c : Fin data.orderedClusterCount,
      HasInversePowerLowerBound atTop
        (boundary.individualMixedBoundaryScaleOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c 0)
        (boundary.individualMixedBoundaryValueOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c 0) := by
  let P : Fin data.orderedClusterCount → Prop := fun c ↦
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
  have hzero : P (bottomTerminalCluster x data) := by
    exact boundary.bottomClusterIndividualMixedInitialBoundary_lower D
      representative offset radius Fsys x w₀ hw₀ data separation hA
      (hmargin (bottomTerminalCluster x data))
  have hindex : ∀ k (hk : k < data.orderedClusterCount), P ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        have heq : (⟨0, hk⟩ : Fin data.orderedClusterCount) =
            bottomTerminalCluster x data := Fin.ext rfl
        rw [heq]
        exact hzero
    | succ k ih =>
        intro hk
        have hkprev : k < data.orderedClusterCount :=
          Nat.lt_trans (Nat.lt_succ_self k) hk
        let prev : Fin data.orderedClusterCount := ⟨k, hkprev⟩
        have hc : prev.val + 1 < data.orderedClusterCount := by
          simpa only [prev, Nat.succ_eq_add_one] using hk
        have hprev : P prev := ih hkprev
        have hnext :
            P (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data prev hc) := by
          exact boundary.nextClusterIndividualMixedInitialBoundary_lower D
            representative offset radius Fsys x w₀ hw₀ data separation hA prev
            hc
            (hmargin
              (boundary.nextOrderedCluster D representative offset radius Fsys
                x w₀ hw₀ data prev hc))
            hprev
        have heq :
            boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data prev hc =
              (⟨Nat.succ k, hk⟩ : Fin data.orderedClusterCount) :=
          Fin.ext (by simp only [nextOrderedCluster, prev, Nat.succ_eq_add_one])
        rw [← heq]
        exact hnext
  intro c
  have hc := hindex c.val c.isLt
  have heq : (⟨c.val, c.isLt⟩ : Fin data.orderedClusterCount) = c :=
    Fin.ext rfl
  rw [heq] at hc
  exact hc

/-- Backward propagation through every ordered cluster contradicts the
vanishing selected padded top-prefix family.  The only explicit quantitative
input is the simultaneous margin at each cluster. -/
theorem false_of_allClusterBackwardPropagation
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hmargin : ∀ c : Fin data.orderedClusterCount,
      ((((boundary.simultaneousNumericStage D representative offset radius Fsys
        x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ)) ≤
          separation.N c) :
    False := by
  let top := boundary.topOrderedCluster D representative offset radius Fsys x
    w₀ hw₀ data
  apply boundary.false_of_topIndividualBoundaryZero_lower_auto D representative
    offset radius Fsys x w₀ hw₀ data hA top
  · exact boundary.topOrderedCluster_val_add_one D representative offset radius
      Fsys x w₀ hw₀ data
  · exact boundary.individualMixedInitialBoundary_lower_all_clusters D
      representative offset radius Fsys x w₀ hw₀ data separation hA hmargin top

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

/-! ## Diagonal specialization -/

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

include diagonal

/-- The diagonal boundary supplies its separation record and every required
simultaneous margin canonically, so the completed backward chain is an
unconditional contradiction. -/
theorem false_of_canonicalBackwardPropagation : False := by
  apply
    RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary.false_of_allClusterBackwardPropagation
      (boundary := diagonal.boundary) D representative offset radius Fsys
    (diagonal.ambientSequence hA D representative offset radius Fsys x w₀ hw₀
      data)
    w₀ hw₀
    (diagonal.clusterData hA D representative offset radius Fsys x w₀ hw₀ data)
    (diagonal.separation hA D representative offset radius Fsys x w₀ hw₀ data)
    hA
  intro c
  exact diagonal.terminalSimultaneousMargin hA D representative offset radius
    Fsys x w₀ hw₀ data c

end DiagonalHermiteRankPreprocessedQuantitativeData
end AbelFormalization
