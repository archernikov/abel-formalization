import AbelFormalization.HermiteRankBottomSimultaneousBoundaryBridge
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeTail

/-!
# Bottom terminal lower bound on the common quantitative tail

The finite analytic terminal-localization construction already produces a
lower bound after every cofinal reindexing.  This module specializes it to
the common individual-plus-simultaneous tail and identifies its scale with
the terminal simultaneous boundary scale of ordered cluster zero.

The analytic terminal generators and the terminal `afterValue` family in a
simultaneous segment may use independently chosen representatives.  The only
residual datum below is their eventual pointwise equality.  No global
evaluation homomorphism on analytic germs is used.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Topology

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

/-- The terminal `afterValue` family of the bottom simultaneous segment on
the common individual-plus-simultaneous quantitative tail. -/
abbrev bottomSimultaneousQuantitativeTerminalAfterValue
    (hA : IsAbel A)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data)) :=
  (segment.change
    (boundary.bottomSimultaneousTerminalIndex D representative offset radius
      Fsys x w₀ hw₀ data)).afterValue

/-- The bottom terminal scale pulled back along the common quantitative
reindexing is literally the output scale of the last simultaneous operation
of ordered cluster zero. -/
theorem bottomTerminalScale_simultaneousQuantitativeReindex_eq
    (hA : IsAbel A) :
    boundary.bottomTerminalScale D representative offset radius Fsys x w₀ hw₀
        data
        (boundary.simultaneousQuantitativeReindex D representative offset
          radius Fsys x w₀ hw₀ data hA) =
      boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data)
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.terminalized.extraSteps +
            1) := by
  rfl

/-- The sole representative seam at the common-tail bottom boundary.  The
chosen analytic representatives of the last central generators agree
eventually with the terminal `afterValue` family stored in the simultaneous
segment. -/
def BottomTerminalSimultaneousQuantitativeCompatibility
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data)) : Prop :=
  ∀ᶠ n in atTop, ∀ b,
    (boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceValue
        (boundary.bottomTerminalParameter D representative offset radius Fsys x
          w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (boundary.bottomTerminalSymbolValue D representative offset radius Fsys
          x w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA)) b n =
      boundary.bottomSimultaneousQuantitativeTerminalAfterValue D
        representative offset radius Fsys x w₀ hw₀ data hA segment b n

/-- Terminal localization supplies the canonical last simultaneous
`afterValue` lower bound directly on the common quantitative tail. -/
theorem bottomSimultaneousQuantitativeTerminalAfterValue_lower
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data))
    (compatibility :
      boundary.BottomTerminalSimultaneousQuantitativeCompatibility D
        representative offset radius Fsys x w₀ hw₀ data hA localization
        segment) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data)
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.terminalized.extraSteps +
            1))
      (boundary.bottomSimultaneousQuantitativeTerminalAfterValue D
        representative offset radius Fsys x w₀ hw₀ data hA segment) := by
  have hsource :=
    boundary.bottomTerminalSourceValue_lower_of_tendsto D representative offset
      radius Fsys x w₀ hw₀ data hA
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA) localization
  rw [boundary.bottomTerminalScale_simultaneousQuantitativeReindex_eq D
    representative offset radius Fsys x w₀ hw₀ data hA] at hsource
  exact hsource.congr_of_eventually compatibility

/-- End-to-end propagation of the localized bottom lower bound through the
whole simultaneous segment on the common tail. -/
theorem bottomSimultaneousQuantitativeFirstBeforeValue_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hN : (((boundary.bottomTerminalExtraSteps D representative offset radius
      Fsys x w₀ hw₀ data + 6 : ℕ) : ℝ)) ≤
        separation.N (bottomTerminalCluster x data))
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data))
    (compatibility :
      boundary.BottomTerminalSimultaneousQuantitativeCompatibility D
        representative offset radius Fsys x w₀ hw₀ data hA localization
        segment) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data) 0)
      ((segment.change
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.firstCentralStepIndex).beforeValue) := by
  apply
    boundary.hermiteSimultaneousQuantitativeFirstBeforeValue_lower_of_terminalAfterValue_lower
      D representative offset radius Fsys x w₀ hw₀ data separation hA
      (bottomTerminalCluster x data) hN segment
  exact boundary.bottomSimultaneousQuantitativeTerminalAfterValue_lower D
    representative offset radius Fsys x w₀ hw₀ data hA localization segment
    compatibility

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
