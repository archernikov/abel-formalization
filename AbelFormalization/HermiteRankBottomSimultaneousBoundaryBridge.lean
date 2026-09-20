import AbelFormalization.HermiteRankBottomTerminalEvaluationInputs
import AbelFormalization.HermiteRankPreprocessedSimultaneousNumericData

/-!
# Bottom terminal localization to the first simultaneous segment

The analytic bottom seed and the concrete simultaneous segment use the same
last displayed central family of ordered cluster zero.  Their values arise
from independently chosen finite analytic representatives, so the only
remaining compatibility datum is their eventual pointwise equality.  Once
that equality is supplied, this module transports the localized lower bound
to the segment's literal terminal `afterValue` and then invokes the existing
finite simultaneous recursion.
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

/-- The last simultaneous operation index in ordered cluster zero. -/
abbrev bottomSimultaneousTerminalIndex :
    Fin ((boundary.simultaneousNumericStage D representative offset radius Fsys
      x w₀ hw₀ data (bottomTerminalCluster x data)).certificate.terminalized.extraSteps +
        1) :=
  Fin.last (boundary.bottomTerminalExtraSteps D representative offset radius
    Fsys x w₀ hw₀ data)

/-- The terminal `afterValue` family stored in a concrete cluster-zero
simultaneous segment. -/
abbrev bottomSimultaneousTerminalAfterValue
    (hA : IsAbel A)
    (segment : boundary.SimultaneousFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data)) :=
  (segment.change
    (boundary.bottomSimultaneousTerminalIndex D representative offset radius
      Fsys x w₀ hw₀ data)).afterValue

/-- The sole boundary seam between terminal localization and the simultaneous
segment: their independently chosen representatives of the same last central
generators agree eventually along the selected Hermite parameter sequence. -/
def BottomTerminalSimultaneousCompatibility
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (segment : boundary.SimultaneousFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data)) : Prop :=
  ∀ᶠ n in atTop, ∀ b,
    (boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceValue
        (boundary.bottomTerminalParameter D representative offset radius Fsys x
          w₀ hw₀ data id)
        (boundary.bottomTerminalSymbolValue D representative offset radius Fsys
          x w₀ hw₀ data id) b n =
      boundary.bottomSimultaneousTerminalAfterValue D representative offset
        radius Fsys x w₀ hw₀ data hA segment b n

/-- The concrete analytic bottom seed is a lower bound for the terminal
`afterValue` family of the cluster-zero simultaneous segment. -/
theorem bottomSimultaneousTerminalAfterValue_lower
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (segment : boundary.SimultaneousFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data))
    (compatibility : boundary.BottomTerminalSimultaneousCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA localization segment) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data (bottomTerminalCluster x data)
        (boundary.bottomTerminalExtraSteps D representative offset radius Fsys x
          w₀ hw₀ data + 1))
      (boundary.bottomSimultaneousTerminalAfterValue D representative offset
        radius Fsys x w₀ hw₀ data hA segment) := by
  have hsource := boundary.bottomTerminalSourceValue_lower_id D representative
    offset radius Fsys x w₀ hw₀ data hA localization
  exact hsource.congr_of_eventually compatibility

/-- End-to-end propagation from the analytic bottom seed through every
simultaneous operation of ordered cluster zero. -/
theorem bottomSimultaneousFirstBeforeValue_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hN : (((boundary.bottomTerminalExtraSteps D representative offset radius
      Fsys x w₀ hw₀ data + 6 : ℕ) : ℝ)) ≤
        separation.N (bottomTerminalCluster x data))
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (segment : boundary.SimultaneousFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data))
    (compatibility : boundary.BottomTerminalSimultaneousCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA localization segment) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data (bottomTerminalCluster x data) 0)
      (segment.change
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.firstCentralStepIndex).beforeValue := by
  apply boundary.hermiteSimultaneousFirstBeforeValue_lower_of_terminalAfterValue_lower
    D representative offset radius Fsys x w₀ hw₀ data separation hA
    (bottomTerminalCluster x data) hN segment
  exact boundary.bottomSimultaneousTerminalAfterValue_lower D representative
    offset radius Fsys x w₀ hw₀ data hA localization segment compatibility

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
