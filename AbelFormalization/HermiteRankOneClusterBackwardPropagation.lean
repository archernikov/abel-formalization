import AbelFormalization.FiniteAnalyticTerminalCoefficientBridge
import AbelFormalization.HermiteRankIndividualSimultaneousBoundaryCompatibility
import AbelFormalization.HermiteRankPreprocessedIndividualQuantitativePropagation

/-!
# Backward quantitative propagation through one Hermite cluster

This module composes the two concrete finite recursions belonging to one
ordered cluster.  A terminal lower bound first crosses every simultaneous
operation, then a finite change of generating family crosses the
simultaneous/individual seam, and finally the mixed individual recursion
reaches the incoming boundary of the cluster.

The paper-coordinate compatibility at the seam is automatic and is provided
by `individualSimultaneousBoundaryCompatibility`.  The remaining seam datum
is only the finite numeric change between independently selected analytic
representatives.  It is stated as an eventual linear-combination identity
with polynomially bounded coefficients.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u

/-- An eventual equality of scales transports an inverse-power lower bound. -/
theorem HasInversePowerLowerBound.congr_scale_of_eventually
    {X κ : Type*} [Fintype κ] [Nonempty κ]
    {l : Filter X} {R S : X → ℝ} {f : κ → X → ℝ}
    (hf : HasInversePowerLowerBound l R f)
    (hRS : ∀ᶠ x in l, R x = S x) :
    HasInversePowerLowerBound l S f := by
  obtain ⟨c, hc, M, hlower⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hlower, hRS] with x hx hscale
  simpa only [hscale] using hx

/-- Adding a fixed natural tail does not change an eventual inverse-power
lower bound.  Both the family and its scale are shifted together. -/
theorem hasInversePowerLowerBound_nat_add_iff
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (N : ℕ) (scale : ℕ → ℝ) (f : κ → ℕ → ℝ) :
    HasInversePowerLowerBound atTop (fun n ↦ scale (n + N))
        (fun k n ↦ f k (n + N)) ↔
      HasInversePowerLowerBound atTop scale f := by
  constructor
  · rintro ⟨c, hc, M, hlower⟩
    refine ⟨c, hc, M, ?_⟩
    rw [Filter.eventually_atTop] at hlower ⊢
    obtain ⟨n₀, hn₀⟩ := hlower
    refine ⟨n₀ + N, ?_⟩
    intro n hn
    have hN : N ≤ n := by omega
    have hn₀' : n₀ ≤ n - N := by omega
    have hraw := hn₀ (n - N) hn₀'
    simpa [finiteFamilyMaxAbs, Nat.sub_add_cancel hN] using hraw
  · intro hf
    exact hf.comp_tendsto (fun n ↦ n + N) (by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat N)

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

/-- Shift only by the additional simultaneous tail.  The underlying
individual boundary values already contain the common individual tail. -/
def individualSimultaneousTailShift
    (hA : IsAbel A) (n : ℕ) : ℕ :=
  n + boundary.simultaneousQuantitativeTail D representative offset radius Fsys
    x w₀ hw₀ data hA

/-- An individual-boundary scale on the common individual-plus-simultaneous
tail. -/
def individualMixedBoundaryScaleOnSimultaneousTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) (n : ℕ) : ℝ :=
  data.orderedClusterIndividualBoundaryScale A
    (boundary.individualQuantitativeSubsequence D representative offset radius
      Fsys x w₀ hw₀ data hA) c (boundary.preprocessed.fixedSteps c) q
    (boundary.individualSimultaneousTailShift D representative offset radius
      Fsys x w₀ hw₀ data hA n)

/-- A finite mixed individual-boundary family on the common
individual-plus-simultaneous tail. -/
def individualMixedBoundaryValueOnSimultaneousTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) :=
  fun b n ↦
    (boundary.individualMixedNumericBoundaryCompatibility D representative
      offset radius Fsys x w₀ hw₀ data hA c).boundaryValue q b
      (boundary.individualSimultaneousTailShift D representative offset radius
        Fsys x w₀ hw₀ data hA n)

/-- Residual finite representative compatibility at the boundary between the
first simultaneous source family and the last individual mixed boundary.

The equality of literal active and smaller-prefix assignments is already the
theorem `individualSimultaneousBoundaryCompatibility`; this record asks only
for the change matrix between the two independently selected finite
generating families.  Equality of the canonical scales follows from the
fixed balancing plan and is proved independently. -/
structure IndividualSimultaneousFiniteFamilyCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA c) where
  coefficient :
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).source.count + 1) →
    Fin ((boundary.individualMixedNumericBoundaryCompatibility D representative
      offset radius Fsys x w₀ hw₀ data hA c).boundaryCount
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c) + 1) → ℕ → ℝ
  coefficient_bound : ∀ k b,
    HasPolynomialUpperBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c))
      (coefficient k b)
  identity : ∀ᶠ n in atTop, ∀ k,
    (segment.change
      (boundary.simultaneousNumericStage D representative offset radius Fsys x
        w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue k n =
      ∑ b, coefficient k b n *
        boundary.individualMixedBoundaryValueOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.individualMixedTerminalBoundaryIndex D representative offset
            radius Fsys x w₀ hw₀ data c) b n

/-- The exact paper-coordinate compatibility underlying the finite family
seam.  This is automatic; it is exposed here so consumers of the residual
numeric record do not need to reconstruct the coordinate proof. -/
def IndividualSimultaneousFiniteFamilyCompatibility.coordinateCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    {segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA c}
    (_compatibility : boundary.IndividualSimultaneousFiniteFamilyCompatibility
      D representative offset radius Fsys x w₀ hw₀ data hA c segment) :
    boundary.IndividualSimultaneousBoundaryCompatibility D representative
      offset radius Fsys x w₀ hw₀ data hA c :=
  boundary.individualSimultaneousBoundaryCompatibility D representative offset
    radius Fsys x w₀ hw₀ data hA c

/-- Pull the first simultaneous source-family lower bound across the finite
representative seam to the shifted last individual mixed boundary. -/
theorem individualMixedTerminalBoundary_lower_of_simultaneousFirstBefore_lower
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA c)
    (compatibility : boundary.IndividualSimultaneousFiniteFamilyCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA c segment)
    (hfirst : HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      ((segment.change
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue)) :
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c))
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c)) := by
  have hfirst' : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c))
      ((segment.change
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue) :=
    hfirst.congr_scale_of_eventually (by
      simpa only [individualMixedBoundaryScaleOnSimultaneousTail,
        individualSimultaneousTailShift] using
        boundary.simultaneousQuantitativeBoundaryScale_zero_eventuallyEq_individualMixedTerminal
          D representative offset radius Fsys x w₀ hw₀ data hA c)
  apply hasInversePowerLowerBound_of_linearCombinations
    (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
      offset radius Fsys x w₀ hw₀ data hA c
      (boundary.individualMixedTerminalBoundaryIndex D representative offset
        radius Fsys x w₀ hw₀ data c))
    ((segment.change
      (boundary.simultaneousNumericStage D representative offset radius Fsys x
        w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue)
    compatibility.coefficient
  · exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c)
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c).val
        (boundary.individualSimultaneousTailShift D representative offset radius
          Fsys x w₀ hw₀ data hA n))
  · exact compatibility.identity
  · exact hasUniformPolynomialUpperBound_of_finite compatibility.coefficient
      (Filter.Eventually.of_forall fun n ↦ one_le_two.trans
        (two_le_clusterBalancingPrefixScale A
          (fun k ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA k) c)
          (boundary.preprocessed.fixedSteps c)
          (boundary.individualMixedTerminalBoundaryIndex D representative offset
            radius Fsys x w₀ hw₀ data c).val
          (boundary.individualSimultaneousTailShift D representative offset
            radius Fsys x w₀ hw₀ data hA n)))
      compatibility.coefficient_bound
  · exact hfirst'

/-- Complete backward propagation through the simultaneous and individual
parts of one cluster.  The output stays on the common two-part tail, so it is
ready to be used at the next cluster boundary. -/
theorem individualMixedInitialBoundary_lower_of_terminalSimultaneous_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hN : (((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ) ≤
        separation.N c)
    (individual : boundary.IndividualMixedFiniteAnalyticTraceData D
      representative offset radius Fsys x w₀ hw₀ data hA c)
    (simultaneous : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA c)
    (seam : boundary.IndividualSimultaneousFiniteFamilyCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA c simultaneous)
    (hterminal : HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
      ((simultaneous.change (Fin.last
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps)).afterValue)) :
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0) := by
  have hfirst :=
    boundary.hermiteSimultaneousQuantitativeFirstBeforeValue_lower_of_terminalAfterValue_lower
      D representative offset radius Fsys x w₀ hw₀ data separation hA c hN
      simultaneous hterminal
  have hlastShift :=
    boundary.individualMixedTerminalBoundary_lower_of_simultaneousFirstBefore_lower
      D representative offset radius Fsys x w₀ hw₀ data hA c simultaneous seam
      hfirst
  let Ntail := boundary.simultaneousQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let terminal := boundary.individualMixedTerminalBoundaryIndex D representative
    offset radius Fsys x w₀ hw₀ data c
  let compatibility := boundary.individualMixedNumericBoundaryCompatibility D
    representative offset radius Fsys x w₀ hw₀ data hA c
  have hlast : HasInversePowerLowerBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) terminal)
      (compatibility.boundaryValue terminal) := by
    exact (hasInversePowerLowerBound_nat_add_iff Ntail
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) terminal)
      (compatibility.boundaryValue terminal)).mp hlastShift
  have hzero := boundary.individualMixedBoundaryValue_zero_lower_of_terminal D
    representative offset radius Fsys x w₀ hw₀ data separation hA c individual
    hlast
  exact (hasInversePowerLowerBound_nat_add_iff Ntail
    (data.orderedClusterIndividualBoundaryScale A
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA) c
      (boundary.preprocessed.fixedSteps c) 0)
    (compatibility.boundaryValue 0)).mpr hzero

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
