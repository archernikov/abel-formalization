import AbelFormalization.HermiteRankTopPrefixPreprocessedSequenceBoundary
import AbelFormalization.FiniteGeneratorSpanLowerBound
import AbelFormalization.InversePowerLowerBoundNonvanishing

/-!
# Contradiction from a quantitative lower bound at the Hermite top prefix

The global quantitative descent returns a lower bound for some finite family
spanning the literal ordered-cluster top-prefix ideal.  The family chosen by
that descent need not be the Hermite/rank boundary's displayed family.  This
module changes families using equality of ideal spans, transports the
boundary's eventual vanishing to the fixed balancing subsequence, and applies
the general inverse-power-lower/nonvanishing contradiction.

Evaluation of arbitrary analytic germs away from their base point requires a
choice of representatives.  Accordingly, the final theorem asks only for the
generatorwise equality identifying the propagated top evaluation with the
concrete selected Hermite representative evaluation.  All span and vanishing
facts are supplied by the existing boundary data.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

variable {ι : Type*}

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
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

/-- The translated source point on the representative-cluster and balancing
subsequence selected by the preprocessed boundary. -/
def selectedTopPrefixSource (n : ℕ) : RestrictedSource m p a :=
  restrictedSourceTranslateToZero w₀
    (x (data.subsequence (boundary.preprocessed.balancingSubsequence n)))

/-- The retained full-Hermite assignment at the selected translated source
point, before relabeling it by the ordered top-prefix equivalence. -/
def selectedTopPrefixRetainedAssignment (n : ℕ) :
    PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount boundary.S + 1)) → ℝ :=
  paperRankRetainedArgument
    (paperRankFullHermiteSmoothValue (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
      boundary.Fbranch)
    (boundary.selectedTopPrefixSource D representative offset radius Fsys x
      w₀ hw₀ data n)

/-- The bounded parameter at which the selected top-prefix representative is
evaluated. -/
def selectedTopPrefixBoxParameter (n : ℕ) : RestrictedBoxSpace p :=
  (boundary.selectedTopPrefixSource D representative offset radius Fsys x
    w₀ hw₀ data n).1.2

/-- Eventual top-prefix vanishing remains true on the further balancing
subsequence. -/
theorem selected_topPrefix_vanish :
    ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval
        (data.paperRankHermiteTopPrefixAssignment boundary.S
          (boundary.selectedTopPrefixRetainedAssignment D representative
            offset radius Fsys x w₀ hw₀ data n))
        (data.paperRankHermiteTopPrefixRepresentative boundary.S
          (boundary.representativePolynomial j)
          (boundary.selectedTopPrefixBoxParameter D representative offset
            radius Fsys x w₀ hw₀ data n)) = 0 := by
  have hselected : Tendsto
      (data.subsequence ∘ boundary.preprocessed.balancingSubsequence)
      atTop atTop :=
    boundary.preprocessed.selectedSubsequence_strictMono.tendsto_atTop
  simpa only [Function.comp_apply, selectedTopPrefixRetainedAssignment,
    selectedTopPrefixSource, selectedTopPrefixBoxParameter] using
      hselected.eventually boundary.topPrefix_vanish

/-- Any inverse-power lower bound for a finite family spanning the literal
top-prefix ideal contradicts the Hermite boundary's selected common zeros.

`htopEvaluation` is the sole remaining compatibility seam: it says that the
coefficientwise/coordinatewise evaluation propagated through the algebraic
trace evaluates each mapped top generator as its concrete analytic
representative at the selected Hermite parameter. -/
theorem false_of_topPrefix_lower_of_eventually_topEvaluation
    (scale : ℕ → ℝ)
    (coefficientEval : RealAnalyticGerm p →+* (ℕ → ℝ))
    (coordinateValue :
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1)
          data.orderedClusterCount) → ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r : RealAnalyticGerm p,
      HasPolynomialUpperBound atTop scale (coefficientEval r))
    (hcoordinate : ∀ z,
      HasPolynomialUpperBound atTop scale (coordinateValue z))
    (lower : EvaluatedPaddedIdealLowerBound
      (ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1)
          data.orderedClusterCount))
      atTop scale coefficientEval coordinateValue
      (data.paperRankHermiteTopPrefixIdeal
        (RealAnalyticGerm p) boundary.S boundary.I))
    (htopEvaluation : ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval₂Hom coefficientEval coordinateValue
          (data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) boundary.S (boundary.generator j)) n =
        MvPolynomial.eval
          (boundary.selectedTopPrefixRetainedAssignment D representative
            offset radius Fsys x w₀ hw₀ data n)
          (boundary.representativePolynomial j
            (boundary.selectedTopPrefixBoxParameter D representative offset
              radius Fsys x w₀ hw₀ data n))) :
    False := by
  let paddedGenerator :=
    data.paperRankHermiteTopPrefixPaddedGenerator boundary.S
      boundary.generator
  have hpaddedLower : HasInversePowerLowerBound atTop scale
      (fun j n ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (paddedGenerator j) n) := by
    exact lower.lower_of_span_eq paddedGenerator
      boundary.paddedTopPrefix_span hscale hcoefficient hcoordinate
  have hselectedVanish := boundary.selected_topPrefix_vanish D representative
    offset radius Fsys x w₀ hw₀ data
  have hpaddedVanish : ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (paddedGenerator j) n = 0 := by
    filter_upwards [hselectedVanish, htopEvaluation] with n hn heval
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [paddedGenerator,
        RepresentativeClusterSubsequence.paperRankHermiteTopPrefixPaddedGenerator]
    · change MvPolynomial.eval₂Hom coefficientEval coordinateValue
          (data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) boundary.S (boundary.generator k)) n = 0
      calc
        _ = MvPolynomial.eval
            (boundary.selectedTopPrefixRetainedAssignment D representative
              offset radius Fsys x w₀ hw₀ data n)
            (boundary.representativePolynomial k
              (boundary.selectedTopPrefixBoxParameter D representative offset
                radius Fsys x w₀ hw₀ data n)) := heval k
        _ = MvPolynomial.eval
            (data.paperRankHermiteTopPrefixAssignment boundary.S
              (boundary.selectedTopPrefixRetainedAssignment D representative
                offset radius Fsys x w₀ hw₀ data n))
            (data.paperRankHermiteTopPrefixRepresentative boundary.S
              (boundary.representativePolynomial k)
              (boundary.selectedTopPrefixBoxParameter D representative offset
                radius Fsys x w₀ hw₀ data n)) :=
          (boundary.topPrefix_evaluation k
            (boundary.selectedTopPrefixBoxParameter D representative offset
              radius Fsys x w₀ hw₀ data n)
            (boundary.selectedTopPrefixRetainedAssignment D representative
              offset radius Fsys x w₀ hw₀ data n)).symm
        _ = 0 := hn k
  exact hpaddedLower.not_eventually_forall_eq_zero hscale hpaddedVanish

/-- Pointwise evaluation compatibility is a convenient stronger input for
`false_of_topPrefix_lower_of_eventually_topEvaluation`. -/
theorem false_of_topPrefix_lower
    (scale : ℕ → ℝ)
    (coefficientEval : RealAnalyticGerm p →+* (ℕ → ℝ))
    (coordinateValue :
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1)
          data.orderedClusterCount) → ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r : RealAnalyticGerm p,
      HasPolynomialUpperBound atTop scale (coefficientEval r))
    (hcoordinate : ∀ z,
      HasPolynomialUpperBound atTop scale (coordinateValue z))
    (lower : EvaluatedPaddedIdealLowerBound
      (ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1)
          data.orderedClusterCount))
      atTop scale coefficientEval coordinateValue
      (data.paperRankHermiteTopPrefixIdeal
        (RealAnalyticGerm p) boundary.S boundary.I))
    (htopEvaluation : ∀ j n,
      MvPolynomial.eval₂Hom coefficientEval coordinateValue
          (data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) boundary.S (boundary.generator j)) n =
        MvPolynomial.eval
          (boundary.selectedTopPrefixRetainedAssignment D representative
            offset radius Fsys x w₀ hw₀ data n)
          (boundary.representativePolynomial j
            (boundary.selectedTopPrefixBoxParameter D representative offset
              radius Fsys x w₀ hw₀ data n))) :
    False :=
  boundary.false_of_topPrefix_lower_of_eventually_topEvaluation D
    representative offset radius Fsys x w₀ hw₀ data scale coefficientEval
    coordinateValue hscale hcoefficient hcoordinate lower
    (Filter.Eventually.of_forall fun n j ↦ htopEvaluation j n)

/-- A coefficientwise descent may finish directly with the concrete padded
top-prefix representatives, without constructing a sequence-valued ring map
on all analytic germs.  An inverse-power lower bound for that literal finite
family contradicts its selected eventual common zeros. -/
theorem false_of_selectedPaddedTopPrefix_lower
    (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (lower : HasInversePowerLowerBound atTop scale
      (fun j n ↦ MvPolynomial.eval
        (data.paperRankHermiteTopPrefixAssignment boundary.S
          (boundary.selectedTopPrefixRetainedAssignment D representative
            offset radius Fsys x w₀ hw₀ data n))
        (data.paperRankHermiteTopPrefixPaddedRepresentative boundary.S
          boundary.representativePolynomial j
          (boundary.selectedTopPrefixBoxParameter D representative offset
            radius Fsys x w₀ hw₀ data n)))) :
    False := by
  have hzero : ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval
        (data.paperRankHermiteTopPrefixAssignment boundary.S
          (boundary.selectedTopPrefixRetainedAssignment D representative
            offset radius Fsys x w₀ hw₀ data n))
        (data.paperRankHermiteTopPrefixPaddedRepresentative boundary.S
          boundary.representativePolynomial j
          (boundary.selectedTopPrefixBoxParameter D representative offset
            radius Fsys x w₀ hw₀ data n)) = 0 := by
    simpa only [selectedTopPrefixRetainedAssignment,
      selectedTopPrefixSource, selectedTopPrefixBoxParameter,
      Function.comp_apply] using boundary.paddedTopPrefix_selected_vanish
  exact lower.not_eventually_forall_eq_zero hscale hzero

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
