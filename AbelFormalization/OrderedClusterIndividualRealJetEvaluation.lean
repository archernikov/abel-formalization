import AbelFormalization.HermiteRankTopPrefixClusterValues
import AbelFormalization.IndividualCentralRealJetEvaluation
import AbelFormalization.IndividualClusterBalancingHierarchy
import AbelFormalization.OrderedClusterIndividualTraceData

/-!
# Real-jet evaluation of one ordered-cluster balancing step

This module instantiates the selected-block real-jet evaluation at an actual
step of the fixed ordered-cluster balancing list.  The selected one-block
scale is the inverse-Abel value after the unit decrement.  The two full flat
assignments replace only that selected block; every remaining block is
evaluated through one common coefficient-ring homomorphism.

The optional Hermite sequence assignment below supplies the canonical flat
prefix value from `HermiteRankTopPrefixClusterValues`.  The evaluation results
themselves only require a flat base assignment and exact selected real-jet
data, so they can also be reused after later sequence transports.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

section StepValues

variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable (data : RepresentativeClusterSubsequence time)
variable (higher : ℕ) (c : Fin data.orderedClusterCount)

noncomputable local instance orderedClusterIndividualRealJetBlockDecidableEq :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- The literal prefix block selected by source step `j`.  It is written via
the trace index equivalence so that its type agrees definitionally with the
displayed transfer data at that step. -/
def orderedClusterIndividualSelectedBlock
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) :
    data.OrderedClusterPrefixBlock (c.val + 1) :=
  (data.orderedClusterPrefixIndividualSteps c fixedSteps).get
    (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)

/-- The trace-selected block is the literal prefix image of the balancing
coordinate at the same source position. -/
@[simp]
theorem orderedClusterIndividualSelectedBlock_eq
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) :
    data.orderedClusterIndividualSelectedBlock c fixedSteps j =
      data.orderedClusterBalancingPrefixBlock c (fixedSteps.get j) := by
  exact data.orderedClusterPrefixIndividualSteps_get c fixedSteps j

/-- The one-block variable after the selected unit decrement. -/
def orderedClusterIndividualPostLogScale
    (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) : Fin 1 → ℕ → ℝ :=
  fun _ n ↦ clusterBalancingStepValue A rawTime fixedSteps j n

/-- The selected scale is the inverse Abel function at the current prefix
time minus one. -/
@[simp]
theorem orderedClusterIndividualPostLogScale_apply
    (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) (i : Fin 1) (n : ℕ) :
    data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n =
      inverse A
        (clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc)
          (fixedSteps.get j) - 1) := by
  rfl

/-- If the fixed list is supplied by pointwise balancing plans, the same scale
is the selected post-decrement value in each actual plan. -/
theorem orderedClusterIndividualPostLogScale_apply_of_plan
    (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (base : ℕ → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (base n))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    (j : Fin fixedSteps.length) (i : Fin 1) (n : ℕ) :
    data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n =
      inverse A
        (clusterShiftedTimes (rawTime n) ((plans n).steps.take j.castSucc)
          (fixedSteps.get j) - 1) := by
  rw [hfixedSteps n]
  rfl

/-- Turn the concrete Hermite value on the actual `(c+1)`-prefix into the
sequence-valued flat assignment consumed by the displayed trace API. -/
def paperRankHermiteOrderedClusterPrefixSequenceValue
    {ι : Type*} {p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : ℕ → PaperRankParameterSpace m p) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) (c.val + 1)) →
      ℕ → ℝ :=
  fun z n ↦ paperRankHermitePrefixValue data D representative offset S B F
    (sw n) (c.val + 1) z

/-- Replace the selected block of a flat prefix assignment by its exact
pre-log real-jet values.  All other blocks are copied from `baseValue`. -/
def orderedClusterIndividualPreLogFlatAssignment
    {A : ℝ → ℝ}
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) i)) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ :=
  selectedBlockJoinedAssignment
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
    (individualCentralPreLogActiveAssignment
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) jets)
    (selectedBlockCoefficientAssignment
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1))
      (data.orderedClusterIndividualSelectedBlock c fixedSteps j) baseValue)

/-- Replace the selected block by its exact post-log central values, keeping
the same remaining-block assignment as on the pre-log side. -/
def orderedClusterIndividualPostLogFlatAssignment
    (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ :=
  selectedBlockJoinedAssignment
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
    (individualCentralPostLogActiveAssignment A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)))
    (selectedBlockCoefficientAssignment
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1))
      (data.orderedClusterIndividualSelectedBlock c fixedSteps j) baseValue)

/-- The selected restriction of the full pre-log assignment is exactly the
one-block real-jet source assignment. -/
@[simp]
theorem selectedBlockActiveAssignment_orderedClusterIndividualPreLog
    {A : ℝ → ℝ}
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) i)) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
        (data.orderedClusterIndividualPreLogFlatAssignment higher c
          rawTime fixedSteps j baseValue jets) =
      individualCentralPreLogActiveAssignment
        (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
        (selectedBlockDerivativeCount
          (data.orderedClusterPrefixConstantDerivativeCount
            (higher + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) jets := by
  simp [orderedClusterIndividualPreLogFlatAssignment]

/-- The selected restriction of the full post-log assignment is exactly the
one-block central assignment. -/
@[simp]
theorem selectedBlockActiveAssignment_orderedClusterIndividualPostLog
    (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
        (data.orderedClusterIndividualPostLogFlatAssignment higher c A
          rawTime fixedSteps j baseValue) =
      individualCentralPostLogActiveAssignment A
        (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
        (selectedBlockDerivativeCount
          (data.orderedClusterPrefixConstantDerivativeCount
            (higher + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) := by
  simp [orderedClusterIndividualPostLogFlatAssignment]

/-- An already available flat prefix assignment is exactly the constructed
pre-log assignment as soon as its selected restriction has the required
real-jet values.  This is the compatibility premise needed to specialize the
construction to the concrete Hermite prefix sequence. -/
theorem orderedClusterIndividualPreLogFlatAssignment_eq_base
    {A : ℝ → ℝ}
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) i))
    (hactive : selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) baseValue =
      individualCentralPreLogActiveAssignment
        (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
        (selectedBlockDerivativeCount
          (data.orderedClusterPrefixConstantDerivativeCount
            (higher + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) jets) :
    data.orderedClusterIndividualPreLogFlatAssignment higher c
        rawTime fixedSteps j baseValue jets = baseValue := by
  funext z
  change selectedBlockJoinedAssignment
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1))
      (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
      (individualCentralPreLogActiveAssignment
        (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
        (selectedBlockDerivativeCount
          (data.orderedClusterPrefixConstantDerivativeCount
            (higher + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) jets)
      (selectedBlockCoefficientAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) baseValue) z =
    baseValue z
  rw [← hactive]
  exact selectedBlockAssignment_eq_sum_elim
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterIndividualSelectedBlock c fixedSteps j) baseValue z

/-- Both sides of the balancing step use this one coefficient-ring
evaluation, obtained by restricting the original flat prefix assignment to
all blocks except the selected one. -/
def orderedClusterIndividualCoefficientEvaluationHom
    (R : Type u) [CommRing R]
    (coefficientMap : R →+* (ℕ → ℝ))
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ) :
    IndividualCentralCoefficientRing R
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1))
      (data.orderedClusterIndividualSelectedBlock c fixedSteps j) →+*
        (ℕ → ℝ) :=
  selectedBlockCoefficientEvaluationHom coefficientMap
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterIndividualSelectedBlock c fixedSteps j) baseValue

/-- The pre-log full assignment induces the unchanged coefficient hom. -/
theorem selectedBlockCoefficientEvaluationHom_orderedClusterIndividualPreLog
    (R : Type u) [CommRing R]
    {A : ℝ → ℝ}
    (coefficientMap : R →+* (ℕ → ℝ))
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) i)) :
    selectedBlockCoefficientEvaluationHom coefficientMap
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
        (data.orderedClusterIndividualPreLogFlatAssignment higher c
          rawTime fixedSteps j baseValue jets) =
      data.orderedClusterIndividualCoefficientEvaluationHom
        higher c R coefficientMap fixedSteps j baseValue := by
  simp [orderedClusterIndividualPreLogFlatAssignment,
    orderedClusterIndividualCoefficientEvaluationHom,
    selectedBlockCoefficientEvaluationHom]

/-- The post-log full assignment induces the same coefficient hom. -/
theorem selectedBlockCoefficientEvaluationHom_orderedClusterIndividualPostLog
    (R : Type u) [CommRing R]
    (A : ℝ → ℝ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ) :
    selectedBlockCoefficientEvaluationHom coefficientMap
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
        (data.orderedClusterIndividualPostLogFlatAssignment higher c A
          rawTime fixedSteps j baseValue) =
      data.orderedClusterIndividualCoefficientEvaluationHom
        higher c R coefficientMap fixedSteps j baseValue := by
  simp [orderedClusterIndividualPostLogFlatAssignment,
    orderedClusterIndividualCoefficientEvaluationHom,
    selectedBlockCoefficientEvaluationHom]

/-- The representative coordinate of the selected pre-log block is exactly
the inverse-Abel value at the preceding balancing boundary. -/
theorem orderedClusterIndividualPreLog_selected_q
    {A : ℝ → ℝ} (hA : IsAbel A)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) i))
    (i : Fin 1) (n : ℕ) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j)
        (data.orderedClusterIndividualPreLogFlatAssignment higher c
          rawTime fixedSteps j baseValue jets) (Sum.inl i) n =
      inverse A
        (clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc)
          (fixedSteps.get j)) := by
  rw [data.selectedBlockActiveAssignment_orderedClusterIndividualPreLog]
  simp only [individualCentralPreLogActiveAssignment_q,
    orderedClusterIndividualPostLogScale_apply]
  calc
    E (inverse A
        (clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc)
          (fixedSteps.get j) - 1)) =
        inverse A
          ((clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc)
            (fixedSteps.get j) - 1) + 1) :=
      (hA.inverse_add_one
        (clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc)
          (fixedSteps.get j) - 1)).symm
    _ = inverse A
        (clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc)
          (fixedSteps.get j)) := by
      congr 1
      ring

end StepValues

namespace OrderedClusterIndividualDisplayedTraceData

variable (R : Type u) [CommRing R]
variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable (data : RepresentativeClusterSubsequence time)
variable (higher : ℕ) (c : Fin data.orderedClusterCount)

noncomputable local instance orderedClusterIndividualDisplayedRealJetBlockDecidableEq :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Exact source-side evaluation of the displayed family at source-indexed
balancing step `j`. -/
theorem eval_beforeGenerator_preLog
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    (j : Fin fixedSteps.length)
    {A : ℝ → ℝ}
    (coefficientMap : R →+* (ℕ → ℝ))
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j i n)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c fixedSteps j) i))
    (k : Fin ((displayed.displayed
      (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).source.count + 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom coefficientMap
        (data.orderedClusterIndividualPreLogFlatAssignment higher c
          rawTime fixedSteps j baseValue jets)
        (IndividualCentralTransferData.DisplayedData.beforeGenerator R
          (displayed.displayed
            (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)) k) n =
      realJetSourceEvaluationHom
        (data.orderedClusterIndividualCoefficientEvaluationHom
          higher c R coefficientMap fixedSteps j baseValue)
        (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
        (selectedBlockDerivativeCount
          (data.orderedClusterPrefixConstantDerivativeCount
            (higher + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) jets n
        ((displayed.displayed
          (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).source.generator k) := by
  have h :=
    IndividualCentralTransferData.DisplayedData.eval_beforeGenerator_preLog
      R
      (displayed.displayed
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j))
      coefficientMap
      (data.orderedClusterIndividualPreLogFlatAssignment higher c
        rawTime fixedSteps j baseValue jets)
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
      jets
      (data.selectedBlockActiveAssignment_orderedClusterIndividualPreLog
        higher c rawTime fixedSteps j baseValue jets)
      k n
  have hcoefficient :=
    data.selectedBlockCoefficientEvaluationHom_orderedClusterIndividualPreLog
      higher c R coefficientMap rawTime fixedSteps j baseValue jets
  unfold orderedClusterIndividualSelectedBlock at hcoefficient
  rw [hcoefficient] at h
  exact h

/-- Exact central-side evaluation of the displayed family at the successor
boundary of source-indexed balancing step `j`. -/
theorem eval_afterGenerator_postLog
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    (j : Fin fixedSteps.length)
    (A : ℝ → ℝ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (baseValue : ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1)) → ℕ → ℝ)
    (k : Fin ((displayed.displayed
      (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).central.count + 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom coefficientMap
        (data.orderedClusterIndividualPostLogFlatAssignment higher c A
          rawTime fixedSteps j baseValue)
        (IndividualCentralTransferData.DisplayedData.afterGenerator R
          (displayed.displayed
            (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)) k) n =
      realJetCentralEvaluationHom A
        (data.orderedClusterIndividualCoefficientEvaluationHom
          higher c R coefficientMap fixedSteps j baseValue)
        (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
        (selectedBlockDerivativeCount
          (data.orderedClusterPrefixConstantDerivativeCount
            (higher + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c fixedSteps j)) n
        ((displayed.displayed
          (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)).central.generator k) := by
  have h :=
    IndividualCentralTransferData.DisplayedData.eval_afterGenerator_postLog
      R
      (displayed.displayed
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j))
      A coefficientMap
      (data.orderedClusterIndividualPostLogFlatAssignment higher c A
        rawTime fixedSteps j baseValue)
      (data.orderedClusterIndividualPostLogScale c A rawTime fixedSteps j)
      (data.selectedBlockActiveAssignment_orderedClusterIndividualPostLog
        higher c A rawTime fixedSteps j baseValue)
      k n
  have hcoefficient :=
    data.selectedBlockCoefficientEvaluationHom_orderedClusterIndividualPostLog
      higher c R A coefficientMap rawTime fixedSteps j baseValue
  unfold orderedClusterIndividualSelectedBlock at hcoefficient
  rw [hcoefficient] at h
  exact h

end OrderedClusterIndividualDisplayedTraceData

end RepresentativeClusterSubsequence
end AbelFormalization
