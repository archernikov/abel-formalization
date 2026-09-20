import AbelFormalization.OrderedClusterIndividualPreprocessing
import AbelFormalization.IndividualCentralRealJetIdentities

/-!
# Displayed individual-decrement traces for an ordered cluster

This module specializes the generic selected-block trace to the literal
`(c+1)`-prefix ring used by the ordered-cluster descent.  It keeps the
balancing list as the source index and records its image as actual prefix
blocks, so the combinatorial balancing plan and the algebraic transfer data
can be addressed by the same finite step number.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

section

variable (R : Type u) [CommRing R]
variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable (data : RepresentativeClusterSubsequence time)
variable (higher : ℕ) (c : Fin data.orderedClusterCount)

noncomputable local instance orderedClusterIndividualBlockDecidableEq :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Mapping balancing indices to literal prefix blocks preserves the number
of individual logarithmic steps. -/
@[simp]
theorem orderedClusterPrefixIndividualSteps_length
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))) :
    (data.orderedClusterPrefixIndividualSteps c fixedSteps).length =
      fixedSteps.length := by
  simp [orderedClusterPrefixIndividualSteps]

/-- The canonical equivalence between source balancing-step indices and the
indices of their literal-prefix image. -/
def orderedClusterIndividualStepIndexEquiv
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))) :
    Fin fixedSteps.length ≃
      Fin (data.orderedClusterPrefixIndividualSteps c fixedSteps).length :=
  { toFun := fun j ↦ ⟨j.val, by simpa using j.isLt⟩
    invFun := fun j ↦ ⟨j.val, by simpa using j.isLt⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

@[simp]
theorem orderedClusterIndividualStepIndexEquiv_apply_val
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) :
    (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j).val = j.val :=
  rfl

/-- Looking up a mapped trace step gives exactly the literal prefix block
corresponding to the balancing index at the same source position. -/
@[simp]
theorem orderedClusterPrefixIndividualSteps_get
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) :
    (data.orderedClusterPrefixIndividualSteps c fixedSteps).get
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j) =
      data.orderedClusterBalancingPrefixBlock c (fixedSteps.get j) := by
  let j' : Fin
      (data.orderedClusterPrefixIndividualSteps c fixedSteps).length :=
    ⟨j.val, by simpa using j.isLt⟩
  have hj' : data.orderedClusterIndividualStepIndexEquiv c fixedSteps j = j' :=
    Fin.ext rfl
  rw [hj']
  simp [j', orderedClusterPrefixIndividualSteps, List.get_eq_getElem]

/-- The ideal at a boundary of the literal individual-decrement trace. -/
abbrev orderedClusterIndividualIdealBoundary
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    (j : Fin
      ((data.orderedClusterPrefixIndividualSteps c fixedSteps).length + 1)) :=
  individualCentralIdealBoundary R
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterPrefixIndividualSteps c fixedSteps) I j

/-- Boundary zero is the incoming ordered-prefix ideal. -/
@[simp]
theorem orderedClusterIndividualIdealBoundary_zero
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    data.orderedClusterIndividualIdealBoundary
      R higher c fixedSteps I 0 = I := by
  exact individualCentralIdealBoundary_zero R _ _ I

/-- The last boundary is the individually preprocessed ordered-prefix ideal. -/
@[simp]
theorem orderedClusterIndividualIdealBoundary_last
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    data.orderedClusterIndividualIdealBoundary R higher c fixedSteps I
        (Fin.last
          (data.orderedClusterPrefixIndividualSteps c fixedSteps).length) =
      data.orderedClusterIndividuallyPreprocessedIdeal
        R higher c fixedSteps I := by
  exact individualCentralIdealBoundary_last R _ _ I

/-- Generic finite transfer certificates specialized to the actual block
list of an ordered cluster. -/
abbrev OrderedClusterIndividualIdealTraceData
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :=
  IndividualCentralIdealTraceData R
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterPrefixIndividualSteps c fixedSteps) I

/-- Noetherianity supplies a nonempty transfer certificate at every
individual decrement in the fixed ordered-cluster plan. -/
theorem nonempty_orderedClusterIndividualIdealTraceData
    [IsNoetherianRing R]
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    Nonempty
      (data.OrderedClusterIndividualIdealTraceData
        R higher c fixedSteps I) := by
  classical
  exact nonempty_individualCentralIdealTraceData R _ _ I

/-- Displayed finite generators and exact source/central identities at every
individual decrement of the ordered cluster. -/
abbrev OrderedClusterIndividualDisplayedTraceData
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    (traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I) :=
  IndividualCentralDisplayedTraceData R
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterPrefixIndividualSteps c fixedSteps) I traceData

/-- Choose all displayed families and their exact coefficient matrices for
the literal ordered-cluster trace at once. -/
theorem nonempty_orderedClusterIndividualDisplayedTraceData
    [IsNoetherianRing R]
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    (traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I) :
    Nonempty
      (data.OrderedClusterIndividualDisplayedTraceData
        R higher c fixedSteps I traceData) := by
  classical
  exact nonempty_individualCentralDisplayedTraceData R _ _ I traceData

namespace OrderedClusterIndividualDisplayedTraceData

/-- The displayed source family at a source-indexed balancing step spans the
literal boundary ideal immediately before that decrement. -/
theorem before_span
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    (j : Fin fixedSteps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.DisplayedData.beforeGenerator R
        (displayed.displayed
          (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)))) =
      individualCentralIdealBefore R
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterPrefixIndividualSteps c fixedSteps) I
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j) := by
  exact IndividualCentralDisplayedTraceData.before_span R displayed
    (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)

/-- The displayed central family at a source-indexed balancing step spans
the next literal boundary ideal. -/
theorem after_span_boundary_succ
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    (j : Fin fixedSteps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.DisplayedData.afterGenerator R
        (displayed.displayed
          (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)))) =
      individualCentralIdealBoundary R
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterPrefixIndividualSteps c fixedSteps) I
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j).succ := by
  exact IndividualCentralDisplayedTraceData.after_span_boundary_succ R displayed
    (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j)

end OrderedClusterIndividualDisplayedTraceData

end

end RepresentativeClusterSubsequence
end AbelFormalization
