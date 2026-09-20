import AbelFormalization.IndividualCentralIdealStep

/-!
# Indexed transfer data for individual central ideal steps

A fixed balancing decrement list determines a finite sequence of ideals in
the common flat block ring.  This module exposes all boundaries of that
sequence, the ideals immediately before and after every decrement, and one
nonempty quantitative-transfer family for every actual step.

The construction is algebraic.  It adds no evaluation data or analytic
hypotheses.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

universe u v

section

variable (R : Type u) [CommRing R]
variable {Block : Type v} [DecidableEq Block]

/-- Applying two lists of individual steps is applying the first list and
then the second list. -/
theorem individualCentralIdealSteps_append
    (d : Block → ℕ) (first second : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    individualCentralIdealSteps R d (first ++ second) I =
      individualCentralIdealSteps R d second
        (individualCentralIdealSteps R d first I) := by
  induction first generalizing I with
  | nil => rfl
  | cons selected first ih =>
      exact ih (individualCentralIdealStep R d selected I)

/-- The ideal at a boundary of the fixed decrement list.  Boundary zero is
the input, and the last boundary is the result of every decrement. -/
def individualCentralIdealBoundary
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (j : Fin (steps.length + 1)) :
    Ideal (MvPolynomial (ClusterOperationSymbol Block d) R) :=
  individualCentralIdealSteps R d (steps.take j) I

@[simp]
theorem individualCentralIdealBoundary_zero
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    individualCentralIdealBoundary R d steps I 0 = I :=
  rfl

@[simp]
theorem individualCentralIdealBoundary_last
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    individualCentralIdealBoundary R d steps I (Fin.last steps.length) =
      individualCentralIdealSteps R d steps I := by
  simp [individualCentralIdealBoundary]

/-- The ideal immediately before decrement `j`. -/
def individualCentralIdealBefore
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (j : Fin steps.length) :
    Ideal (MvPolynomial (ClusterOperationSymbol Block d) R) :=
  individualCentralIdealBoundary R d steps I j.castSucc

/-- The curried before-ideal after the representative translation used by
the quantitative-transfer certificate at decrement `j`. -/
def individualCentralTranslatedCurriedIdealBefore
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (j : Fin steps.length) :
    Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d (steps.get j)))
      (IndividualCentralCoefficientRing R d (steps.get j))) :=
  (individualCentralCurriedIdeal R d (steps.get j)
    (individualCentralIdealBefore R d steps I j)).map
      (polynomialCoordinateTranslation
        (Sum.elim
          (fun _ : Fin 1 ↦
            (-1 : IndividualCentralCoefficientRing R d (steps.get j)))
          (fun _ : CentralPolynomialIndex (Fin 1)
              (selectedBlockDerivativeCount d (steps.get j)) (Fin 1) ↦
            (0 : IndividualCentralCoefficientRing R d
              (steps.get j))))).toRingHom

/-- The ideal immediately after decrement `j`. -/
def individualCentralIdealAfter
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (j : Fin steps.length) :
    Ideal (MvPolynomial (ClusterOperationSymbol Block d) R) :=
  individualCentralIdealStep R d (steps.get j)
    (individualCentralIdealBefore R d steps I j)

/-- Adjacent boundary ideals are related by the selected individual central
step. -/
theorem individualCentralIdealBoundary_succ
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (j : Fin steps.length) :
    individualCentralIdealBoundary R d steps I j.succ =
      individualCentralIdealStep R d (steps.get j)
        (individualCentralIdealBoundary R d steps I j.castSucc) := by
  unfold individualCentralIdealBoundary
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [List.take_succ_eq_append_getElem j.isLt]
  rw [individualCentralIdealSteps_append]
  rfl

@[simp]
theorem individualCentralIdealAfter_eq_boundary
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (j : Fin steps.length) :
    individualCentralIdealAfter R d steps I j =
      individualCentralIdealBoundary R d steps I j.succ := by
  exact (individualCentralIdealBoundary_succ R d steps I j).symm

/-- One nonempty finite transfer family for every decrement in a fixed
balancing list. -/
structure IndividualCentralIdealTraceData
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) where
  transferData : (j : Fin steps.length) →
    IndividualCentralTransferData R d (steps.get j)
      (individualCentralIdealBefore R d steps I j)

/-- Noetherianity chooses the transfer data for all entries of the fixed
decrement list at once. -/
theorem nonempty_individualCentralIdealTraceData
    [Fintype Block] [IsNoetherianRing R]
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    Nonempty (IndividualCentralIdealTraceData R d steps I) := by
  classical
  let transferData := fun j : Fin steps.length ↦ Classical.choice
    (nonempty_individualCentralTransferData R d (steps.get j)
      (individualCentralIdealBefore R d steps I j))
  exact ⟨{ transferData := transferData }⟩

namespace IndividualCentralIdealTraceData

/-- Every certificate source at decrement `j` belongs to the coordinate-
translated curried before-ideal for that same decrement. -/
theorem source_mem_translated_before
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (data : IndividualCentralIdealTraceData R d steps I)
    (j : Fin steps.length)
    (a : Fin (data.transferData j).certificate.count) :
    (data.transferData j).certificate.source a ∈
      individualCentralTranslatedCurriedIdealBefore R d steps I j := by
  exact (data.transferData j).certificate.source_mem a

/-- The retained generators at decrement `j` span its indexed after-ideal. -/
theorem retained_span_eq_after
    [Fintype Block]
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (data : IndividualCentralIdealTraceData R d steps I)
    (j : Fin steps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.retainedGenerator R
        (data.transferData j))) =
      individualCentralIdealAfter R d steps I j := by
  exact IndividualCentralTransferData.retained_span_eq_step R
    (data.transferData j)

/-- Equivalently, the retained generators at decrement `j` span the next
boundary ideal of the fixed trace. -/
theorem retained_span_eq_boundary_succ
    [Fintype Block]
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (data : IndividualCentralIdealTraceData R d steps I)
    (j : Fin steps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.retainedGenerator R
        (data.transferData j))) =
      individualCentralIdealBoundary R d steps I j.succ := by
  exact (data.retained_span_eq_after R j).trans
    (individualCentralIdealAfter_eq_boundary R d steps I j)

end IndividualCentralIdealTraceData

end

end AbelFormalization
