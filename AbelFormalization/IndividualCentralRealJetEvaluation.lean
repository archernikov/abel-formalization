import AbelFormalization.IndividualCentralRealJetIdentities

/-!
# Evaluation of one individual central step

This module connects the flat selected-block presentation to the one-block
real-jet evaluation used by a central transfer certificate.  It first splits
an arbitrary flat assignment into its selected active block and its remaining
coefficient blocks.  It then records the two evaluations relevant to one
logarithmic decrement: the input coordinates at `E u` and the output central
coordinates at `u`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

universe u v w

section AssignmentSplit

variable {R : Type u} [CommRing R]
variable {S : Type w}
variable {Block : Type v} [DecidableEq Block]

/-- The variable equivalence underlying `selectedBlockCurryAlgEquiv`, before
the final polynomial currying step. -/
def selectedBlockSplitOperationEquiv
    (d : Block → ℕ) (selected : Block) :
    ClusterOperationSymbol Block d ≃
      SplitClusterBlockSymbol (Fin 1) (RemainingBlock selected)
        (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected) := by
  let e : Block ≃ Fin 1 ⊕ RemainingBlock selected :=
    (selectedBlockSumEquiv selected).symm
  let dSplit : Fin 1 ⊕ RemainingBlock selected → ℕ :=
    Sum.elim (selectedBlockDerivativeCount d selected)
      (remainingBlockDerivativeCount d selected)
  have hd : ∀ b, d b = dSplit (e b) := by
    intro b
    by_cases h : b = selected
    · subst b
      simp [e, dSplit, selectedBlockSumEquiv,
        selectedBlockDerivativeCount]
    · simp [e, dSplit, selectedBlockSumEquiv, h,
        remainingBlockDerivativeCount]
  exact clusterOperationSymbolEquiv e d dSplit hd

/-- The selected singleton part of a flat block assignment. -/
def selectedBlockActiveAssignment
    (d : Block → ℕ) (selected : Block)
    (value : ClusterOperationSymbol Block d → S) :
    ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount d selected) → S :=
  fun z ↦ value
    ((selectedBlockSplitOperationEquiv d selected).symm
      ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
        (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected)).symm (Sum.inl z)))

/-- The unselected part of a flat block assignment.  These values evaluate
the coefficient polynomial ring after the selected block is curried out. -/
def selectedBlockCoefficientAssignment
    (d : Block → ℕ) (selected : Block)
    (value : ClusterOperationSymbol Block d → S) :
    ClusterOperationSymbol (RemainingBlock selected)
      (remainingBlockDerivativeCount d selected) → S :=
  fun z ↦ value
    ((selectedBlockSplitOperationEquiv d selected).symm
      ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
        (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected)).symm (Sum.inr z)))

/-- Join a selected-block assignment and a remaining-block assignment into a
flat assignment.  This is the inverse operation to the two restrictions
`selectedBlockActiveAssignment` and `selectedBlockCoefficientAssignment`. -/
def selectedBlockJoinedAssignment
    (d : Block → ℕ) (selected : Block)
    (active : ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount d selected) → S)
    (coefficient : ClusterOperationSymbol (RemainingBlock selected)
      (remainingBlockDerivativeCount d selected) → S) :
    ClusterOperationSymbol Block d → S :=
  fun z ↦ Sum.elim active coefficient
    (splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
      (selectedBlockDerivativeCount d selected)
      (remainingBlockDerivativeCount d selected)
      (selectedBlockSplitOperationEquiv d selected z))

/-- Restricting a joined assignment to its selected block recovers the active
assignment literally. -/
@[simp]
theorem selectedBlockActiveAssignment_joined
    (d : Block → ℕ) (selected : Block)
    (active : ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount d selected) → S)
    (coefficient : ClusterOperationSymbol (RemainingBlock selected)
      (remainingBlockDerivativeCount d selected) → S) :
    selectedBlockActiveAssignment d selected
        (selectedBlockJoinedAssignment d selected active coefficient) =
      active := by
  funext z
  simp [selectedBlockActiveAssignment, selectedBlockJoinedAssignment]

/-- Restricting a joined assignment to the remaining blocks recovers the
coefficient assignment literally. -/
@[simp]
theorem selectedBlockCoefficientAssignment_joined
    (d : Block → ℕ) (selected : Block)
    (active : ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount d selected) → S)
    (coefficient : ClusterOperationSymbol (RemainingBlock selected)
      (remainingBlockDerivativeCount d selected) → S) :
    selectedBlockCoefficientAssignment d selected
        (selectedBlockJoinedAssignment d selected active coefficient) =
      coefficient := by
  funext z
  simp [selectedBlockCoefficientAssignment, selectedBlockJoinedAssignment]

/-- Evaluation of the coefficient ring at the unselected part of a flat
assignment. -/
def selectedBlockCoefficientEvaluationHom
    [CommSemiring S]
    (c : R →+* S) (d : Block → ℕ) (selected : Block)
    (value : ClusterOperationSymbol Block d → S) :
    IndividualCentralCoefficientRing R d selected →+* S :=
  MvPolynomial.eval₂Hom c
    (selectedBlockCoefficientAssignment d selected value)

/-- A flat assignment is recovered by joining its selected and unselected
restrictions along the two equivalences used by selected-block currying. -/
theorem selectedBlockAssignment_eq_sum_elim
    (d : Block → ℕ) (selected : Block)
    (value : ClusterOperationSymbol Block d → S)
    (z : ClusterOperationSymbol Block d) :
    Sum.elim
        (selectedBlockActiveAssignment d selected value)
        (selectedBlockCoefficientAssignment d selected value)
        (splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
          (selectedBlockDerivativeCount d selected)
          (remainingBlockDerivativeCount d selected)
          (selectedBlockSplitOperationEquiv d selected z)) =
      value z := by
  let split := selectedBlockSplitOperationEquiv d selected
  let currySplit := splitClusterBlockSymbolEquiv
    (Fin 1) (RemainingBlock selected)
    (selectedBlockDerivativeCount d selected)
    (remainingBlockDerivativeCount d selected)
  generalize h : currySplit (split z) = y
  rcases y with a | b
  · change value (split.symm (currySplit.symm (Sum.inl a))) = value z
    rw [← h, currySplit.symm_apply_apply, split.symm_apply_apply]
  · change value (split.symm (currySplit.symm (Sum.inr b))) = value z
    rw [← h, currySplit.symm_apply_apply, split.symm_apply_apply]

/-- Evaluation in the flat block ring is evaluation in the selected block
over the coefficient-ring evaluation of all remaining blocks. -/
theorem eval₂Hom_selectedBlockCurryAlgEquiv
    [CommSemiring S]
    (c : R →+* S) (d : Block → ℕ) (selected : Block)
    (value : ClusterOperationSymbol Block d → S)
    (P : MvPolynomial (ClusterOperationSymbol Block d) R) :
    MvPolynomial.eval₂Hom c value P =
      MvPolynomial.eval₂Hom
        (selectedBlockCoefficientEvaluationHom c d selected value)
        (selectedBlockActiveAssignment d selected value)
        (selectedBlockCurryAlgEquiv R d selected P) := by
  let split := selectedBlockSplitOperationEquiv d selected
  let splitValue : SplitClusterBlockSymbol (Fin 1)
      (RemainingBlock selected) (selectedBlockDerivativeCount d selected)
      (remainingBlockDerivativeCount d selected) → S :=
    fun z ↦ Sum.elim
      (selectedBlockActiveAssignment d selected value)
      (selectedBlockCoefficientAssignment d selected value)
      (splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
        (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected) z)
  have hrename :
      MvPolynomial.eval₂Hom c value P =
        MvPolynomial.eval₂Hom c splitValue (MvPolynomial.rename split P) := by
    rw [MvPolynomial.eval₂Hom_rename]
    apply DFunLike.congr_fun
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro z
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      change value z = splitValue (split z)
      exact (selectedBlockAssignment_eq_sum_elim d selected value z).symm
  calc
    MvPolynomial.eval₂Hom c value P =
        MvPolynomial.eval₂Hom c splitValue (MvPolynomial.rename split P) :=
      hrename
    _ = MvPolynomial.eval₂Hom
          (MvPolynomial.eval₂Hom c
            (selectedBlockCoefficientAssignment d selected value))
          (selectedBlockActiveAssignment d selected value)
          (splitClusterCurryAlgEquiv R (Fin 1) (RemainingBlock selected)
            (selectedBlockDerivativeCount d selected)
            (remainingBlockDerivativeCount d selected)
            (MvPolynomial.rename split P)) :=
      eval₂Hom_splitClusterCurryAlgEquiv c (Fin 1)
        (RemainingBlock selected) (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected)
        (selectedBlockActiveAssignment d selected value)
        (selectedBlockCoefficientAssignment d selected value)
        (MvPolynomial.rename split P)
    _ = _ := by
      rfl

end AssignmentSplit

section RealJetValues

/-- Values in the selected flat block immediately before one logarithmic
decrement.  The representative coordinate is `E u = exp u - 1`; the other
coordinates are the literal source jets and source time value at `E u`. -/
def individualCentralPreLogActiveAssignment
    {A : ℝ → ℝ} (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    ClusterOperationSymbol (Fin 1) d → ℕ → ℝ
  | Sum.inl i, n => E (u i n)
  | Sum.inr x, n =>
      realCentralTransferActualValue A (fun i ↦ u i n) d (jets n)
        (Sum.inr x)

/-- Values in the selected flat block after the logarithmic decrement.  The
fresh representative is assigned `u`; the retained central variables are
evaluated at the derivative and time coordinates at `u`. -/
def individualCentralPostLogActiveAssignment
    (A : ℝ → ℝ) (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ) :
    ClusterOperationSymbol (Fin 1) d → ℕ → ℝ
  | Sum.inl i, n => u i n
  | Sum.inr x, n =>
      realCentralTransferCentralValue A (fun i ↦ u i n) d x

@[simp]
theorem individualCentralPreLogActiveAssignment_q
    {A : ℝ → ℝ} (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (i : Fin 1) (n : ℕ) :
    individualCentralPreLogActiveAssignment u d jets (Sum.inl i) n =
      E (u i n) :=
  rfl

@[simp]
theorem individualCentralPreLogActiveAssignment_central
    {A : ℝ → ℝ} (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (x : CentralPolynomialIndex (Fin 1) d (Fin 1)) (n : ℕ) :
    individualCentralPreLogActiveAssignment u d jets (Sum.inr x) n =
      realCentralTransferActualValue A (fun i ↦ u i n) d (jets n)
        (Sum.inr x) :=
  rfl

@[simp]
theorem individualCentralPostLogActiveAssignment_q
    (A : ℝ → ℝ) (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ)
    (i : Fin 1) (n : ℕ) :
    individualCentralPostLogActiveAssignment A u d (Sum.inl i) n =
      u i n :=
  rfl

@[simp]
theorem individualCentralPostLogActiveAssignment_central
    (A : ℝ → ℝ) (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ)
    (x : CentralPolynomialIndex (Fin 1) d (Fin 1)) (n : ℕ) :
    individualCentralPostLogActiveAssignment A u d (Sum.inr x) n =
      realCentralTransferCentralValue A (fun i ↦ u i n) d x :=
  rfl

end RealJetValues

section TranslationEvaluation

variable (R : Type u) [CommRing R]
variable {Block : Type v}

/-- Undoing the source translation at the pre-log assignment changes the
selected representative value from `E u` to the literal source value
`exp u`.  Thus it is exactly the existing one-block real-jet source
evaluation homomorphism. -/
theorem eval₂Hom_sourceTranslation_symm_preLog
    {d : Block → ℕ} (selected : Block)
    {A : ℝ → ℝ}
    (coefficientEval :
      IndividualCentralCoefficientRing R d selected →+* (ℕ → ℝ))
    (u : Fin 1 → ℕ → ℝ)
    (jets : ∀ n i,
      RealCentralJetSubstitutionData A (u i n)
        (selectedBlockDerivativeCount d selected i))
    (P : MvPolynomial
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (IndividualCentralCoefficientRing R d selected))
    (n : ℕ) :
    MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
        (fun z ↦ individualCentralPreLogActiveAssignment u
          (selectedBlockDerivativeCount d selected) jets z n)
        ((IndividualCentralTransferData.sourceTranslation R selected).symm P) =
      realJetSourceEvaluationHom coefficientEval u
        (selectedBlockDerivativeCount d selected) jets n P := by
  let pre := individualCentralPreLogActiveAssignment u
    (selectedBlockDerivativeCount d selected) jets
  let lhs : MvPolynomial
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (IndividualCentralCoefficientRing R d selected) →+* ℝ :=
    (MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
      (fun z ↦ pre z n)).comp
        (IndividualCentralTransferData.sourceTranslation R selected).symm.toRingHom
  let rhs := realJetSourceEvaluationHom coefficientEval u
    (selectedBlockDerivativeCount d selected) jets n
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, IndividualCentralTransferData.sourceTranslation,
        polynomialCoordinateTranslation]
      dsimp only [rhs, realJetSourceEvaluationHom]
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    · intro z
      rcases z with i | x
      · simp [lhs, rhs, pre,
          IndividualCentralTransferData.sourceTranslation,
          polynomialCoordinateTranslation, realJetSourceEvaluationHom,
          realJetActualAssignment, realCentralTransferActualValue, E]
      · simp [lhs, rhs, pre,
          IndividualCentralTransferData.sourceTranslation,
          polynomialCoordinateTranslation, realJetSourceEvaluationHom,
          realJetActualAssignment]
  exact RingHom.congr_fun hhom P

/-- Re-adjoining the unused representative and evaluating at post-log values
is exactly evaluation by the existing one-block central real-jet hom. -/
theorem eval₂Hom_rename_inr_postLog
    {d : Block → ℕ} (selected : Block)
    (A : ℝ → ℝ)
    (coefficientEval :
      IndividualCentralCoefficientRing R d selected →+* (ℕ → ℝ))
    (u : Fin 1 → ℕ → ℝ)
    (P : CentralPolynomial (IndividualCentralCoefficientRing R d selected)
      (Fin 1) (selectedBlockDerivativeCount d selected) (Fin 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
        (fun z ↦ individualCentralPostLogActiveAssignment A u
          (selectedBlockDerivativeCount d selected) z n)
        (MvPolynomial.rename Sum.inr P) =
      realJetCentralEvaluationHom A coefficientEval u
        (selectedBlockDerivativeCount d selected) n P := by
  rw [MvPolynomial.eval₂Hom_rename]
  rfl

end TranslationEvaluation

namespace IndividualCentralTransferData.DisplayedData

variable (R : Type u) [CommRing R]
variable {Block : Type v} [DecidableEq Block]

/-- Evaluation of a displayed flat input generator at pre-log coordinates
is the literal source-side real-jet evaluation of its translated, curried
generator.  The coefficient hom is obtained canonically by evaluating all
unselected blocks of the same flat assignment. -/
theorem eval_beforeGenerator_preLog
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : IndividualCentralTransferData.DisplayedData R transferData)
    {A : ℝ → ℝ} (c : R →+* (ℕ → ℝ))
    (flatValue : ClusterOperationSymbol Block d → ℕ → ℝ)
    (u : Fin 1 → ℕ → ℝ)
    (jets : ∀ n i,
      RealCentralJetSubstitutionData A (u i n)
        (selectedBlockDerivativeCount d selected i))
    (hactive : selectedBlockActiveAssignment d selected flatValue =
      individualCentralPreLogActiveAssignment u
        (selectedBlockDerivativeCount d selected) jets)
    (k : Fin (data.source.count + 1)) (n : ℕ) :
    MvPolynomial.eval₂Hom c flatValue (beforeGenerator R data k) n =
      realJetSourceEvaluationHom
        (selectedBlockCoefficientEvaluationHom c d selected flatValue)
        u (selectedBlockDerivativeCount d selected) jets n
        (data.source.generator k) := by
  let coefficientEval :=
    selectedBlockCoefficientEvaluationHom c d selected flatValue
  calc
    MvPolynomial.eval₂Hom c flatValue (beforeGenerator R data k) n =
        MvPolynomial.eval₂Hom coefficientEval
          (selectedBlockActiveAssignment d selected flatValue)
          ((IndividualCentralTransferData.sourceTranslation R selected).symm
            (data.source.generator k)) n := by
      have h := congrFun
        (eval₂Hom_selectedBlockCurryAlgEquiv c d selected flatValue
          (beforeGenerator R data k)) n
      simpa [coefficientEval, beforeGenerator] using h
    _ = MvPolynomial.eval₂Hom
          (coefficientEvaluationAt coefficientEval n)
          (fun z ↦ individualCentralPreLogActiveAssignment u
            (selectedBlockDerivativeCount d selected) jets z n)
          ((IndividualCentralTransferData.sourceTranslation R selected).symm
            (data.source.generator k)) := by
      rw [hactive]
      exact mvPolynomial_eval₂Hom_pi_apply coefficientEval
        (individualCentralPreLogActiveAssignment u
          (selectedBlockDerivativeCount d selected) jets)
        ((IndividualCentralTransferData.sourceTranslation R selected).symm
          (data.source.generator k)) n
    _ = realJetSourceEvaluationHom coefficientEval u
          (selectedBlockDerivativeCount d selected) jets n
          (data.source.generator k) :=
      eval₂Hom_sourceTranslation_symm_preLog R selected coefficientEval u jets
        (data.source.generator k) n

/-- Evaluation of a displayed flat output generator at post-log coordinates
is the canonical central real-jet evaluation of its central generator.  As
on the source side, all other blocks are evaluated through the coefficient
ring hom induced by the flat assignment. -/
theorem eval_afterGenerator_postLog
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : IndividualCentralTransferData.DisplayedData R transferData)
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (flatValue : ClusterOperationSymbol Block d → ℕ → ℝ)
    (u : Fin 1 → ℕ → ℝ)
    (hactive : selectedBlockActiveAssignment d selected flatValue =
      individualCentralPostLogActiveAssignment A u
        (selectedBlockDerivativeCount d selected))
    (k : Fin (data.central.count + 1)) (n : ℕ) :
    MvPolynomial.eval₂Hom c flatValue (afterGenerator R data k) n =
      realJetCentralEvaluationHom A
        (selectedBlockCoefficientEvaluationHom c d selected flatValue)
        u (selectedBlockDerivativeCount d selected) n
        (data.central.generator k) := by
  let coefficientEval :=
    selectedBlockCoefficientEvaluationHom c d selected flatValue
  calc
    MvPolynomial.eval₂Hom c flatValue (afterGenerator R data k) n =
        MvPolynomial.eval₂Hom coefficientEval
          (selectedBlockActiveAssignment d selected flatValue)
          (MvPolynomial.rename Sum.inr (data.central.generator k)) n := by
      have h := congrFun
        (eval₂Hom_selectedBlockCurryAlgEquiv c d selected flatValue
          (afterGenerator R data k)) n
      simpa [coefficientEval, afterGenerator] using h
    _ = MvPolynomial.eval₂Hom
          (coefficientEvaluationAt coefficientEval n)
          (fun z ↦ individualCentralPostLogActiveAssignment A u
            (selectedBlockDerivativeCount d selected) z n)
          (MvPolynomial.rename Sum.inr (data.central.generator k)) := by
      rw [hactive]
      exact mvPolynomial_eval₂Hom_pi_apply coefficientEval
        (individualCentralPostLogActiveAssignment A u
          (selectedBlockDerivativeCount d selected))
        (MvPolynomial.rename Sum.inr (data.central.generator k)) n
    _ = realJetCentralEvaluationHom A coefficientEval u
          (selectedBlockDerivativeCount d selected) n
          (data.central.generator k) :=
      eval₂Hom_rename_inr_postLog R selected A coefficientEval u
        (data.central.generator k) n

end IndividualCentralTransferData.DisplayedData

end AbelFormalization
