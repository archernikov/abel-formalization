import AbelFormalization.OrderedClusterPrefixCurrying
import AbelFormalization.TerminalizedClusterIterationTraceData

/-!
# One retained logarithmic substitution in a selected block

The balancing phase performs logarithmic substitutions one representative at
a time, before the simultaneous operation on an entire cluster.  This module
constructs that algebraic operation on the common flat block ring.

The selected block is curried out as a one-block polynomial ring, all other
blocks become coefficients, the usual central ideal construction is applied,
and a fresh representative variable is adjoined again.  Uncurrying returns an
ideal in the original flat ring, ready for the next balancing decrement.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

universe u v

/-- Extending a ranged family along the right summand extends its span. -/
theorem individual_span_rename_inr_range
    {S X Q κ : Type*} [CommRing S]
    (g : κ → MvPolynomial X S) :
    Ideal.span (Set.range (fun k ↦
      MvPolynomial.rename (Sum.inr : X → Q ⊕ X) (g k))) =
      unusedPolynomialExtension Q (Ideal.span (Set.range g)) := by
  unfold unusedPolynomialExtension
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨g i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

section SelectedBlock

variable {Block : Type v} [DecidableEq Block]

/-- The blocks other than the selected block. -/
abbrev RemainingBlock (selected : Block) := {b : Block // b ≠ selected}

/-- Split a type into one selected element and its complement. -/
def selectedBlockSumEquiv (selected : Block) :
    Fin 1 ⊕ RemainingBlock selected ≃ Block where
  toFun
    | Sum.inl _ => selected
    | Sum.inr b => b.1
  invFun b := if h : b = selected then Sum.inl 0 else Sum.inr ⟨b, h⟩
  left_inv := by
    intro x
    rcases x with i | b
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp
    · simp [b.2]
  right_inv := by
    intro b
    by_cases h : b = selected
    · simp [h]
    · simp [h]

@[simp]
theorem selectedBlockSumEquiv_inl (selected : Block) (i : Fin 1) :
    selectedBlockSumEquiv selected (Sum.inl i) = selected :=
  rfl

@[simp]
theorem selectedBlockSumEquiv_inr (selected : Block)
    (b : RemainingBlock selected) :
    selectedBlockSumEquiv selected (Sum.inr b) = b.1 :=
  rfl

/-- The positive derivative count of the active singleton block. -/
def selectedBlockDerivativeCount (d : Block → ℕ) (selected : Block) :
    Fin 1 → ℕ :=
  fun _ => d selected

/-- The positive derivative counts of the coefficient blocks. -/
def remainingBlockDerivativeCount (d : Block → ℕ) (selected : Block) :
    RemainingBlock selected → ℕ :=
  fun b => d b.1

/-- Curry one selected block out of a flat block-operation ring. -/
def selectedBlockCurryAlgEquiv
    (R : Type u) [CommSemiring R]
    (d : Block → ℕ) (selected : Block) :
    MvPolynomial (ClusterOperationSymbol Block d) R ≃ₐ[R]
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (MvPolynomial
          (ClusterOperationSymbol (RemainingBlock selected)
            (remainingBlockDerivativeCount d selected)) R) := by
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
  exact
    (clusterOperationRenameAlgEquiv R e d dSplit hd).trans
      (splitClusterCurryAlgEquiv R (Fin 1)
        (RemainingBlock selected)
        (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected))

end SelectedBlock

section IndividualStep

variable (R : Type u) [CommRing R]
variable {Block : Type v} [Fintype Block] [DecidableEq Block]

/-- The coefficient ring obtained by retaining every block except the one
being logarithmically decremented. -/
abbrev IndividualCentralCoefficientRing
    (d : Block → ℕ) (selected : Block) :=
  MvPolynomial
    (ClusterOperationSymbol (RemainingBlock selected)
      (remainingBlockDerivativeCount d selected)) R

/-- The input ideal in the one-block curried coordinates. -/
def individualCentralCurriedIdeal
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (IndividualCentralCoefficientRing R d selected)) :=
  I.map (selectedBlockCurryAlgEquiv R d selected).toRingHom

/-- The central output after eliminating the old representative of the
selected block. -/
def individualCentralCoreIdeal
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    Ideal (CentralPolynomial
      (IndividualCentralCoefficientRing R d selected)
      (Fin 1) (selectedBlockDerivativeCount d selected) (Fin 1)) :=
  centralIdealConstruction
    (centralTransferShear (selectedBlockDerivativeCount d selected))
    (individualCentralCurriedIdeal R d selected I)

/-- One individual logarithmic substitution, with a fresh representative
variable adjoined before returning to the common flat block ring. -/
def individualCentralIdealStep
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    Ideal (MvPolynomial (ClusterOperationSymbol Block d) R) :=
  (unusedRepresentativeExtension
      (IndividualCentralCoefficientRing R d selected)
      (selectedBlockDerivativeCount d selected) (Fin 1)
      (individualCentralCoreIdeal R d selected I)).map
    (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom

theorem individualCentralCurriedIdeal_height
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    (individualCentralCurriedIdeal R d selected I).height = I.height :=
  (selectedBlockCurryAlgEquiv R d selected).toRingEquiv.height_map I

theorem individualCentralIdealStep_height_le
    [IsNoetherianRing R]
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    I.height ≤ (individualCentralIdealStep R d selected I).height := by
  let C := IndividualCentralCoefficientRing R d selected
  let d₁ := selectedBlockDerivativeCount d selected
  let J := individualCentralCurriedIdeal R d selected I
  let K := individualCentralCoreIdeal R d selected I
  have hIJ : I.height = J.height :=
    (individualCentralCurriedIdeal_height R d selected I).symm
  have hJK : J.height ≤ K.height := by
    exact centralIdealConstruction_height_le
      (centralTransferShear d₁) J
  have hKU :
      K.height =
        (unusedRepresentativeExtension C d₁ (Fin 1) K).height := by
    exact (unusedRepresentativeExtension_height C d₁ (Fin 1) K).symm
  have hUout :
      (unusedRepresentativeExtension C d₁ (Fin 1) K).height =
        (individualCentralIdealStep R d selected I).height := by
    exact
      ((selectedBlockCurryAlgEquiv R d selected).symm.toRingEquiv.height_map _).symm
  calc
    I.height = J.height := hIJ
    _ ≤ K.height := hJK
    _ = (unusedRepresentativeExtension C d₁ (Fin 1) K).height := hKU
    _ = (individualCentralIdealStep R d selected I).height := hUout

/-! ## Finite transfer data for the selected block -/

/-- A nonempty quantitative-transfer family for the curried one-block
operation.  Its coefficient ring contains every unselected block. -/
structure IndividualCentralTransferData
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) where
  certificate : CentralQuantitativeTransferCertificate
    (IndividualCentralCoefficientRing R d selected)
    (Fin 1) (Fin 1) (selectedBlockDerivativeCount d selected) 1
    (centralTransferShear (selectedBlockDerivativeCount d selected))
    (individualCentralCurriedIdeal R d selected I)
  source_nonempty : Nonempty (Fin certificate.count)

/-- Noetherianity supplies finite transfer data for every selected-block
operation, including when the current ideal is zero. -/
theorem nonempty_individualCentralTransferData
    [IsNoetherianRing R]
    (d : Block → ℕ) (selected : Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    Nonempty (IndividualCentralTransferData R d selected I) := by
  obtain ⟨certificate, hcount⟩ :=
    exists_nonempty_centralQuantitativeTransferCertificate
      (centralTransferShear (selectedBlockDerivativeCount d selected))
      (individualCentralCurriedIdeal R d selected I)
  exact ⟨{ certificate := certificate, source_nonempty := hcount }⟩

namespace IndividualCentralTransferData

/-- The canonical central generator produced from one certificate source. -/
def centralGenerator
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (data : IndividualCentralTransferData R d selected I)
    (a : Fin data.certificate.count) :
    CentralPolynomial (IndividualCentralCoefficientRing R d selected)
      (Fin 1) (selectedBlockDerivativeCount d selected) (Fin 1) :=
  centralPolynomialPhi (IndividualCentralCoefficientRing R d selected)
    (Fin 1) (selectedBlockDerivativeCount d selected) (Fin 1)
    (centralNormalizedInitialPolynomial
      (centralTransferShear (selectedBlockDerivativeCount d selected))
      (data.certificate.source a))

/-- Re-adjoin the fresh representative variable and uncurry a canonical
central generator back into the common flat block ring. -/
def retainedGenerator
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
  (data : IndividualCentralTransferData R d selected I)
    (a : Fin data.certificate.count) :
    MvPolynomial (ClusterOperationSymbol Block d) R :=
  (selectedBlockCurryAlgEquiv R d selected).symm
    (MvPolynomial.rename Sum.inr (centralGenerator R data a))

/-- The canonical certificate generators span the central core exactly. -/
theorem central_span_eq_core
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (data : IndividualCentralTransferData R d selected I) :
    Ideal.span (Set.range (centralGenerator R data)) =
      individualCentralCoreIdeal R d selected I := by
  exact data.certificate.central_span

/-- After the fresh representative is re-adjoined and the variables are
uncurried, the same canonical family spans the literal one-block output
ideal. -/
theorem retained_span_eq_step
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (data : IndividualCentralTransferData R d selected I) :
    Ideal.span (Set.range (retainedGenerator R data)) =
      individualCentralIdealStep R d selected I := by
  let C := IndividualCentralCoefficientRing R d selected
  let d₁ := selectedBlockDerivativeCount d selected
  have hrename :
      Ideal.span (Set.range (fun a =>
        MvPolynomial.rename
          (Sum.inr : CentralPolynomialIndex (Fin 1) d₁ (Fin 1) →
            Fin 1 ⊕ CentralPolynomialIndex (Fin 1) d₁ (Fin 1))
          (centralGenerator R data a))) =
        unusedRepresentativeExtension C d₁ (Fin 1)
          (Ideal.span (Set.range (centralGenerator R data))) := by
    simpa only [unusedRepresentativeExtension] using
      (individual_span_rename_inr_range
        (Q := Fin 1) (g := centralGenerator R data))
  change Ideal.span (Set.range (fun a =>
      (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom
        (MvPolynomial.rename Sum.inr (centralGenerator R data a)))) = _
  calc
    Ideal.span (Set.range (fun a =>
        (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom
          (MvPolynomial.rename Sum.inr (centralGenerator R data a)))) =
        (Ideal.span (Set.range (fun a =>
          MvPolynomial.rename Sum.inr (centralGenerator R data a)))).map
          (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom :=
      span_range_map_eq _ _
    _ = (unusedRepresentativeExtension C d₁ (Fin 1)
          (Ideal.span (Set.range (centralGenerator R data)))).map
          (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom :=
      congrArg (fun J => J.map
        (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom) hrename
    _ = (unusedRepresentativeExtension C d₁ (Fin 1)
          (individualCentralCoreIdeal R d selected I)).map
          (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom :=
      congrArg (fun J =>
        (unusedRepresentativeExtension C d₁ (Fin 1) J).map
          (selectedBlockCurryAlgEquiv R d selected).symm.toRingHom)
        (central_span_eq_core R data)
    _ = individualCentralIdealStep R d selected I := rfl

end IndividualCentralTransferData

/-- Apply a fixed list of balancing decrements in chronological order. -/
def individualCentralIdealSteps
    (d : Block → ℕ) :
    List Block → Ideal (MvPolynomial (ClusterOperationSymbol Block d) R) →
      Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)
  | [], I => I
  | selected :: steps, I =>
      individualCentralIdealSteps d steps
        (individualCentralIdealStep R d selected I)

@[simp]
theorem individualCentralIdealSteps_nil
    (d : Block → ℕ)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    individualCentralIdealSteps R d [] I = I :=
  rfl

@[simp]
theorem individualCentralIdealSteps_cons
    (d : Block → ℕ) (selected : Block) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    individualCentralIdealSteps R d (selected :: steps) I =
      individualCentralIdealSteps R d steps
        (individualCentralIdealStep R d selected I) :=
  rfl

theorem individualCentralIdealSteps_height_le
    [IsNoetherianRing R]
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)) :
    I.height ≤ (individualCentralIdealSteps R d steps I).height := by
  induction steps generalizing I with
  | nil => exact le_rfl
  | cons selected steps ih =>
      exact (individualCentralIdealStep_height_le R d selected I).trans
        (ih (individualCentralIdealStep R d selected I))

end IndividualStep

end AbelFormalization
