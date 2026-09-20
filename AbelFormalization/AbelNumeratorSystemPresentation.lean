import AbelFormalization.AbelNumeratorPolynomialPresentation

/-!
# One finite Abel-jet presentation for a square numerator system

The individual finite generator lists are combined through their sigma type
and its canonical finite equivalence.  The resulting single `Fin b` list is
shared by every row of the square system.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- One common finite polynomial presentation for every row of a square
numerator system. -/
structure AbelNumeratorSystemPolynomialPresentation
    (A : ℝ → ℝ) {n : ℕ} (F : Fin n → RealEuclideanFunction n) where
  generatorCount : ℕ
  derivativeOrder : Fin generatorCount → ℕ
  argument : Fin generatorCount → (RealEuclidean n →ᵃ[ℝ] ℝ)
  polynomial : Fin n → MvPolynomial (Fin n ⊕ Fin generatorCount) ℝ
  eval_eq : ∀ i x,
    MvPolynomial.eval
      (Sum.elim x (fun j ↦ Cr A (derivativeOrder j) (argument j x)))
      (polynomial i) = F i x

namespace AbelNumeratorSystemPolynomialPresentation

variable {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}

/-- The disjoint union of all rowwise generator lists. -/
abbrev TotalGeneratorIndex
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i)) :=
  Σ i, Fin (P i).generatorCount

/-- Canonical enumeration of the disjoint union by one `Fin`. -/
noncomputable def totalGeneratorEquiv
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i)) :
    TotalGeneratorIndex P ≃ Fin (Fintype.card (TotalGeneratorIndex P)) :=
  Fintype.equivFin _

/-- The derivative order attached to a generator in the common enumeration. -/
noncomputable def totalDerivativeOrder
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i))
    (k : Fin (Fintype.card (TotalGeneratorIndex P))) : ℕ :=
  let ij := (totalGeneratorEquiv P).symm k
  (P ij.1).derivativeOrder ij.2

/-- The affine argument attached to a generator in the common enumeration. -/
noncomputable def totalArgument
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i))
    (k : Fin (Fintype.card (TotalGeneratorIndex P))) :
    RealEuclidean n →ᵃ[ℝ] ℝ :=
  let ij := (totalGeneratorEquiv P).symm k
  (P ij.1).argument ij.2

/-- Relabel the variables of row `i` into the common enumeration. -/
noncomputable def rowVariableMap
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i)) (i : Fin n) :
    Fin n ⊕ Fin (P i).generatorCount →
      Fin n ⊕ Fin (Fintype.card (TotalGeneratorIndex P)) :=
  Sum.map id (fun j ↦ totalGeneratorEquiv P ⟨i, j⟩)

@[simp]
theorem totalDerivativeOrder_apply
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i))
    (i : Fin n) (j : Fin (P i).generatorCount) :
    totalDerivativeOrder P (totalGeneratorEquiv P ⟨i, j⟩) =
      (P i).derivativeOrder j := by
  unfold totalDerivativeOrder
  rw [(totalGeneratorEquiv P).symm_apply_apply ⟨i, j⟩]

@[simp]
theorem totalArgument_apply
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i))
    (i : Fin n) (j : Fin (P i).generatorCount) :
    totalArgument P (totalGeneratorEquiv P ⟨i, j⟩) =
      (P i).argument j := by
  unfold totalArgument
  rw [(totalGeneratorEquiv P).symm_apply_apply ⟨i, j⟩]

/-- Combine a chosen rowwise presentation family into one common list. -/
noncomputable def ofRowPresentations
    (P : ∀ i, AbelNumeratorPolynomialPresentation A (F i)) :
    AbelNumeratorSystemPolynomialPresentation A F where
  generatorCount := Fintype.card (TotalGeneratorIndex P)
  derivativeOrder := totalDerivativeOrder P
  argument := totalArgument P
  polynomial := fun i ↦ MvPolynomial.rename (rowVariableMap P i) (P i).polynomial
  eval_eq := by
    intro i x
    rw [MvPolynomial.eval_rename]
    have hvalue :
        ((Sum.elim x fun j ↦ Cr A (totalDerivativeOrder P j)
            (totalArgument P j x)) ∘ rowVariableMap P i) =
          (P i).variableValue x := by
      funext z
      rcases z with k | j
      · rfl
      · simp [rowVariableMap,
          AbelNumeratorPolynomialPresentation.variableValue]
    rw [hvalue, (P i).eval_polynomial x]

end AbelNumeratorSystemPolynomialPresentation

/-- Every finite square tuple of numerator expressions admits one common
finite Abel-jet list and a polynomial for each row. -/
theorem nonempty_abelNumeratorSystemPolynomialPresentation
    {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (hF : ∀ i, AbelNumerator A n (F i)) :
    Nonempty (AbelNumeratorSystemPolynomialPresentation A F) := by
  classical
  let P : ∀ i, AbelNumeratorPolynomialPresentation A (F i) :=
    fun i ↦ Classical.choice ((hF i).nonempty_polynomialPresentation)
  exact ⟨AbelNumeratorSystemPolynomialPresentation.ofRowPresentations P⟩

end AbelFormalization
