import AbelFormalization.AbelGeometricFamily
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Finite polynomial presentations of Abel numerator expressions

Every numerator expression uses only finitely many affine Abel-jet generators.
This file packages those generators by a `Fin b` index and represents the
whole expression by one multivariable polynomial in the ordinary coordinates
and the selected jet values.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- A finite polynomial presentation of one Abel numerator expression. -/
structure AbelNumeratorPolynomialPresentation
    (A : ℝ → ℝ) {n : ℕ} (f : RealEuclideanFunction n) where
  generatorCount : ℕ
  derivativeOrder : Fin generatorCount → ℕ
  argument : Fin generatorCount → (RealEuclidean n →ᵃ[ℝ] ℝ)
  polynomial : MvPolynomial (Fin n ⊕ Fin generatorCount) ℝ
  eval_eq : ∀ x,
    MvPolynomial.eval
      (Sum.elim x (fun j ↦ Cr A (derivativeOrder j) (argument j x)))
      polynomial = f x

namespace AbelNumeratorPolynomialPresentation

variable {A : ℝ → ℝ} {n : ℕ} {f g : RealEuclideanFunction n}

/-- The valuation of all ordinary and selected-jet variables. -/
def variableValue (P : AbelNumeratorPolynomialPresentation A f)
    (x : RealEuclidean n) : Fin n ⊕ Fin P.generatorCount → ℝ :=
  Sum.elim x (fun j ↦ Cr A (P.derivativeOrder j) (P.argument j x))

@[simp]
theorem eval_polynomial (P : AbelNumeratorPolynomialPresentation A f)
    (x : RealEuclidean n) :
    MvPolynomial.eval (P.variableValue x) P.polynomial = f x :=
  P.eval_eq x

/-- Relabel the generators of the left presentation into the first block. -/
def leftVariableMap (P : AbelNumeratorPolynomialPresentation A f)
    (Q : AbelNumeratorPolynomialPresentation A g) :
    Fin n ⊕ Fin P.generatorCount →
      Fin n ⊕ Fin (P.generatorCount + Q.generatorCount) :=
  Sum.map id (Fin.castAdd Q.generatorCount)

/-- Relabel the generators of the right presentation into the second block. -/
def rightVariableMap (P : AbelNumeratorPolynomialPresentation A f)
    (Q : AbelNumeratorPolynomialPresentation A g) :
    Fin n ⊕ Fin Q.generatorCount →
      Fin n ⊕ Fin (P.generatorCount + Q.generatorCount) :=
  Sum.map id (Fin.natAdd P.generatorCount)

def sumDerivativeOrder (P : AbelNumeratorPolynomialPresentation A f)
    (Q : AbelNumeratorPolynomialPresentation A g) :
    Fin (P.generatorCount + Q.generatorCount) → ℕ :=
  Fin.addCases P.derivativeOrder Q.derivativeOrder

def sumArgument (P : AbelNumeratorPolynomialPresentation A f)
    (Q : AbelNumeratorPolynomialPresentation A g) :
    Fin (P.generatorCount + Q.generatorCount) →
      (RealEuclidean n →ᵃ[ℝ] ℝ) :=
  Fin.addCases P.argument Q.argument

/-- Combine two finite presentations using addition. -/
def add (P : AbelNumeratorPolynomialPresentation A f)
    (Q : AbelNumeratorPolynomialPresentation A g) :
    AbelNumeratorPolynomialPresentation A (f + g) where
  generatorCount := P.generatorCount + Q.generatorCount
  derivativeOrder := sumDerivativeOrder P Q
  argument := sumArgument P Q
  polynomial :=
    MvPolynomial.rename (leftVariableMap P Q) P.polynomial +
      MvPolynomial.rename (rightVariableMap P Q) Q.polynomial
  eval_eq := by
    intro x
    rw [map_add, MvPolynomial.eval_rename, MvPolynomial.eval_rename]
    have hleft :
        ((Sum.elim x fun j ↦
            Cr A (sumDerivativeOrder P Q j)
              (sumArgument P Q j x)) ∘
          leftVariableMap P Q) = P.variableValue x := by
      funext z
      rcases z with i | j
      · rfl
      · simp [variableValue, leftVariableMap, sumDerivativeOrder, sumArgument]
    have hright :
        ((Sum.elim x fun j ↦
            Cr A (sumDerivativeOrder P Q j)
              (sumArgument P Q j x)) ∘
          rightVariableMap P Q) = Q.variableValue x := by
      funext z
      rcases z with i | j
      · rfl
      · simp [variableValue, rightVariableMap, sumDerivativeOrder, sumArgument]
    rw [hleft, hright, P.eval_polynomial x, Q.eval_polynomial x]
    rfl

/-- Combine two finite presentations using multiplication. -/
def mul (P : AbelNumeratorPolynomialPresentation A f)
    (Q : AbelNumeratorPolynomialPresentation A g) :
    AbelNumeratorPolynomialPresentation A (f * g) where
  generatorCount := P.generatorCount + Q.generatorCount
  derivativeOrder := sumDerivativeOrder P Q
  argument := sumArgument P Q
  polynomial :=
    MvPolynomial.rename (leftVariableMap P Q) P.polynomial *
      MvPolynomial.rename (rightVariableMap P Q) Q.polynomial
  eval_eq := by
    intro x
    rw [map_mul, MvPolynomial.eval_rename, MvPolynomial.eval_rename]
    have hleft :
        ((Sum.elim x fun j ↦
            Cr A (sumDerivativeOrder P Q j)
              (sumArgument P Q j x)) ∘
          leftVariableMap P Q) = P.variableValue x := by
      funext z
      rcases z with i | j
      · rfl
      · simp [variableValue, leftVariableMap, sumDerivativeOrder, sumArgument]
    have hright :
        ((Sum.elim x fun j ↦
            Cr A (sumDerivativeOrder P Q j)
              (sumArgument P Q j x)) ∘
          rightVariableMap P Q) = Q.variableValue x := by
      funext z
      rcases z with i | j
      · rfl
      · simp [variableValue, rightVariableMap, sumDerivativeOrder, sumArgument]
    rw [hleft, hright, P.eval_polynomial x, Q.eval_polynomial x]
    rfl

/-- The polynomial substituted for an old variable after affine composition. -/
def affineCompVariablePolynomial {m : ℕ}
    (P : AbelNumeratorPolynomialPresentation A f)
    (ell : RealEuclidean m →ᵃ[ℝ] RealEuclidean n) :
    Fin n ⊕ Fin P.generatorCount →
      MvPolynomial (Fin m ⊕ Fin P.generatorCount) ℝ
  | Sum.inl i =>
      MvPolynomial.rename Sum.inl
        (affinePolynomial ((AffineMap.proj i).comp ell))
  | Sum.inr j => MvPolynomial.X (Sum.inr j)

/-- Affine precomposition preserves finite polynomial presentation. -/
def affineComp {m : ℕ}
    (P : AbelNumeratorPolynomialPresentation A f)
    (ell : RealEuclidean m →ᵃ[ℝ] RealEuclidean n) :
    AbelNumeratorPolynomialPresentation A (f ∘ ell) where
  generatorCount := P.generatorCount
  derivativeOrder := P.derivativeOrder
  argument := fun j ↦ P.argument j |>.comp ell
  polynomial := MvPolynomial.bind₁ (affineCompVariablePolynomial P ell)
    P.polynomial
  eval_eq := by
    intro x
    unfold MvPolynomial.eval
    rw [MvPolynomial.eval₂Hom_bind₁]
    change MvPolynomial.eval₂Hom (RingHom.id ℝ) _ P.polynomial = f (ell x)
    rw [← P.eval_eq (ell x)]
    unfold MvPolynomial.eval
    apply congrArg (fun v ↦ MvPolynomial.eval₂Hom (RingHom.id ℝ) v P.polynomial)
    funext z
    rcases z with i | j
    · rw [affineCompVariablePolynomial, MvPolynomial.eval₂Hom_rename]
      change MvPolynomial.eval x
        (affinePolynomial ((AffineMap.proj i).comp ell)) = ell x i
      rw [eval_affinePolynomial]
      rfl
    · simp [affineCompVariablePolynomial]

end AbelNumeratorPolynomialPresentation

/-- Every finite Abel numerator expression has a finite polynomial
presentation by affine Abel-jet generators. -/
theorem AbelNumerator.nonempty_polynomialPresentation
    {A : ℝ → ℝ} {n : ℕ} {f : RealEuclideanFunction n}
    (hf : AbelNumerator A n f) :
    Nonempty (AbelNumeratorPolynomialPresentation A f) := by
  induction hf with
  | polynomial P =>
      exact ⟨{
        generatorCount := 0
        derivativeOrder := Fin.elim0
        argument := Fin.elim0
        polynomial := MvPolynomial.rename Sum.inl P
        eval_eq := by
          intro x
          rw [MvPolynomial.eval_rename]
          rfl
      }⟩
  | affine ell =>
      exact ⟨{
        generatorCount := 0
        derivativeOrder := Fin.elim0
        argument := Fin.elim0
        polynomial := MvPolynomial.rename Sum.inl (affinePolynomial ell)
        eval_eq := by
          intro x
          rw [MvPolynomial.eval_rename]
          change MvPolynomial.eval x (affinePolynomial ell) = ell x
          rw [eval_affinePolynomial]
      }⟩
  | crAffine r ell =>
      exact ⟨{
        generatorCount := 1
        derivativeOrder := fun _ ↦ r
        argument := fun _ ↦ ell
        polynomial := MvPolynomial.X (Sum.inr 0)
        eval_eq := by intro x; simp
      }⟩
  | add _ _ ihf ihg =>
      exact ⟨ihf.some.add ihg.some⟩
  | mul _ _ ihf ihg =>
      exact ⟨ihf.some.mul ihg.some⟩
  | affineComp _ ell ih =>
      exact ⟨ih.some.affineComp ell⟩

end AbelFormalization
