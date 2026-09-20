import AbelFormalization.Inverse
import Mathlib.ModelTheory.Definability

/-!
# Exact statement of the proposed main theorem

This file defines the first-order expansion and the conclusion as
`MainTheorem : Prop`. Its proof is `AbelFormalization.mainTheorem` in
`WilkieSection4LiteralZeroInduction`.

Definability here is mathlib's first-order definability, allowing arbitrary real
parameters. The o-minimality conclusion explicitly requires every definable
unary set to be a finite union of points and intervals, including unbounded
intervals. No regular-zero finiteness assumption is hidden in that conclusion.
-/

namespace AbelFormalization

/-- The total real-analytic generator named in the proposed structure. -/
def C0 (A : ℝ → ℝ) (x : ℝ) : ℝ := A (1 + x ^ 2)

/-- Exactly the function symbols in `(ℝ; <, +, ·, C₀)`. -/
inductive AbelFunctionSymbol : ℕ → Type
  | add : AbelFunctionSymbol 2
  | mul : AbelFunctionSymbol 2
  | c0 : AbelFunctionSymbol 1

/-- The strict order relation symbol. -/
inductive AbelRelationSymbol : ℕ → Type
  | lt : AbelRelationSymbol 2

/-- The language of the proposed expansion. Real constants are available as
parameters in the definability predicates below. -/
def abelLanguage : FirstOrder.Language where
  Functions := AbelFunctionSymbol
  Relations := AbelRelationSymbol

/-- Interpret the expansion on the actual real numbers. This is a definition,
not a global instance, so different choices of `A` cannot be confused. -/
@[instance_reducible] def abelStructure (A : ℝ → ℝ) : abelLanguage.Structure ℝ where
  funMap
    | .add, x => x 0 + x 1
    | .mul, x => x 0 * x 1
    | .c0, x => C0 A (x 0)
  RelMap
    | .lt, x => x 0 < x 1

/-- Unary definability with real parameters in the specified expansion. -/
def UnaryDefinable (A : ℝ → ℝ) (s : Set ℝ) : Prop :=
  letI := abelStructure A
  (Set.univ : Set ℝ).Definable₁ abelLanguage s

/-- Binary definability with real parameters in the specified expansion. -/
def BinaryDefinable (A : ℝ → ℝ) (s : Set (ℝ × ℝ)) : Prop :=
  letI := abelStructure A
  (Set.univ : Set ℝ).Definable₂ abelLanguage s

/-- The pieces allowed in a unary o-minimal decomposition. Endpoints of closed
or half-closed intervals can be represented by separate point pieces. -/
inductive UnaryPiece
  | point (a : ℝ)
  | bounded (a b : ℝ)
  | leftRay (b : ℝ)
  | rightRay (a : ℝ)
  | whole

/-- The real set represented by one piece. -/
def UnaryPiece.carrier : UnaryPiece → Set ℝ
  | .point a => {a}
  | .bounded a b => Set.Ioo a b
  | .leftRay b => Set.Iio b
  | .rightRay a => Set.Ioi a
  | .whole => Set.univ

/-- O-minimality of this particular first-order structure, written directly as
finite point-and-interval decomposition of every definable unary set. -/
def OMinimal (A : ℝ → ℝ) : Prop :=
  ∀ s : Set ℝ, UnaryDefinable A s →
    ∃ (n : ℕ) (pieces : Fin n → UnaryPiece),
      s = ⋃ i, (pieces i).carrier

/-- The full real exponential has a definable graph. -/
def ExponentialDefinable (A : ℝ → ℝ) : Prop :=
  BinaryDefinable A {p : ℝ × ℝ | p.2 = Real.exp p.1}

/-- The graph of the inverse restricted to positive input, exactly as named in
the proposed main theorem. -/
def PositiveInverseDefinable (A T : ℝ → ℝ) : Prop :=
  BinaryDefinable A {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = T p.1}

/-- `T` is the inverse of `A : (0,∞) → ℝ`. Values of the total Lean function
`A` outside `(0,∞)` play no role. -/
def IsPositiveInverse (A T : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 < T t ∧ A (T t) = t) ∧
  (∀ x : ℝ, 0 < x → T (A x) = x)

/-- Domination of each fixed finite iterate of the usual exponential. -/
def IsTransexponential (T : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ threshold : ℝ,
    ∀ s : ℝ, threshold < s → (Real.exp^[k]) s < T s

/-- The complete theorem stated in the manuscript. The proof is
`AbelFormalization.mainTheorem` in `WilkieSection4LiteralZeroInduction`. -/
def MainTheorem : Prop :=
  ∀ A : ℝ → ℝ, IsAbel A →
    OMinimal A ∧ ExponentialDefinable A ∧
      PositiveInverseDefinable A (inverse A) ∧
        IsTransexponential (inverse A)

end AbelFormalization
