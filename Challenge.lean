import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.ModelTheory.Definability

/-!
# Abel functions and a transexponential o-minimal expansion

Let `E x = exp x - 1`.  An Abel function in this file is a real function that
is analytic with strictly positive derivative on the positive half-line, is
normalized at one, and conjugates `E` to translation by one.  From such a
function `A`, we expand the ordered real field by the single analytic function
`C0 A x = A (1 + x²)`.

The first claim says that every such expansion is o-minimal, defines the full
real exponential, defines the positive-input graph of the inverse of `A`, and
that this inverse eventually dominates every fixed finite iterate of
exponentiation.  The second claim says that an Abel function satisfying these
conclusions exists.

All definability below is first-order definability with arbitrary real
parameters.  The finite-union formulation of o-minimality includes points,
bounded open intervals, rays, and the whole line.
-/

namespace AbelFormalization

noncomputable section

/-- The dynamical map `E(x) = exp(x) - 1` on the positive real axis. -/
def E (x : ℝ) : ℝ := Real.exp x - 1

/-- The hypotheses on an Abel function `A : (0,∞) → ℝ`: analyticity and
positive derivative on its domain, the normalization `A(1) = 0`, and the Abel
equation `A(exp(x) - 1) = A(x) + 1`.  Lean functions are total, but values of
`A` outside the positive half-line play no role. -/
structure IsAbel (A : ℝ → ℝ) : Prop where
  analytic : AnalyticOnNhd ℝ A (Set.Ioi 0)
  deriv_pos : ∀ x > 0, 0 < deriv A x
  normalized : A 1 = 0
  abel : ∀ x > 0, A (E x) = A x + 1

/-- The inverse of `A` selected on its positive domain.  Under `IsAbel A`, the
restriction `A : (0,∞) → ℝ` is bijective, so this is its ordinary inverse. -/
def inverse (A : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFunOn A (Set.Ioi 0)

/-- The total real-analytic generator `C₀(x) = A(1 + x²)` used to expand the
ordered real field. -/
def C0 (A : ℝ → ℝ) (x : ℝ) : ℝ := A (1 + x ^ 2)

/-- The addition, multiplication, and `C₀` symbols of `(ℝ; <, +, ·, C₀)`. -/
inductive AbelFunctionSymbol : ℕ → Type
  | add : AbelFunctionSymbol 2
  | mul : AbelFunctionSymbol 2
  | c0 : AbelFunctionSymbol 1

/-- The strict-order symbol of `(ℝ; <, +, ·, C₀)`. -/
inductive AbelRelationSymbol : ℕ → Type
  | lt : AbelRelationSymbol 2

/-- The first-order language with function symbols `+`, `·`, and `C₀`, and
relation symbol `<`. -/
def abelLanguage : FirstOrder.Language where
  Functions := AbelFunctionSymbol
  Relations := AbelRelationSymbol

/-- The interpretation of `abelLanguage` on the real numbers determined by
`A`, with the usual addition, multiplication, and order. -/
@[instance_reducible] def abelStructure (A : ℝ → ℝ) :
    abelLanguage.Structure ℝ where
  funMap
    | .add, x => x 0 + x 1
    | .mul, x => x 0 * x 1
    | .c0, x => C0 A (x 0)
  RelMap
    | .lt, x => x 0 < x 1

/-- First-order definability, with arbitrary real parameters, of a unary set
in the structure `(ℝ; <, +, ·, C₀)`. -/
def UnaryDefinable (A : ℝ → ℝ) (s : Set ℝ) : Prop :=
  letI := abelStructure A
  (Set.univ : Set ℝ).Definable₁ abelLanguage s

/-- First-order definability, with arbitrary real parameters, of a binary set
in the structure `(ℝ; <, +, ·, C₀)`. -/
def BinaryDefinable (A : ℝ → ℝ) (s : Set (ℝ × ℝ)) : Prop :=
  letI := abelStructure A
  (Set.univ : Set ℝ).Definable₂ abelLanguage s

/-- A point, bounded open interval, open ray, or the whole real line: the
pieces used in the finite decomposition formulation of o-minimality. -/
inductive UnaryPiece
  | point (a : ℝ)
  | bounded (a b : ℝ)
  | leftRay (b : ℝ)
  | rightRay (a : ℝ)
  | whole

/-- The subset of `ℝ` represented by a unary piece. -/
def UnaryPiece.carrier : UnaryPiece → Set ℝ
  | .point a => {a}
  | .bounded a b => Set.Ioo a b
  | .leftRay b => Set.Iio b
  | .rightRay a => Set.Ioi a
  | .whole => Set.univ

/-- O-minimality of `(ℝ; <, +, ·, C₀)`: every definable unary set is a finite
union of points and intervals, with unbounded intervals allowed. -/
def OMinimal (A : ℝ → ℝ) : Prop :=
  ∀ s : Set ℝ, UnaryDefinable A s →
    ∃ (n : ℕ) (pieces : Fin n → UnaryPiece),
      s = ⋃ i, (pieces i).carrier

/-- The graph of the full real exponential is definable in the expansion. -/
def ExponentialDefinable (A : ℝ → ℝ) : Prop :=
  BinaryDefinable A {p : ℝ × ℝ | p.2 = Real.exp p.1}

/-- The graph of `T` restricted to positive inputs is definable in the
expansion determined by `A`. -/
def PositiveInverseDefinable (A T : ℝ → ℝ) : Prop :=
  BinaryDefinable A {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = T p.1}

/-- A function is transexponential when it eventually dominates every fixed
finite iterate of the real exponential. -/
def IsTransexponential (T : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ threshold : ℝ,
    ∀ s : ℝ, threshold < s → (Real.exp^[k]) s < T s

/-- Every Abel function gives an o-minimal expansion that defines exponential
and the positive-input graph of its transexponential inverse. -/
def MainTheorem : Prop :=
  ∀ A : ℝ → ℝ, IsAbel A →
    OMinimal A ∧ ExponentialDefinable A ∧
      PositiveInverseDefinable A (inverse A) ∧
        IsTransexponential (inverse A)

/-- The universal theorem for expansions generated by Abel functions. -/
theorem mainTheorem : MainTheorem := by
  sorry

/-- There exists an Abel function whose associated expansion is o-minimal,
defines exponential and its positive inverse graph, and has transexponential
inverse growth. -/
theorem exists_abel_ominimal_expansion :
    ∃ A : ℝ → ℝ, IsAbel A ∧
      OMinimal A ∧ ExponentialDefinable A ∧
        PositiveInverseDefinable A (inverse A) ∧
          IsTransexponential (inverse A) := by
  sorry

end

end AbelFormalization
