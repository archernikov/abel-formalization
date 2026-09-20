import AbelFormalization.PolynomialGermDifferentialRepresentatives
import AbelFormalization.GermMatrixMinors
import AbelFormalization.PolynomialFamilyFormalJacobian
import AbelFormalization.AugmentedJacobianHeight

/-!
# The formal Jacobian over actual analytic germs

The coefficient and symbol
derivations are actual derivations of the polynomial algebra over analytic
germs. Their matrix entries and squared-minor denominator are represented
using the same finite coefficient family as the original equations.

The evaluation formulas below are literal polynomial identities for every
coefficient argument and every symbol assignment. The assertions about
germs require actual analytic representatives at the origin.
-/

noncomputable section

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι] {p n : ℕ}

/-- The actual coefficient partials followed by the independent symbol
partials, with exactly the same column indexing as the chain-rule matrix. -/
def analyticGermFormalDerivations (p : ℕ) :
    (Fin p ⊕ ι) → Derivation ℝ
      (MvPolynomial ι (RealAnalyticGerm p))
      (MvPolynomial ι (RealAnalyticGerm p)) :=
  Sum.elim (analyticGermCoefficientPartial p) (analyticGermSymbolPartial p)

/-- The coefficient block differentiates the original coefficient functions
on their original finite supports. The symbol block applies actual polynomial
partial derivatives, which may change those supports. -/
def analyticGermFormalJacobianRepresentative
    (P : Fin n → MvPolynomial ι (RealAnalyticGerm p))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : Fin p → ℝ) : Matrix (Fin n) (Fin p ⊕ ι) (MvPolynomial ι ℝ) :=
  fun i => Sum.elim
    (fun j => polynomialFromCoefficientRepresentatives (P i).support
      (fun d v => fderiv ℝ (a i d) v (Pi.single j 1)) w)
    (fun j => MvPolynomial.pderiv j
      (polynomialFromCoefficientRepresentatives (P i).support (a i) w))

/-- The polynomial representative of the formal squared-minor denominator. -/
def analyticGermJacobianDenominatorRepresentative
    (P : Fin n → MvPolynomial ι (RealAnalyticGerm p))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : Fin p → ℝ) : MvPolynomial ι ℝ :=
  sumSquaresColumnMinors (analyticGermFormalJacobianRepresentative P a w)

omit [Fintype ι] in
/-- Every actual derivation-Jacobian entry has the indicated
polynomial-valued germ representative from the same coefficient functions. -/
theorem analyticPolynomialGermHom_formalJacobian_entry
    (P : Fin n → MvPolynomial ι (RealAnalyticGerm p))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (ha : ∀ i d, AnalyticAt ℝ (a i d) 0)
    (hrep : ∀ i d, d ∈ (P i).support →
      (P i).coeff d = analyticGermOf (a i d) (ha i d))
    (i : Fin n) (j : Fin p ⊕ ι) :
    analyticPolynomialGermHom (0 : Fin p → ℝ)
        (derivationJacobian P (analyticGermFormalDerivations p) i j) =
      ((fun w => analyticGermFormalJacobianRepresentative P a w i j) :
        Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial ι ℝ)) := by
  cases j with
  | inl j =>
      change analyticPolynomialGermHom (0 : Fin p → ℝ)
          (mvPolynomialCoefficientDerivation
            (analyticGermDerivation 0 (Pi.single j 1)) (P i)) =
        (polynomialFromCoefficientRepresentatives (P i).support
          (fun d w => fderiv ℝ (a i d) w (Pi.single j 1)) :
          Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial ι ℝ))
      exact analyticPolynomialGermHom_coefficientDerivation_eq_representative
        0 (Pi.single j 1) (P i) (a i) (ha i) (hrep i)
  | inr j =>
      change analyticPolynomialGermHom (0 : Fin p → ℝ)
          (MvPolynomial.pderiv j (P i)) =
        ((fun w => MvPolynomial.pderiv j
          (polynomialFromCoefficientRepresentatives (P i).support (a i) w)) :
          Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial ι ℝ))
      exact analyticPolynomialGermHom_pderiv_eq_representative
        0 j (P i) (a i) (ha i) (hrep i)

/-- The actual formal denominator has the pointwise squared-minor
polynomial as its germ representative. -/
theorem analyticPolynomialGermHom_formalJacobianDenominator
    (P : Fin n → MvPolynomial ι (RealAnalyticGerm p))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (ha : ∀ i d, AnalyticAt ℝ (a i d) 0)
    (hrep : ∀ i d, d ∈ (P i).support →
      (P i).coeff d = analyticGermOf (a i d) (ha i d)) :
    analyticPolynomialGermHom (0 : Fin p → ℝ)
        (derivationJacobianDenominator P (analyticGermFormalDerivations p)) =
      (analyticGermJacobianDenominatorRepresentative P a :
        Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial ι ℝ)) := by
  exact analyticPolynomialGermHom_sumSquaresColumnMinors (0 : Fin p → ℝ)
    (derivationJacobian P (analyticGermFormalDerivations p))
    (analyticGermFormalJacobianRepresentative P a)
    (analyticPolynomialGermHom_formalJacobian_entry P a ha hrep)

omit [Fintype ι] in
/-- Evaluating the polynomial-valued matrix gives exactly the real formal
Jacobian used in the actual chain rule, at every argument and symbol value. -/
theorem analyticGermFormalJacobianRepresentative_eval
    (P : Fin n → MvPolynomial ι (RealAnalyticGerm p))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : Fin p → ℝ) (z : ι → ℝ) :
    (analyticGermFormalJacobianRepresentative P a w).map (MvPolynomial.eval z) =
      polynomialFamilyFormalJacobian (fun i => (P i).support) a w z := by
  funext i j
  cases j <;> rfl

/-- The evaluated polynomial denominator is the literal sum of squares of
all full-row-size minors of the same real formal matrix. -/
theorem eval_analyticGermJacobianDenominatorRepresentative
    (P : Fin n → MvPolynomial ι (RealAnalyticGerm p))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : Fin p → ℝ) (z : ι → ℝ) :
    MvPolynomial.eval z (analyticGermJacobianDenominatorRepresentative P a w) =
      sumSquaresColumnMinors
        (polynomialFamilyFormalJacobian (fun i => (P i).support) a w z) := by
  rw [analyticGermJacobianDenominatorRepresentative, eval_sumSquaresColumnMinors,
    analyticGermFormalJacobianRepresentative_eval]

end AbelFormalization
