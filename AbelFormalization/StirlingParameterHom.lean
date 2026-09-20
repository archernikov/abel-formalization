import AbelFormalization.TerminalCoefficientIdentities
import AbelFormalization.PolynomialParameterDerivations
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

/-!
# An actual finite-block Stirling parameter substitution

A block variable indexed by r : Fin d
represents the manuscript's positive derivative order r+1. Variables in Keep
are fixed, and may contain every other block. No preservation of an ideal by
this individual block map is claimed: that must be deduced from the actual
global multigrading and global J-invariance in the application.
-/

noncomputable section

namespace AbelFormalization

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- The finite image of the derivative-order r+1 variable. The parameter
degree r-j records the exact lowering in this block. -/
def stirlingParameterVariable (r : Fin d) :
    Polynomial (MvPolynomial (Keep ⊕ Fin d) R) :=
  ∑ j : Fin (r.val + 1), Polynomial.monomial (r.val - j.val)
    ((signedStirling (r.val + 1) (j.val + 1) : MvPolynomial (Keep ⊕ Fin d) R) *
      MvPolynomial.X (Sum.inr (⟨j.val, by omega⟩ : Fin d)))

/-- The genuine Q-algebra homomorphism, obtained by an R-algebra polynomial
evaluation and restriction of scalars. -/
def stirlingParameterHom : MvPolynomial (Keep ⊕ Fin d) R →ₐ[ℚ]
    Polynomial (MvPolynomial (Keep ⊕ Fin d) R) :=
  (MvPolynomial.aeval (Sum.elim
    (fun k : Keep => Polynomial.C (MvPolynomial.X (Sum.inl k)))
    (stirlingParameterVariable R Keep d))).restrictScalars ℚ

@[simp]
theorem stirlingParameterHom_C (a : R) :
    stirlingParameterHom R Keep d (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
  simp [stirlingParameterHom, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

@[simp]
theorem stirlingParameterHom_X_keep (k : Keep) :
    stirlingParameterHom R Keep d (MvPolynomial.X (Sum.inl k)) =
      Polynomial.C (MvPolynomial.X (Sum.inl k)) := by
  simp [stirlingParameterHom]

@[simp]
theorem stirlingParameterHom_X_block (r : Fin d) :
    stirlingParameterHom R Keep d (MvPolynomial.X (Sum.inr r)) =
      stirlingParameterVariable R Keep d r := by
  simp [stirlingParameterHom]

omit [Algebra ℚ R] in
/-- Every coefficient of a variable image is identified, including all
coefficients beyond the possible lowering range. -/
theorem stirlingParameterVariable_coeff (r : Fin d) (k : ℕ) :
    (stirlingParameterVariable R Keep d r).coeff k =
      if hk : k ≤ r.val then
        (signedStirling (r.val + 1) (r.val - k + 1) : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr (⟨r.val - k, by omega⟩ : Fin d))
      else 0 := by
  classical
  unfold stirlingParameterVariable
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ r.val
  · rw [dite_eq_left hk]
    let j₀ : Fin (r.val + 1) := ⟨r.val - k, by omega⟩
    rw [Finset.sum_eq_single j₀]
    · simp [j₀, Nat.sub_sub_self hk]
    · intro j hj hne
      have hdeg : r.val - j.val ≠ k := by
        intro heq
        apply hne
        apply Fin.ext
        dsimp [j₀]
        omega
      simp [Polynomial.coeff_monomial, hdeg]
    · intro hmissing
      exact (hmissing (Finset.mem_univ j₀)).elim
  · rw [dite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hdeg : r.val - j.val ≠ k := by omega
    simp [Polynomial.coeff_monomial, hdeg]

omit [Algebra ℚ R] in
@[simp]
theorem stirlingParameterVariable_coeff_zero (r : Fin d) :
    (stirlingParameterVariable R Keep d r).coeff 0 =
      MvPolynomial.X (Sum.inr r) := by
  rw [stirlingParameterVariable_coeff, dite_eq_left (Nat.zero_le r.val)]
  simp [signedStirling_self]

/-- The parameter-zero coefficient is the identity on every polynomial,
proved on coefficients and independent variables by ring-hom extensionality. -/
theorem stirlingParameterHom_coeff_zero
    (P : MvPolynomial (Keep ⊕ Fin d) R) :
    (stirlingParameterHom R Keep d P).coeff 0 = P := by
  have h : Polynomial.constantCoeff.comp (stirlingParameterHom R Keep d).toRingHom =
      RingHom.id (MvPolynomial (Keep ⊕ Fin d) R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · rintro (k | r)
      · simp
      · simp
  exact RingHom.congr_fun h P

/-- The first coefficient is minus the coefficient of V₁ on this variable.
The r=0 branch is the genuine first-derivative variable and is zero. -/
theorem stirlingParameterVariable_coeff_one (r : Fin d) :
    (stirlingParameterVariable R Keep d r).coeff 1 =
      if hr : 1 ≤ r.val then
        -((r.val + 1).choose 2 : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr (⟨r.val - 1, by omega⟩ : Fin d))
      else 0 := by
  rw [stirlingParameterVariable_coeff]
  split_ifs with hr
  · rw [Nat.sub_add_cancel hr,
      signedStirling_first_subdiagonal_qAlgebra (MvPolynomial (Keep ⊕ Fin d) R)]
  · rfl

omit [Algebra ℚ R] in
/-- The second raw coefficient is the signed-Stirling second subdiagonal.
For the first two derivative-order variables the coefficient is zero. -/
theorem stirlingParameterVariable_coeff_two (r : Fin d) :
    (stirlingParameterVariable R Keep d r).coeff 2 =
      if hr : 2 ≤ r.val then
        (signedStirling (r.val + 1) (r.val - 2 + 1) : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr (⟨r.val - 2, by omega⟩ : Fin d))
      else 0 :=
  stirlingParameterVariable_coeff R Keep d r 2

/-- The actual first derivation of this finite-block substitution. -/
def stirlingParameterFirstDerivation :
    Derivation ℚ (MvPolynomial (Keep ⊕ Fin d) R) (MvPolynomial (Keep ⊕ Fin d) R) :=
  polynomialParameterFirstDerivation (stirlingParameterHom R Keep d)
    (stirlingParameterHom_coeff_zero R Keep d)

/-- The actual second logarithmic component of this substitution, formed
from its coefficients using the proved generic construction. -/
def stirlingParameterSecondLogDerivation :
    Derivation ℚ (MvPolynomial (Keep ⊕ Fin d) R) (MvPolynomial (Keep ⊕ Fin d) R) :=
  polynomialParameterSecondLogDerivation (stirlingParameterHom R Keep d)
    (stirlingParameterHom_coeff_zero R Keep d)

@[simp]
theorem stirlingParameterFirstDerivation_C (a : R) :
    stirlingParameterFirstDerivation R Keep d (MvPolynomial.C a) = 0 := by
  simp [stirlingParameterFirstDerivation]

@[simp]
theorem stirlingParameterFirstDerivation_X_keep (k : Keep) :
    stirlingParameterFirstDerivation R Keep d (MvPolynomial.X (Sum.inl k)) = 0 := by
  simp [stirlingParameterFirstDerivation]

/-- The first coefficient gives the indicated lowering on each block
variable, with no boundary index interpreted outside Fin d. -/
theorem stirlingParameterFirstDerivation_X_block (r : Fin d) :
    stirlingParameterFirstDerivation R Keep d (MvPolynomial.X (Sum.inr r)) =
      if hr : 1 ≤ r.val then
        -((r.val + 1).choose 2 : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr (⟨r.val - 1, by omega⟩ : Fin d))
      else 0 := by
  simp only [stirlingParameterFirstDerivation, polynomialParameterFirstDerivation_apply,
    stirlingParameterHom_X_block]
  exact stirlingParameterVariable_coeff_one R Keep d r

end AbelFormalization
