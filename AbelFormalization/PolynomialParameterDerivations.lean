import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# The first two derivations of an actual polynomial-parameter homomorphism

If the constant coefficient of an
actual Q-algebra homomorphism H : R → Polynomial R is the identity, then its
first coefficient is a derivation, and its second coefficient minus half
the square of the first is another derivation. The product rules are proved
from Polynomial.coeff_mul, rather than assumed as additional structure.

The ideal-preservation results use genuine coefficient membership in the
given ideal. They do not assert that an arbitrary ideal has this property;
the application to a graded Stirling substitution must establish it.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Every coefficient of the actual parameter homomorphism is Q-linear. -/
def polynomialParameterCoeff (H : R →ₐ[ℚ] Polynomial R) (k : ℕ) : R →ₗ[ℚ] R :=
  ((Polynomial.lcoeff R k).restrictScalars ℚ).comp H.toLinearMap

@[simp]
theorem polynomialParameterCoeff_apply (H : R →ₐ[ℚ] Polynomial R)
    (k : ℕ) (a : R) :
    polynomialParameterCoeff H k a = (H a).coeff k := rfl

/-- The first coefficient product rule follows from the two terms in the
degree-one antidiagonal and the identity constant coefficient. -/
theorem polynomialParameterCoeff_one_mul (H : R →ₐ[ℚ] Polynomial R)
    (h0 : ∀ a, (H a).coeff 0 = a) (a b : R) :
    polynomialParameterCoeff H 1 (a * b) =
      a * polynomialParameterCoeff H 1 b + b * polynomialParameterCoeff H 1 a := by
  simp only [polynomialParameterCoeff_apply, map_mul, Polynomial.mul_coeff_one, h0]
  ring

/-- The genuine first coefficient, bundled as a derivation. -/
def polynomialParameterFirstDerivation (H : R →ₐ[ℚ] Polynomial R)
    (h0 : ∀ a, (H a).coeff 0 = a) : Derivation ℚ R R :=
  Derivation.mk' (polynomialParameterCoeff H 1) (by
    intro a b
    simpa only [smul_eq_mul] using polynomialParameterCoeff_one_mul H h0 a b)

@[simp]
theorem polynomialParameterFirstDerivation_apply (H : R →ₐ[ℚ] Polynomial R)
    (h0 : ∀ a, (H a).coeff 0 = a) (a : R) :
    polynomialParameterFirstDerivation H h0 a = (H a).coeff 1 := rfl

/-- The three degree-two antidiagonal terms give the second coefficient
product rule, with exactly one cross term. -/
theorem polynomialParameterCoeff_two_mul (H : R →ₐ[ℚ] Polynomial R)
    (h0 : ∀ a, (H a).coeff 0 = a) (a b : R) :
    polynomialParameterCoeff H 2 (a * b) =
      a * polynomialParameterCoeff H 2 b +
        polynomialParameterCoeff H 1 a * polynomialParameterCoeff H 1 b +
        b * polynomialParameterCoeff H 2 a := by
  simp only [polynomialParameterCoeff_apply, map_mul]
  have hanti : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [Polynomial.coeff_mul, hanti]
  simp [h0]
  ring

/-- Applying Leibniz twice gives a coefficient two on the cross term. -/
theorem derivation_iterate_two_mul (D : Derivation ℚ R R) (a b : R) :
    D (D (a * b)) =
      a * D (D b) + 2 * D a * D b + b * D (D a) := by
  simp only [Derivation.leibniz, smul_eq_mul, map_add]
  ring

/-- The second logarithmic component as a Q-linear map. This definition
requires no logarithm, nilpotence or invertibility of H. -/
def polynomialParameterSecondLogLinearMap (H : R →ₐ[ℚ] Polynomial R) : R →ₗ[ℚ] R :=
  polynomialParameterCoeff H 2 - (1 / 2 : ℚ) •
    (polynomialParameterCoeff H 1).comp (polynomialParameterCoeff H 1)

@[simp]
theorem polynomialParameterSecondLogLinearMap_apply (H : R →ₐ[ℚ] Polynomial R)
    (a : R) :
    polynomialParameterSecondLogLinearMap H a =
      (H a).coeff 2 - (1 / 2 : ℚ) • (H ((H a).coeff 1)).coeff 1 := rfl

/-- The second logarithmic component obeys Leibniz because its correction
term cancels the unique second-coefficient cross term. -/
theorem polynomialParameterSecondLogLinearMap_mul (H : R →ₐ[ℚ] Polynomial R)
    (h0 : ∀ a, (H a).coeff 0 = a) (a b : R) :
    polynomialParameterSecondLogLinearMap H (a * b) =
      a * polynomialParameterSecondLogLinearMap H b +
        b * polynomialParameterSecondLogLinearMap H a := by
  let D := polynomialParameterFirstDerivation H h0
  have hsquare : polynomialParameterCoeff H 1 (polynomialParameterCoeff H 1 (a * b)) =
      a * polynomialParameterCoeff H 1 (polynomialParameterCoeff H 1 b) +
        2 * polynomialParameterCoeff H 1 a * polynomialParameterCoeff H 1 b +
        b * polynomialParameterCoeff H 1 (polynomialParameterCoeff H 1 a) :=
    derivation_iterate_two_mul D a b
  change polynomialParameterCoeff H 2 (a * b) -
      (1 / 2 : ℚ) • polynomialParameterCoeff H 1 (polynomialParameterCoeff H 1 (a * b)) =
    a * (polynomialParameterCoeff H 2 b -
      (1 / 2 : ℚ) • polynomialParameterCoeff H 1 (polynomialParameterCoeff H 1 b)) +
    b * (polynomialParameterCoeff H 2 a -
      (1 / 2 : ℚ) • polynomialParameterCoeff H 1 (polynomialParameterCoeff H 1 a))
  rw [polynomialParameterCoeff_two_mul H h0, hsquare]
  simp only [Algebra.smul_def]
  have hhalf : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  linear_combination
    -(polynomialParameterCoeff H 1 a * polynomialParameterCoeff H 1 b) * hhalf

/-- The actual second logarithmic component, bundled as a derivation. -/
def polynomialParameterSecondLogDerivation (H : R →ₐ[ℚ] Polynomial R)
    (h0 : ∀ a, (H a).coeff 0 = a) : Derivation ℚ R R :=
  Derivation.mk' (polynomialParameterSecondLogLinearMap H) (by
    intro a b
    simpa only [smul_eq_mul] using polynomialParameterSecondLogLinearMap_mul H h0 a b)

/-- Its defining coefficient formula uses the square of the actual first
derivation, not a separately postulated second-order operator. -/
theorem polynomialParameterSecondLogDerivation_apply
    (H : R →ₐ[ℚ] Polynomial R) (h0 : ∀ a, (H a).coeff 0 = a) (a : R) :
    polynomialParameterSecondLogDerivation H h0 a =
      (H a).coeff 2 - (1 / 2 : ℚ) •
        polynomialParameterFirstDerivation H h0
          (polynomialParameterFirstDerivation H h0 a) := rfl

/-- A raw coefficient form is convenient when proving ideal membership. -/
theorem polynomialParameterSecondLogDerivation_apply_coeff
    (H : R →ₐ[ℚ] Polynomial R) (h0 : ∀ a, (H a).coeff 0 = a) (a : R) :
    polynomialParameterSecondLogDerivation H h0 a =
      (H a).coeff 2 - algebraMap ℚ R (1 / 2) * (H ((H a).coeff 1)).coeff 1 := by
  rw [polynomialParameterSecondLogDerivation_apply]
  simp only [polynomialParameterFirstDerivation_apply, Algebra.smul_def]

/-- Closure under the actual first coefficient implies preservation by
the first derivation. -/
theorem polynomialParameterFirstDerivation_preserves_ideal
    (H : R →ₐ[ℚ] Polynomial R) (h0 : ∀ a, (H a).coeff 0 = a)
    (I : Ideal R) (hI1 : ∀ a ∈ I, (H a).coeff 1 ∈ I) :
    ∀ a ∈ I, polynomialParameterFirstDerivation H h0 a ∈ I := by
  intro a ha
  exact hI1 a ha

/-- Closure under the actual first two coefficients implies preservation
by the second logarithmic derivation: the iterated first coefficient lies
in I, and its rational multiple is multiplication by an element of R. -/
theorem polynomialParameterSecondLogDerivation_preserves_ideal
    (H : R →ₐ[ℚ] Polynomial R) (h0 : ∀ a, (H a).coeff 0 = a)
    (I : Ideal R) (hI1 : ∀ a ∈ I, (H a).coeff 1 ∈ I)
    (hI2 : ∀ a ∈ I, (H a).coeff 2 ∈ I) :
    ∀ a ∈ I, polynomialParameterSecondLogDerivation H h0 a ∈ I := by
  intro a ha
  rw [polynomialParameterSecondLogDerivation_apply_coeff]
  exact I.sub_mem (hI2 a ha)
    (I.mul_mem_left (algebraMap ℚ R (1 / 2)) (hI1 _ (hI1 a ha)))

end AbelFormalization
