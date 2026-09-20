import AbelFormalization.LaurentRescaling
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Normalization by the minimum integer support weight

Every polynomial has finitely many monomials even when the variable type is
infinite. Subtracting their minimum integer weight produces an ordinary
polynomial in the deformation parameter. Its Laurent image is the rescaled
original polynomial multiplied by the compensating Laurent unit, and its
special fiber is precisely the minimum-weight homogeneous component.

No domain assumption is used: distinct original monomials remain distinct
coefficient monomials throughout this construction.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*} [CommSemiring R]

/-- The minimum weight of the nonzero monomials, with value zero for the zero
polynomial. The weights themselves may be negative. -/
def minimumSupportWeight (ω : ι → ℤ) (f : MvPolynomial ι R) : ℤ := by
  classical
  exact if h : f.support.Nonempty then f.support.inf' h (Finsupp.weight ω) else 0

@[simp]
theorem minimumSupportWeight_zero (ω : ι → ℤ) :
    minimumSupportWeight ω (0 : MvPolynomial ι R) = 0 := by
  simp [minimumSupportWeight]

/-- Every monomial in the support has weight at least the chosen minimum. -/
theorem minimumSupportWeight_le (ω : ι → ℤ) (f : MvPolynomial ι R)
    {d : ι →₀ ℕ} (hd : d ∈ f.support) :
    minimumSupportWeight ω f ≤ Finsupp.weight ω d := by
  classical
  have hs : f.support.Nonempty := ⟨d, hd⟩
  simp only [minimumSupportWeight, dite_eq_left hs]
  exact Finset.inf'_le (Finsupp.weight ω) hd

/-- For a nonzero polynomial the minimum is attained by an actual nonzero
coefficient, rather than by an artificial default value. -/
theorem exists_support_weight_eq_minimum (ω : ι → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ d ∈ f.support, Finsupp.weight ω d = minimumSupportWeight ω f := by
  classical
  have hs : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
  obtain ⟨d, hd, hle⟩ :=
    (Finset.inf'_le_iff hs (f := Finsupp.weight ω)).mp le_rfl
  refine ⟨d, hd, le_antisymm ?_ (minimumSupportWeight_le ω f hd)⟩
  simpa only [minimumSupportWeight, dite_eq_left hs] using hle

/-- Normalization of all monomials of a polynomial by its own minimum weight.
The natural deformation exponents are nonnegative by construction. -/
def weightedNormalize (ω : ι → ℤ) (f : MvPolynomial ι R) :
    Polynomial (MvPolynomial ι R) := by
  classical
  exact ∑ d ∈ f.support,
    Polynomial.monomial ((Finsupp.weight ω d - minimumSupportWeight ω f).toNat)
      (MvPolynomial.monomial d (f.coeff d))

@[simp]
theorem weightedNormalize_zero (ω : ι → ℤ) :
    weightedNormalize ω (0 : MvPolynomial ι R) = 0 := by
  simp [weightedNormalize]

/-- The natural exponent in the normalization is exactly the integer weight
difference on every supported monomial; no truncation occurs there. -/
theorem weightedNormalize_exponent_cast (ω : ι → ℤ) (f : MvPolynomial ι R)
    {d : ι →₀ ℕ} (hd : d ∈ f.support) :
    (((Finsupp.weight ω d - minimumSupportWeight ω f).toNat : ℕ) : ℤ) =
      Finsupp.weight ω d - minimumSupportWeight ω f :=
  Int.toNat_of_nonneg (sub_nonneg.mpr (minimumSupportWeight_le ω f hd))

/-- The explicit finite normalization is the literal Laurent rescaling,
multiplied by the unit that moves its minimum exponent to zero. -/
theorem weightedNormalize_toLaurent (ω : ι → ℤ) (f : MvPolynomial ι R) :
    Polynomial.toLaurent (weightedNormalize ω f) =
      LaurentPolynomial.T (-minimumSupportWeight ω f) *
        laurentWeightRescaling ω (LaurentPolynomial.C f) := by
  classical
  have hC : LaurentPolynomial.C f =
      ∑ d ∈ f.support, LaurentPolynomial.C (MvPolynomial.monomial d (f.coeff d)) := by
    simpa only [map_sum] using
      congrArg (LaurentPolynomial.C : MvPolynomial ι R →+*
        LaurentPolynomial (MvPolynomial ι R)) (MvPolynomial.as_sum f)
  have hrescale : laurentWeightRescaling ω (LaurentPolynomial.C f) =
      ∑ d ∈ f.support,
        LaurentPolynomial.C (MvPolynomial.monomial d (f.coeff d)) *
          LaurentPolynomial.T (Finsupp.weight ω d) := by
    rw [hC, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simpa only [LaurentPolynomial.T_zero, mul_one, zero_add] using
      laurentWeightRescaling_monomial ω 0 d (f.coeff d)
  rw [weightedNormalize, map_sum, hrescale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.toLaurent_C_mul_T, weightedNormalize_exponent_cast ω f hd,
    sub_eq_add_neg, LaurentPolynomial.T_add]
  ac_rfl

/-- The special fiber of the normalization is exactly the minimum-weight
component of the original polynomial. -/
theorem weightedNormalize_eval_zero (ω : ι → ℤ) (f : MvPolynomial ι R) :
    (weightedNormalize ω f).eval 0 =
      MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f := by
  classical
  rw [weightedNormalize, Polynomial.eval_finsetSum,
    MvPolynomial.weightedHomogeneousComponent_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.eval_monomial]
  by_cases he : Finsupp.weight ω d = minimumSupportWeight ω f
  · simp [he]
  · have hnat : (Finsupp.weight ω d - minimumSupportWeight ω f).toNat ≠ 0 := by
      intro hz
      have hle := sub_nonpos.mp (Int.toNat_eq_zero.mp hz)
      exact he (le_antisymm hle (minimumSupportWeight_le ω f hd))
    simp [he, zero_pow hnat]

/-- The minimum-weight component of a nonzero polynomial is nonzero over
every commutative semiring, including rings with zero divisors. -/
theorem weightedHomogeneousComponent_minimum_ne_zero (ω : ι → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f ≠ 0 := by
  classical
  obtain ⟨d, hd, hweight⟩ := exists_support_weight_eq_minimum ω hf
  intro hz
  have hc : f.coeff d = 0 := by
    simpa only [MvPolynomial.coeff_weightedHomogeneousComponent, ite_eq_left hweight,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      congrArg (fun p : MvPolynomial ι R => p.coeff d) hz
  exact (MvPolynomial.mem_support_iff.mp hd) hc

/-- In particular a nonzero original polynomial has a nonzero special fiber. -/
theorem weightedNormalize_eval_zero_ne_zero (ω : ι → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    (weightedNormalize ω f).eval 0 ≠ 0 := by
  rw [weightedNormalize_eval_zero]
  exact weightedHomogeneousComponent_minimum_ne_zero ω hf

@[simp]
theorem weightedNormalize_eq_zero_iff (ω : ι → ℤ) (f : MvPolynomial ι R) :
    weightedNormalize ω f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    exact weightedNormalize_eval_zero_ne_zero ω hf (by simp [h])
  · rintro rfl
    exact weightedNormalize_zero ω

end AbelFormalization
