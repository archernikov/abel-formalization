import AbelFormalization.TerminalInvariantDerivations
import Mathlib.Algebra.Polynomial.EraseLead

set_option autoImplicit false

noncomputable section

namespace AbelFormalization

open Function

variable {C : Type*} [CommRing C] [Algebra ℚ C]

/-- Differentiating a polynomial as many times as its degree leaves its
factorial-scaled leading coefficient. -/
theorem polynomial_iterate_derivative_natDegree_eq_C (P : Polynomial C) :
    Polynomial.derivative^[P.natDegree] P =
      Polynomial.C (P.natDegree.factorial • P.leadingCoeff) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.zero_add, Nat.descFactorial_self,
      Polynomial.coeff_C_zero]
    rfl
  · have hlt : P.natDegree < m + P.natDegree := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp [hm]

/-- Stability under one derivative implies stability under every iterate. -/
theorem polynomial_iterate_derivative_mem
    (I : Ideal (Polynomial C))
    (hderiv : ∀ P ∈ I, Polynomial.derivative P ∈ I)
    {P : Polynomial C} (hP : P ∈ I) (k : ℕ) :
    Polynomial.derivative^[k] P ∈ I := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hderiv _ ih

/-- Over a rational algebra, derivative stability extracts the leading
coefficient as a constant polynomial. -/
theorem polynomial_C_leadingCoeff_mem_of_derivative_stable
    (I : Ideal (Polynomial C))
    (hderiv : ∀ P ∈ I, Polynomial.derivative P ∈ I)
    {P : Polynomial C} (hP : P ∈ I) :
    Polynomial.C P.leadingCoeff ∈ I := by
  let q : ℚ := (P.natDegree.factorial : ℚ)⁻¹
  have htop : Polynomial.C (P.natDegree.factorial • P.leadingCoeff) ∈ I := by
    rw [← polynomial_iterate_derivative_natDegree_eq_C P]
    exact polynomial_iterate_derivative_mem I hderiv hP P.natDegree
  have hmul := I.mul_mem_left (Polynomial.C (algebraMap ℚ C q)) htop
  have hscale :
      algebraMap ℚ C q * (P.natDegree.factorial • P.leadingCoeff) =
        P.leadingCoeff := by
    change algebraMap ℚ C ((P.natDegree.factorial : ℚ)⁻¹) *
        (P.natDegree.factorial • P.leadingCoeff) = P.leadingCoeff
    rw [← Nat.cast_smul_eq_nsmul C]
    simp only [smul_eq_mul]
    have hnat : (P.natDegree.factorial : C) =
        algebraMap ℚ C (P.natDegree.factorial : ℚ) :=
      (map_natCast (algebraMap ℚ C) P.natDegree.factorial).symm
    have hinv :
        algebraMap ℚ C ((P.natDegree.factorial : ℚ)⁻¹) *
            (P.natDegree.factorial : C) = 1 := by
      have hfac : (P.natDegree.factorial : ℚ) ≠ 0 := by positivity
      calc
        algebraMap ℚ C ((P.natDegree.factorial : ℚ)⁻¹) *
              (P.natDegree.factorial : C) =
            algebraMap ℚ C ((P.natDegree.factorial : ℚ)⁻¹) *
              algebraMap ℚ C (P.natDegree.factorial : ℚ) :=
          congrArg
            (fun z : C =>
              algebraMap ℚ C ((P.natDegree.factorial : ℚ)⁻¹) * z) hnat
        _ = algebraMap ℚ C
              ((P.natDegree.factorial : ℚ)⁻¹ *
                (P.natDegree.factorial : ℚ)) :=
          (map_mul (algebraMap ℚ C) _ _).symm
        _ = algebraMap ℚ C 1 :=
          congrArg (algebraMap ℚ C) (inv_mul_cancel₀ hfac)
        _ = 1 := map_one (algebraMap ℚ C)
    rw [← mul_assoc, hinv, one_mul]
  rw [← Polynomial.C_mul, hscale] at hmul
  exact hmul

/-- An ideal of a polynomial ring over a rational algebra that is stable
under differentiation is extended from its contraction to the coefficient
ring. -/
theorem polynomial_derivative_stable_ideal_eq_map_comap
    (I : Ideal (Polynomial C))
    (hderiv : ∀ P ∈ I, Polynomial.derivative P ∈ I) :
    I = (I.comap Polynomial.C).map Polynomial.C := by
  apply le_antisymm
  · intro P hP
    revert hP
    induction P using
        (measure fun Q : Polynomial C => Q.support.card).wf.induction with
    | h P ih =>
      intro hP
      by_cases hzero : P = 0
      · subst P
        exact (I.comap Polynomial.C).map Polynomial.C |>.zero_mem
      have hleadI : Polynomial.C P.leadingCoeff ∈ I :=
        polynomial_C_leadingCoeff_mem_of_derivative_stable I hderiv hP
      have hlead : Polynomial.C P.leadingCoeff ∈
          (I.comap Polynomial.C).map Polynomial.C :=
        Ideal.mem_map_of_mem Polynomial.C hleadI
      have hterm : Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree ∈
          (I.comap Polynomial.C).map Polynomial.C :=
        ((I.comap Polynomial.C).map Polynomial.C).mul_mem_right _ hlead
      have heraseI : P.eraseLead ∈ I := by
        rw [← Polynomial.self_sub_C_mul_X_pow P]
        exact I.sub_mem hP (I.mul_mem_right _ hleadI)
      have herase : P.eraseLead ∈ (I.comap Polynomial.C).map Polynomial.C := by
        exact ih P.eraseLead (Polynomial.eraseLead_support_card_lt hzero) heraseI
      rw [← Polynomial.eraseLead_add_C_mul_X_pow P]
      exact ((I.comap Polynomial.C).map Polynomial.C).add_mem herase hterm
  · exact Ideal.map_comap_le

end AbelFormalization
