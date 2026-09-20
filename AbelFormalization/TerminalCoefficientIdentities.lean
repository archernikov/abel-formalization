import AbelFormalization.Stirling
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

/-!
# Exact coefficients for the first two lowering components

These statements concern actual
binomial coefficients and the existing falling-factorial definition of
`signedStirling`. They do not assume vector-field or automorphism identities.
The rational identities are transported to arbitrary commutative Q-algebras,
so the applications do not require a domain or a field of coefficients.
-/

noncomputable section

open Polynomial

namespace AbelFormalization

/-- The rational quadratic formula includes r=0, where the rational
factor r-1 is negative but the complete product is zero. -/
theorem terminal_choose_two_rat (r : ℕ) :
    (r.choose 2 : ℚ) = (r : ℚ) * ((r : ℚ) - 1) / 2 := by
  cases r with
  | zero => simp
  | succ r =>
      have hn := Nat.choose_succ_right_eq (r + 1) 1
      simp only [Nat.choose_one_right, Nat.add_sub_cancel] at hn
      have h := congrArg (fun t : ℕ => (t : ℚ)) hn
      push_cast at h ⊢
      nlinarith

/-- The exact coefficient in [V₁,V_q]. It is valid for all natural q,
including q=0 and q=1, and for all r below the active range. -/
theorem terminal_binomial_bracket_rat (r q : ℕ) :
    (r.choose (q + 1) : ℚ) * ((r - q).choose 2 : ℚ) -
        (r.choose 2 : ℚ) * ((r - 1).choose (q + 1) : ℚ) =
      -(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2) *
        (r.choose (q + 2) : ℚ) := by
  by_cases hr : q + 2 ≤ r
  · have hq : q ≤ r := by omega
    have hq1 : q + 1 ≤ r := by omega
    have h1 : 1 ≤ r := by omega
    have ha := congrArg (fun t : ℕ => (t : ℚ))
      (Nat.choose_succ_right_eq r (q + 1))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub hq1] at ha
    have hbN := Nat.add_one_mul_choose_eq (r - 1) (q + 1)
    rw [Nat.sub_add_cancel h1] at hbN
    have hb := congrArg (fun t : ℕ => (t : ℚ)) hbN
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hb
    have htwo : ((r - q).choose 2 : ℚ) =
        ((r : ℚ) - q) * ((r : ℚ) - q - 1) / 2 := by
      rw [terminal_choose_two_rat, Nat.cast_sub hq]
    rw [htwo, terminal_choose_two_rat]
    have ha' := congrArg (fun t : ℚ => t * ((r : ℚ) - q)) ha
    have hb' := congrArg (fun t : ℚ => t * ((r : ℚ) - 1)) hb
    nlinarith [ha', hb']
  · have hr' : r ≤ q + 1 := by omega
    have hc : r.choose (q + 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have hd : (r - 1).choose (q + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    by_cases hsmall : r < q + 1
    · simp [Nat.choose_eq_zero_of_lt hsmall, hc, hd]
    · have hdiff : r - q = 1 := by omega
      simp [hdiff, hc, hd]

/-- Below the output index both commutator terms cancel to zero, without
ever introducing a negative natural-number variable index. -/
theorem terminal_binomial_bracket_rat_eq_zero_of_le {r q : ℕ}
    (hr : r ≤ q + 1) :
    (r.choose (q + 1) : ℚ) * ((r - q).choose 2 : ℚ) -
        (r.choose 2 : ℚ) * ((r - 1).choose (q + 1) : ℚ) = 0 := by
  rw [terminal_binomial_bracket_rat, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The q=1 commutator is identically zero, including every boundary. -/
theorem terminal_binomial_bracket_rat_one (r : ℕ) :
    (r.choose 2 : ℚ) * ((r - 1).choose 2 : ℚ) -
        (r.choose 2 : ℚ) * ((r - 1).choose 2 : ℚ) = 0 := by ring

/-- The lowering sum is literally empty once q is at least the block size. -/
theorem terminal_lowering_sum_empty {M : Type*} [AddCommMonoid M]
    (d q : ℕ) (f : ℕ → M) (hdq : d ≤ q) :
    ∑ r ∈ Finset.Icc (q + 1) d, f r = 0 := by
  rw [Finset.Icc_eq_empty_of_lt (by omega : d < q + 1)]
  simp

section QAlgebra

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- Ring-hom transport of the exact commutator scalar. In particular,
nilpotents or zero divisors in R impose no restriction. -/
theorem terminal_binomial_bracket_qAlgebra (r q : ℕ) :
    (r.choose (q + 1) : R) * ((r - q).choose 2 : R) -
        (r.choose 2 : R) * ((r - 1).choose (q + 1) : R) =
      algebraMap ℚ R (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)) *
        (r.choose (q + 2) : R) := by
  have h := congrArg (algebraMap ℚ R) (terminal_binomial_bracket_rat r q)
  simpa only [map_sub, map_mul, map_natCast] using h

end QAlgebra

/-- The actual falling-factorial coefficients obey the signed recurrence. -/
theorem signedStirling_succ_succ (n j : ℕ) :
    signedStirling (n + 1) (j + 1) =
      signedStirling n j - (n : ℤ) * signedStirling n (j + 1) := by
  unfold signedStirling
  rw [descPochhammer_succ_right, mul_sub, coeff_sub,
    coeff_mul_X, coeff_mul_natCast]
  ring

/-- The leading falling-factorial coefficient is one. -/
theorem signedStirling_self (n : ℕ) : signedStirling n n = 1 := by
  unfold signedStirling
  have h := (monic_descPochhammer ℤ n).coeff_natDegree
  simpa only [descPochhammer_natDegree] using h

/-- First subdiagonal, indexed so that n=0 is the genuine s(1,0)=0 case. -/
theorem signedStirling_first_subdiagonal_rat (n : ℕ) :
    (signedStirling (n + 1) n : ℚ) =
      -(((n : ℚ) + 1) * (n : ℚ) / 2) := by
  induction n with
  | zero => simp [signedStirling_zero (by omega : 1 ≤ 0 + 1)]
  | succ n ih =>
      have h := congrArg (fun z : ℤ => (z : ℚ))
        (signedStirling_succ_succ (n + 1) n)
      rw [signedStirling_self] at h
      push_cast at h
      rw [ih] at h
      push_cast
      nlinarith

/-- The first component has exactly the binomial coefficient used in V₁. -/
theorem signedStirling_first_subdiagonal_choose_rat (n : ℕ) :
    (signedStirling (n + 1) n : ℚ) = -((n + 1).choose 2 : ℚ) := by
  rw [signedStirling_first_subdiagonal_rat, terminal_choose_two_rat]
  push_cast
  ring

/-- The coefficient of Xⁿ in the actual falling factorial of order n+2.
The formula includes n=0, when the constant term vanishes. -/
theorem signedStirling_second_subdiagonal_rat (n : ℕ) :
    (signedStirling (n + 2) n : ℚ) =
      ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n : ℚ) *
        (3 * ((n : ℚ) + 2) - 1) / 24 := by
  induction n with
  | zero => simp [signedStirling_zero (by omega : 1 ≤ 0 + 2)]
  | succ n ih =>
      have h := congrArg (fun z : ℤ => (z : ℚ))
        (signedStirling_succ_succ (n + 2) n)
      have hfirst : (signedStirling (n + 2) (n + 1) : ℚ) =
          -(((n : ℚ) + 2) * ((n : ℚ) + 1) / 2) := by
        convert signedStirling_first_subdiagonal_rat (n + 1) using 1
        push_cast
        ring
      push_cast at h
      rw [ih, hfirst] at h
      push_cast
      nlinarith

/-- A division-free choose recurrence supplies the rational cubic formula. -/
theorem terminal_choose_three_rat_offset (n : ℕ) :
    ((n + 2).choose 3 : ℚ) =
      ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n : ℚ) / 6 := by
  have hn := Nat.choose_succ_right_eq (n + 2) 2
  simp only [Nat.add_sub_cancel] at hn
  have h := congrArg (fun t : ℕ => (t : ℚ)) hn
  push_cast at h
  rw [terminal_choose_two_rat] at h
  push_cast at h
  nlinarith

/-- The exact second component of the logarithm on one variable, without
constructing a logarithm operator. All s are the existing signed Stirling
coefficients. n=0 includes the vanishing order-two boundary case. -/
theorem signedStirling_log_second_subdiagonal_rat (n : ℕ) :
    (signedStirling (n + 2) n : ℚ) -
        (1 / 2 : ℚ) * (signedStirling (n + 2) (n + 1) : ℚ) *
          (signedStirling (n + 1) n : ℚ) =
      (1 / 2 : ℚ) * ((n + 2).choose 3 : ℚ) := by
  have hfirst : (signedStirling (n + 2) (n + 1) : ℚ) =
      -(((n : ℚ) + 2) * ((n : ℚ) + 1) / 2) := by
    convert signedStirling_first_subdiagonal_rat (n + 1) using 1
    push_cast
    ring
  rw [signedStirling_second_subdiagonal_rat, hfirst,
    signedStirling_first_subdiagonal_rat, terminal_choose_three_rat_offset]
  ring

/-- The first-derivative variable has no second lowering component. This
is the boundary not covered by the order n+2 indexing. -/
theorem signedStirling_log_second_order_one_rat :
    (signedStirling 1 0 : ℚ) -
        (1 / 2 : ℚ) * (signedStirling 1 0 : ℚ) * (signedStirling 0 0 : ℚ) = 0 := by
  rw [signedStirling_zero (by omega : 1 ≤ 1)]
  simp

/-- Transport of the first-component coefficient to a Q-algebra. -/
theorem signedStirling_first_subdiagonal_qAlgebra
    (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    (signedStirling (n + 1) n : R) = -((n + 1).choose 2 : R) := by
  have h := congrArg (algebraMap ℚ R) (signedStirling_first_subdiagonal_choose_rat n)
  simpa only [map_neg, map_intCast, map_natCast] using h

/-- Transport of the second-component identity to every commutative
Q-algebra, expressed using the scalar 1/2 rather than division in R. -/
theorem signedStirling_log_second_subdiagonal_qAlgebra
    (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    (signedStirling (n + 2) n : R) -
        algebraMap ℚ R (1 / 2) * (signedStirling (n + 2) (n + 1) : R) *
          (signedStirling (n + 1) n : R) =
      algebraMap ℚ R (1 / 2) * ((n + 2).choose 3 : R) := by
  have h := congrArg (algebraMap ℚ R) (signedStirling_log_second_subdiagonal_rat n)
  simpa only [map_sub, map_mul, map_intCast, map_natCast] using h

end AbelFormalization
