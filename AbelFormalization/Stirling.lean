import AbelFormalization.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Derivative transport and signed Stirling coefficients

The coefficients are defined by the actual falling-factorial polynomial.
Polynomial jet evaluation represents the finite constant-coefficient
differential operator used in the manuscript.
-/

noncomputable section

open Set Filter Polynomial
open scoped Topology

namespace AbelFormalization

def signedStirling (n j : ℕ) : ℤ := (descPochhammer ℤ n).coeff j

theorem cast_signedStirling (n j : ℕ) :
    (signedStirling n j : ℝ) = (descPochhammer ℝ n).coeff j := by
  have h := congrArg (fun p : ℝ[X] => p.coeff j)
    (descPochhammer_map (Int.castRingHom ℝ) n)
  rw [Polynomial.coeff_map] at h
  exact h

theorem signedStirling_zero {n : ℕ} (hn : 1 ≤ n) : signedStirling n 0 = 0 := by
  rw [signedStirling, coeff_zero_eq_eval_zero]
  exact descPochhammer_ne_zero_eval_zero ℤ (by omega)

/-- The defining falling-factorial identity in the manuscript. -/
theorem signedStirling_falling_factorial (n : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range (n + 1), (signedStirling n j : ℝ) * x ^ j =
      ∏ j ∈ Finset.range n, (x - j) := by
  simp_rw [cast_signedStirling]
  have he := Polynomial.eval_eq_sum_range (p := descPochhammer ℝ n) x
  simp only [descPochhammer_natDegree] at he
  rw [← he]
  exact descPochhammer_eval_eq_prod_range n x

/-- Evaluate a polynomial in the differentiation operator on `A`. -/
def polynomialJet (A : ℝ → ℝ) : ℝ[X] →ₗ[ℝ] (ℝ → ℝ) :=
  Polynomial.lsum fun n => (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (iteratedDeriv n A)

@[simp] theorem polynomialJet_monomial (A : ℝ → ℝ) (n : ℕ) (c u : ℝ) :
    polynomialJet A (monomial n c) u = c * iteratedDeriv n A u := by
  simp [polynomialJet, Polynomial.lsum]

@[simp] theorem polynomialJet_X (A : ℝ → ℝ) (u : ℝ) :
    polynomialJet A X u = deriv A u := by
  rw [← monomial_one_one_eq_X]
  simp [iteratedDeriv_one]

theorem polynomialJet_descPochhammer (A : ℝ → ℝ) (n : ℕ) (u : ℝ) :
    polynomialJet A (descPochhammer ℝ n) u =
      ∑ j ∈ Finset.range (n + 1), (signedStirling n j : ℝ) * iteratedDeriv j A u := by
  simp_rw [cast_signedStirling]
  change ((descPochhammer ℝ n).sum (fun j c => c • iteratedDeriv j A)) u = _
  rw [Polynomial.sum_over_range (f := fun j c => c • iteratedDeriv j A)
    _ (by intro j; simp), descPochhammer_natDegree]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem hasDerivAt_iteratedDeriv (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (iteratedDeriv n A) (iteratedDeriv (n + 1) A u) u := by
  rw [iteratedDeriv_succ]
  apply DifferentiableAt.hasDerivAt
  rw [iteratedDeriv_eq_iterate]
  exact ((hA.analytic.iterated_deriv n) u hu).differentiableAt

theorem polynomialJet_hasDerivAt (p : ℝ[X]) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (polynomialJet A p) (polynomialJet A (p * X) u) u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [add_mul, map_add, Pi.add_apply] using hp.add hq
  | monomial n c =>
      rw [Polynomial.monomial_mul_X, polynomialJet_monomial]
      have hf : polynomialJet A (monomial n c) = fun v => c * iteratedDeriv n A v := by
        funext v
        exact polynomialJet_monomial A n c v
      rw [hf]
      exact (hA.hasDerivAt_iteratedDeriv n hu).const_mul c

/-- The normalized all-order derivative transport identity. The polynomial on
the right is exactly `X (X-1) ... (X-n+1)`. -/
theorem iteratedDeriv_transport_normalized (n : ℕ) (hn : 1 ≤ n) :
    ∀ u : ℝ, 0 < u →
      Real.exp ((n : ℝ) * u) * iteratedDeriv n A (E u) =
        polynomialJet A (descPochhammer ℝ n) u := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro u hu
      simp only [Nat.cast_one, one_mul, descPochhammer_one,
        iteratedDeriv_one, polynomialJet_X]
      nlinarith [hA.deriv_abel hu]
  | succ n hn ih =>
      intro u hu
      let p := descPochhammer ℝ n
      have hE : HasDerivAt E (Real.exp u) u := (Real.hasDerivAt_exp u).sub_const 1
      have hex : HasDerivAt (fun v : ℝ => Real.exp ((n : ℝ) * v))
          (Real.exp ((n : ℝ) * u) * (n : ℝ)) u := by
        simpa using ((hasDerivAt_id u).const_mul (n : ℝ)).exp
      have hd := (hA.hasDerivAt_iteratedDeriv n (E_pos hu)).comp u hE
      have hl := hex.mul hd
      have hr := hA.polynomialJet_hasDerivAt p hu
      have heq : (fun v : ℝ => Real.exp ((n : ℝ) * v) * iteratedDeriv n A (E v))
          =ᶠ[𝓝 u] polynomialJet A p := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact ih v hv
      have hdiff := hl.unique (hr.congr_of_eventuallyEq heq)
      have hp : descPochhammer ℝ (n + 1) = p * X - (n : ℝ) • p := by
        rw [descPochhammer_succ_right]
        dsimp [p]
        rw [mul_sub, mul_comm _ (n : ℝ[X]), ← C_eq_natCast, C_mul']
      rw [hp, map_sub, map_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hexp : Real.exp (((n + 1 : ℕ) : ℝ) * u) =
          Real.exp ((n : ℝ) * u) * Real.exp u := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      have hi := ih u hu
      change Real.exp ((n : ℝ) * u) * iteratedDeriv n A (E u) =
        polynomialJet A p u at hi
      have hni := congrArg (fun v : ℝ => (n : ℝ) * v) hi
      simp only [Function.comp_apply] at hdiff
      nlinarith [hni]

/-- The finite signed-Stirling derivative transport formula. The zero-index
summand vanishes for `n ≥ 1`, by `signedStirling_zero`. -/
theorem iteratedDeriv_transport (n : ℕ) (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv n A (E u) = Real.exp (-((n : ℝ) * u)) *
      ∑ j ∈ Finset.range (n + 1), (signedStirling n j : ℝ) * iteratedDeriv j A u := by
  have hnrm := hA.iteratedDeriv_transport_normalized n hn u hu
  rw [polynomialJet_descPochhammer] at hnrm
  have he : Real.exp (-((n : ℝ) * u)) * Real.exp ((n : ℝ) * u) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    iteratedDeriv n A (E u) =
        (Real.exp (-((n : ℝ) * u)) * Real.exp ((n : ℝ) * u)) *
          iteratedDeriv n A (E u) := by rw [he]; simp
    _ = Real.exp (-((n : ℝ) * u)) *
        (Real.exp ((n : ℝ) * u) * iteratedDeriv n A (E u)) := by ring
    _ = _ := by rw [hnrm]

end IsAbel

end AbelFormalization
