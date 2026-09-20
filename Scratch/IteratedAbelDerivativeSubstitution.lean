import AbelFormalization.Stirling

/-!
# Denominator-cleared derivative transport through several Abel iterates

Repeatedly applying the normalized signed-Stirling transport formula gives a
rational expression for `A⁽ʳ⁾ (E^[d] u)` in the jets of `A` at `u`.
This file records an explicit common denominator and numerator.  The
denominator is a finite product of positive exponentials, so it can be used to
clear every exceptional pair-merge jet without adjoining reciprocal
generators.
-/

noncomputable section

open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- A positive common denominator for the order-`r` derivative transported
backwards through `d` iterates of `E`.  At derivative order zero no
denominator is needed. -/
def iteratedAbelDerivativeDenominator (d r : ℕ) (u : ℝ) : ℝ :=
  match d with
  | 0 => 1
  | d + 1 =>
      if r = 0 then 1
      else
        Real.exp ((r : ℝ) * E^[d] u) *
          ∏ j ∈ Finset.range (r + 1),
            iteratedAbelDerivativeDenominator d j u

/-- The corresponding denominator-cleared numerator.  It contains only the
jets at the original point `u`, finite products, sums, real constants, and
finite exponential iterates. -/
def iteratedAbelDerivativeNumerator
    (A : ℝ → ℝ) (d r : ℕ) (u : ℝ) : ℝ :=
  match d with
  | 0 => iteratedDeriv r A u
  | d + 1 =>
      if _hr : r = 0 then A u + (d + 1 : ℝ)
      else
        ∑ j ∈ Finset.range (r + 1),
          (signedStirling r j : ℝ) *
            iteratedAbelDerivativeNumerator A d j u *
              ∏ l ∈ (Finset.range (r + 1)).erase j,
                iteratedAbelDerivativeDenominator d l u

@[simp]
theorem iteratedAbelDerivativeDenominator_zero (r : ℕ) (u : ℝ) :
    iteratedAbelDerivativeDenominator 0 r u = 1 :=
  rfl

@[simp]
theorem iteratedAbelDerivativeNumerator_zero
    (A : ℝ → ℝ) (r : ℕ) (u : ℝ) :
    iteratedAbelDerivativeNumerator A 0 r u = iteratedDeriv r A u :=
  rfl

@[simp]
theorem iteratedAbelDerivativeDenominator_order_zero
    (d : ℕ) (u : ℝ) :
    iteratedAbelDerivativeDenominator d 0 u = 1 := by
  cases d <;> simp [iteratedAbelDerivativeDenominator]

@[simp]
theorem iteratedAbelDerivativeNumerator_order_zero
    (A : ℝ → ℝ) (d : ℕ) (u : ℝ) :
    iteratedAbelDerivativeNumerator A d 0 u = A u + (d : ℝ) := by
  cases d with
  | zero => simp [iteratedAbelDerivativeNumerator]
  | succ d => simp [iteratedAbelDerivativeNumerator]

/-- Every recursively constructed denominator is strictly positive. -/
theorem iteratedAbelDerivativeDenominator_pos
    (d r : ℕ) (u : ℝ) :
    0 < iteratedAbelDerivativeDenominator d r u := by
  induction d generalizing r with
  | zero => simp [iteratedAbelDerivativeDenominator]
  | succ d ih =>
      by_cases hr : r = 0
      · simp [iteratedAbelDerivativeDenominator, hr]
      · rw [iteratedAbelDerivativeDenominator]
        simp only [hr, ↓reduceIte]
        exact mul_pos (Real.exp_pos _)
          (Finset.prod_pos fun j hj ↦ ih j)

/-- The explicit denominator-cleared transport identity through an arbitrary
fixed number of iterates. -/
theorem IsAbel.iteratedAbelDerivative_denominator_mul
    {A : ℝ → ℝ} (hA : IsAbel A) {u : ℝ} (hu : 0 < u)
    (d r : ℕ) :
    iteratedAbelDerivativeDenominator d r u *
        iteratedDeriv r A (E^[d] u) =
      iteratedAbelDerivativeNumerator A d r u := by
  induction d generalizing r with
  | zero => simp [iteratedAbelDerivativeDenominator,
      iteratedAbelDerivativeNumerator]
  | succ d ih =>
      by_cases hr : r = 0
      · subst r
        simp only [iteratedAbelDerivativeDenominator_order_zero,
          one_mul, iteratedDeriv_zero,
          iteratedAbelDerivativeNumerator_order_zero]
        exact hA.abel_iterate hu (d + 1)
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
        have huid : 0 < E^[d] u := E_iterate_pos hu d
        have htransport :=
          hA.iteratedDeriv_transport_normalized r hrpos (E^[d] u) huid
        rw [polynomialJet_descPochhammer] at htransport
        rw [Function.iterate_succ_apply']
        rw [iteratedAbelDerivativeDenominator,
          iteratedAbelDerivativeNumerator]
        simp only [hr, ↓reduceIte]
        let S := Finset.range (r + 1)
        let D : ℕ → ℝ := fun j ↦
          iteratedAbelDerivativeDenominator d j u
        let J : ℕ → ℝ := fun j ↦ iteratedDeriv j A (E^[d] u)
        let N : ℕ → ℝ := fun j ↦
          iteratedAbelDerivativeNumerator A d j u
        have hprodterm : ∀ j ∈ S,
            (∏ l ∈ S, D l) * ((signedStirling r j : ℝ) * J j) =
              (signedStirling r j : ℝ) * N j *
                ∏ l ∈ S.erase j, D l := by
          intro j hj
          have hDj : D j * J j = N j := ih j
          have hsplit : D j * (∏ l ∈ S.erase j, D l) =
              ∏ l ∈ S, D l := by
            exact Finset.mul_prod_erase S D hj
          rw [← hsplit]
          calc
            (D j * ∏ l ∈ S.erase j, D l) *
                  ((signedStirling r j : ℝ) * J j) =
                (signedStirling r j : ℝ) * (D j * J j) *
                  ∏ l ∈ S.erase j, D l := by ring
            _ = (signedStirling r j : ℝ) * N j *
                  ∏ l ∈ S.erase j, D l := by rw [hDj]
        calc
          (Real.exp ((r : ℝ) * E^[d] u) * ∏ j ∈ S, D j) *
                iteratedDeriv r A (E (E^[d] u)) =
              (∏ j ∈ S, D j) *
                (Real.exp ((r : ℝ) * E^[d] u) *
                  iteratedDeriv r A (E (E^[d] u))) := by ring
          _ = (∏ j ∈ S, D j) *
                ∑ j ∈ S,
                  (signedStirling r j : ℝ) * J j := by
                rw [htransport]
          _ = ∑ j ∈ S,
                (∏ l ∈ S, D l) *
                  ((signedStirling r j : ℝ) * J j) := by
                rw [Finset.mul_sum]
          _ = ∑ j ∈ S,
                (signedStirling r j : ℝ) * N j *
                  ∏ l ∈ S.erase j, D l := by
                apply Finset.sum_congr rfl
                intro j hj
                exact hprodterm j hj

end AbelFormalization
