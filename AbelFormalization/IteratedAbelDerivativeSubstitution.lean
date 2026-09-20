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

/-! ## Closure in an ambient function algebra -/

/-- The common denominator belongs to any function algebra containing the
finitely many exponential factors used by its recursion. -/
theorem iteratedAbelDerivativeDenominator_mem_subalgebra
    {X : Type*} (B : Subalgebra ℝ (X → ℝ)) (u : X → ℝ)
    (hexp : ∀ d r : ℕ,
      (fun x ↦ Real.exp ((r : ℝ) * E^[d] (u x))) ∈ B) :
    ∀ d r : ℕ,
      (fun x ↦ iteratedAbelDerivativeDenominator d r (u x)) ∈ B := by
  intro d
  induction d with
  | zero =>
      intro r
      change (1 : X → ℝ) ∈ B
      exact B.one_mem
  | succ d ih =>
      intro r
      by_cases hr : r = 0
      · subst r
        change (1 : X → ℝ) ∈ B
        exact B.one_mem
      · have hprod :
            (fun x ↦ ∏ j ∈ Finset.range (r + 1),
              iteratedAbelDerivativeDenominator d j (u x)) ∈ B := by
          have hp : (∏ j ∈ Finset.range (r + 1),
              (fun x ↦ iteratedAbelDerivativeDenominator d j (u x))) ∈ B := by
            apply B.prod_mem
            intro j hj
            exact ih j
          convert hp using 1
          funext x
          simp
        have hmul := B.mul_mem (hexp d r) hprod
        convert hmul using 1
        funext x
        simp [iteratedAbelDerivativeDenominator, hr]

/-- The denominator-cleared numerator belongs to any function algebra
containing all original Abel jets and the exponential factors used by the
common denominators. -/
theorem iteratedAbelDerivativeNumerator_mem_subalgebra
    {X : Type*} (B : Subalgebra ℝ (X → ℝ))
    (A : ℝ → ℝ) (u : X → ℝ)
    (hjet : ∀ r : ℕ, (fun x ↦ iteratedDeriv r A (u x)) ∈ B)
    (hexp : ∀ d r : ℕ,
      (fun x ↦ Real.exp ((r : ℝ) * E^[d] (u x))) ∈ B) :
    ∀ d r : ℕ,
      (fun x ↦ iteratedAbelDerivativeNumerator A d r (u x)) ∈ B := by
  intro d
  induction d with
  | zero =>
      intro r
      simpa [iteratedAbelDerivativeNumerator] using hjet r
  | succ d ih =>
      intro r
      by_cases hr : r = 0
      · subst r
        have hA : (fun x ↦ A (u x)) ∈ B := by
          simpa only [iteratedDeriv_zero] using hjet 0
        have hc : (fun _ : X ↦ ((d + 1 : ℕ) : ℝ)) ∈ B := by
          exact B.algebraMap_mem _
        have hadd := B.add_mem hA hc
        convert hadd using 1
        funext x
        simp [iteratedAbelDerivativeNumerator]
      · have hdenom : ∀ q : ℕ,
            (fun x ↦ iteratedAbelDerivativeDenominator d q (u x)) ∈ B :=
          fun q ↦ iteratedAbelDerivativeDenominator_mem_subalgebra
            B u hexp d q
        have hsum :
            (fun x ↦ ∑ j ∈ Finset.range (r + 1),
              (signedStirling r j : ℝ) *
                iteratedAbelDerivativeNumerator A d j (u x) *
                  ∏ l ∈ (Finset.range (r + 1)).erase j,
                    iteratedAbelDerivativeDenominator d l (u x)) ∈ B := by
          have hs : (∑ j ∈ Finset.range (r + 1),
              (fun x ↦ (signedStirling r j : ℝ) *
                iteratedAbelDerivativeNumerator A d j (u x) *
                  ∏ l ∈ (Finset.range (r + 1)).erase j,
                    iteratedAbelDerivativeDenominator d l (u x))) ∈ B := by
            apply B.sum_mem
            intro j hj
            have hc : (fun _ : X ↦ (signedStirling r j : ℝ)) ∈ B :=
              B.algebraMap_mem _
            have hn := ih j
            have hp :
                (fun x ↦ ∏ l ∈ (Finset.range (r + 1)).erase j,
                  iteratedAbelDerivativeDenominator d l (u x)) ∈ B := by
              have hp' : (∏ l ∈ (Finset.range (r + 1)).erase j,
                  (fun x ↦ iteratedAbelDerivativeDenominator d l (u x))) ∈ B := by
                apply B.prod_mem
                intro l hl
                exact hdenom l
              convert hp' using 1
              funext x
              simp
            exact B.mul_mem (B.mul_mem hc hn) hp
          convert hs using 1
          funext x
          simp
        convert hsum using 1
        funext x
        simp [iteratedAbelDerivativeNumerator, hr]

/-- Natural scalar multiples in the exponential introduce no new generator:
they are powers of the original exponential. -/
theorem realExp_nat_mul_mem_subalgebra
    {X : Type*} (B : Subalgebra ℝ (X → ℝ)) (f : X → ℝ)
    (hf : (fun x ↦ Real.exp (f x)) ∈ B) (r : ℕ) :
    (fun x ↦ Real.exp ((r : ℝ) * f x)) ∈ B := by
  have hp := B.pow_mem hf r
  convert hp using 1
  funext x
  rw [show (r : ℝ) * f x = (r : ℕ) * f x by rfl,
    Real.exp_nat_mul, Pi.pow_apply]

/-- It suffices to contain one ordinary exponential at every orbit point in
order to contain every recursive common denominator. -/
theorem iteratedAbelDerivativeDenominator_mem_subalgebra_of_exp_orbit
    {X : Type*} (B : Subalgebra ℝ (X → ℝ)) (u : X → ℝ)
    (horbit : ∀ d : ℕ, (fun x ↦ Real.exp (E^[d] (u x))) ∈ B) :
    ∀ d r : ℕ,
      (fun x ↦ iteratedAbelDerivativeDenominator d r (u x)) ∈ B := by
  apply iteratedAbelDerivativeDenominator_mem_subalgebra B u
  intro d r
  exact realExp_nat_mul_mem_subalgebra B
    (fun x ↦ E^[d] (u x)) (horbit d) r

/-- The same orbit-exponential hypothesis and the original jets suffice for
every denominator-cleared numerator. -/
theorem iteratedAbelDerivativeNumerator_mem_subalgebra_of_exp_orbit
    {X : Type*} (B : Subalgebra ℝ (X → ℝ))
    (A : ℝ → ℝ) (u : X → ℝ)
    (hjet : ∀ r : ℕ, (fun x ↦ iteratedDeriv r A (u x)) ∈ B)
    (horbit : ∀ d : ℕ, (fun x ↦ Real.exp (E^[d] (u x))) ∈ B) :
    ∀ d r : ℕ,
      (fun x ↦ iteratedAbelDerivativeNumerator A d r (u x)) ∈ B := by
  apply iteratedAbelDerivativeNumerator_mem_subalgebra B A u hjet
  intro d r
  exact realExp_nat_mul_mem_subalgebra B
    (fun x ↦ E^[d] (u x)) (horbit d) r

/-- Bounded form of denominator closure: transport through `d` iterates uses
only the orbit exponentials at indices strictly below `d`. -/
theorem iteratedAbelDerivativeDenominator_mem_subalgebra_bounded
    {X : Type*} (B : Subalgebra ℝ (X → ℝ)) (u : X → ℝ)
    (d : ℕ)
    (hexp : ∀ e < d, ∀ r : ℕ,
      (fun x ↦ Real.exp ((r : ℝ) * E^[e] (u x))) ∈ B) :
    ∀ r : ℕ,
      (fun x ↦ iteratedAbelDerivativeDenominator d r (u x)) ∈ B := by
  induction d with
  | zero =>
      intro r
      change (1 : X → ℝ) ∈ B
      exact B.one_mem
  | succ d ih =>
      intro r
      by_cases hr : r = 0
      · subst r
        change (1 : X → ℝ) ∈ B
        exact B.one_mem
      · have hprev : ∀ q : ℕ,
            (fun x ↦ iteratedAbelDerivativeDenominator d q (u x)) ∈ B :=
          ih (fun e he q ↦ hexp e (lt_trans he (Nat.lt_succ_self d)) q)
        have hp :
            (fun x ↦ ∏ j ∈ Finset.range (r + 1),
              iteratedAbelDerivativeDenominator d j (u x)) ∈ B := by
          have hp' : (∏ j ∈ Finset.range (r + 1),
              (fun x ↦ iteratedAbelDerivativeDenominator d j (u x))) ∈ B := by
            apply B.prod_mem
            intro j hj
            exact hprev j
          convert hp' using 1
          funext x
          simp
        have hm := B.mul_mem (hexp d (Nat.lt_succ_self d) r) hp
        convert hm using 1
        funext x
        simp [iteratedAbelDerivativeDenominator, hr]

/-- Bounded numerator closure with the same exact orbit range. -/
theorem iteratedAbelDerivativeNumerator_mem_subalgebra_bounded
    {X : Type*} (B : Subalgebra ℝ (X → ℝ))
    (A : ℝ → ℝ) (u : X → ℝ)
    (hjet : ∀ r : ℕ, (fun x ↦ iteratedDeriv r A (u x)) ∈ B)
    (d : ℕ)
    (hexp : ∀ e < d, ∀ r : ℕ,
      (fun x ↦ Real.exp ((r : ℝ) * E^[e] (u x))) ∈ B) :
    ∀ r : ℕ,
      (fun x ↦ iteratedAbelDerivativeNumerator A d r (u x)) ∈ B := by
  induction d with
  | zero =>
      intro r
      simpa [iteratedAbelDerivativeNumerator] using hjet r
  | succ d ih =>
      intro r
      by_cases hr : r = 0
      · subst r
        have hA : (fun x ↦ A (u x)) ∈ B := by
          simpa only [iteratedDeriv_zero] using hjet 0
        have hc : (fun _ : X ↦ ((d + 1 : ℕ) : ℝ)) ∈ B :=
          B.algebraMap_mem _
        convert B.add_mem hA hc using 1
        funext x
        simp [iteratedAbelDerivativeNumerator]
      · let hexpPrev : ∀ e < d, ∀ q : ℕ,
            (fun x ↦ Real.exp ((q : ℝ) * E^[e] (u x))) ∈ B :=
          fun e he q ↦ hexp e (lt_trans he (Nat.lt_succ_self d)) q
        have hnum : ∀ q : ℕ,
            (fun x ↦ iteratedAbelDerivativeNumerator A d q (u x)) ∈ B :=
          ih hexpPrev
        have hden : ∀ q : ℕ,
            (fun x ↦ iteratedAbelDerivativeDenominator d q (u x)) ∈ B :=
          iteratedAbelDerivativeDenominator_mem_subalgebra_bounded
            B u d hexpPrev
        have hs : (∑ j ∈ Finset.range (r + 1),
            (fun x ↦ (signedStirling r j : ℝ) *
              iteratedAbelDerivativeNumerator A d j (u x) *
                ∏ l ∈ (Finset.range (r + 1)).erase j,
                  iteratedAbelDerivativeDenominator d l (u x))) ∈ B := by
          apply B.sum_mem
          intro j hj
          have hc : (fun _ : X ↦ (signedStirling r j : ℝ)) ∈ B :=
            B.algebraMap_mem _
          have hp :
              (fun x ↦ ∏ l ∈ (Finset.range (r + 1)).erase j,
                iteratedAbelDerivativeDenominator d l (u x)) ∈ B := by
            have hp' : (∏ l ∈ (Finset.range (r + 1)).erase j,
                (fun x ↦ iteratedAbelDerivativeDenominator d l (u x))) ∈ B := by
              apply B.prod_mem
              intro l hl
              exact hden l
            convert hp' using 1
            funext x
            simp
          exact B.mul_mem (B.mul_mem hc (hnum j)) hp
        convert hs using 1
        funext x
        simp [iteratedAbelDerivativeNumerator, hr]

/-- Bounded orbit version: ordinary exponentials of `E^[e] u`, for `e < d`,
generate all denominator-cleared numerators at depth `d`. -/
theorem iteratedAbelDerivativeNumerator_mem_subalgebra_bounded_of_exp_orbit
    {X : Type*} (B : Subalgebra ℝ (X → ℝ))
    (A : ℝ → ℝ) (u : X → ℝ)
    (hjet : ∀ r : ℕ, (fun x ↦ iteratedDeriv r A (u x)) ∈ B)
    (d : ℕ)
    (horbit : ∀ e < d, (fun x ↦ Real.exp (E^[e] (u x))) ∈ B) :
    ∀ r : ℕ,
      (fun x ↦ iteratedAbelDerivativeNumerator A d r (u x)) ∈ B := by
  apply iteratedAbelDerivativeNumerator_mem_subalgebra_bounded B A u hjet d
  intro e he r
  exact realExp_nat_mul_mem_subalgebra B
    (fun x ↦ E^[e] (u x)) (horbit e he) r

/-- The analogous bounded orbit criterion for the common denominator. -/
theorem iteratedAbelDerivativeDenominator_mem_subalgebra_bounded_of_exp_orbit
    {X : Type*} (B : Subalgebra ℝ (X → ℝ)) (u : X → ℝ)
    (d : ℕ)
    (horbit : ∀ e < d, (fun x ↦ Real.exp (E^[e] (u x))) ∈ B) :
    ∀ r : ℕ,
      (fun x ↦ iteratedAbelDerivativeDenominator d r (u x)) ∈ B := by
  apply iteratedAbelDerivativeDenominator_mem_subalgebra_bounded B u d
  intro e he r
  exact realExp_nat_mul_mem_subalgebra B
    (fun x ↦ E^[e] (u x)) (horbit e he) r

end AbelFormalization
