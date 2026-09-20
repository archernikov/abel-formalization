import AbelFormalization.PolynomialGermIdentities
import AbelFormalization.PolynomialFamilyFormalJacobian

set_option autoImplicit false

/-!
# Padding a finite coefficient family by zero

Only the coefficient functions on the chosen finite monomial set are used
by a polynomial family. Replacing every other coefficient by the zero
function supplies analytic functions at all exponents without changing the
actual polynomial family, its evaluation, or its formal Jacobian.
-/

noncomputable section

open Set
open scoped Topology

namespace AbelFormalization

section Padding

variable {α E : Type*}

/-- Keep an entire coefficient function on the selected finite set and
use the identically zero function outside it. -/
def zeroPadCoefficients (s : Finset α) (a : α → E → ℝ) : α → E → ℝ := by
  classical
  exact fun d => if d ∈ s then a d else fun _ => 0

@[simp]
theorem zeroPadCoefficients_of_mem (s : Finset α) (a : α → E → ℝ)
    {d : α} (hd : d ∈ s) : zeroPadCoefficients s a d = a d := by
  classical
  simp only [zeroPadCoefficients, ite_eq_left hd]

@[simp]
theorem zeroPadCoefficients_of_not_mem (s : Finset α) (a : α → E → ℝ)
    {d : α} (hd : d ∉ s) : zeroPadCoefficients s a d = (fun _ : E => 0) := by
  classical
  simp only [zeroPadCoefficients, ite_eq_right hd]

end Padding

section Analyticity

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Supported analyticity at a point gives analyticity at every index
after padding; no information about the omitted functions is required. -/
theorem analyticAt_zeroPadCoefficients (s : Finset α) (a : α → E → ℝ)
    (x : E) (ha : ∀ d ∈ s, AnalyticAt ℝ (a d) x) :
    ∀ d, AnalyticAt ℝ (zeroPadCoefficients s a d) x := by
  classical
  intro d
  by_cases hd : d ∈ s
  · rw [zeroPadCoefficients_of_mem s a hd]
    exact ha d hd
  · rw [zeroPadCoefficients_of_not_mem s a hd]
    exact analyticAt_const

/-- Supported analyticity on the given neighborhood gives analyticity
of every padded coefficient on that same neighborhood. -/
theorem analyticOnNhd_zeroPadCoefficients (s : Finset α) (a : α → E → ℝ)
    (W : Set E) (ha : ∀ d ∈ s, AnalyticOnNhd ℝ (a d) W) :
    ∀ d, AnalyticOnNhd ℝ (zeroPadCoefficients s a d) W := by
  intro d x hx
  exact analyticAt_zeroPadCoefficients s a x (fun e he => ha e he x hx) d

/-- Padding preserves the full Fréchet derivative of each supported
coefficient because it preserves the coefficient function itself. -/
theorem fderiv_zeroPadCoefficients_of_mem (s : Finset α) (a : α → E → ℝ)
    {d : α} (hd : d ∈ s) (x : E) :
    fderiv ℝ (zeroPadCoefficients s a d) x = fderiv ℝ (a d) x := by
  rw [zeroPadCoefficients_of_mem s a hd]

/-- At a supported index, padding also preserves the actual analytic germ,
independently of which proofs of analyticity are used. -/
theorem analyticGermOf_zeroPadCoefficients_of_mem
    (s : Finset α) (a : α → E → ℝ) {d : α} (hd : d ∈ s) (x : E)
    (hpad : AnalyticAt ℝ (zeroPadCoefficients s a d) x)
    (ha : AnalyticAt ℝ (a d) x) :
    analyticGermOf (zeroPadCoefficients s a d) hpad = analyticGermOf (a d) ha := by
  apply Subtype.ext
  change ((zeroPadCoefficients s a d) : Filter.Germ (𝓝 x) ℝ) =
    ((a d) : Filter.Germ (𝓝 x) ℝ)
  rw [zeroPadCoefficients_of_mem s a hd]

end Analyticity

section PolynomialFamilies

variable {ι E : Type*}

/-- The literal finite polynomial sum is unchanged for every parameter. -/
theorem sum_monomial_zeroPadCoefficients (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (w : E) :
    (∑ d ∈ s, MvPolynomial.monomial d (zeroPadCoefficients s a d w)) =
      ∑ d ∈ s, MvPolynomial.monomial d (a d w) := by
  classical
  apply Finset.sum_congr rfl
  intro d hd
  rw [zeroPadCoefficients_of_mem s a hd]

/-- The canonical finite polynomial representative is exactly unchanged
as a function, rather than merely having the same germ. -/
theorem polynomialFromCoefficientRepresentatives_zeroPadCoefficients
    (s : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → E → ℝ) :
    polynomialFromCoefficientRepresentatives s (zeroPadCoefficients s a) =
      polynomialFromCoefficientRepresentatives s a := by
  funext w
  exact sum_monomial_zeroPadCoefficients s a w

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The same identity holds for finite sums of directional coefficient
derivatives without any differentiability assumption outside the support. -/
theorem sum_monomial_fderiv_zeroPadCoefficients (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (x v : E) :
    (∑ d ∈ s, MvPolynomial.monomial d
        (fderiv ℝ (zeroPadCoefficients s a d) x v)) =
      ∑ d ∈ s, MvPolynomial.monomial d (fderiv ℝ (a d) x v) := by
  classical
  apply Finset.sum_congr rfl
  intro d hd
  rw [zeroPadCoefficients_of_mem s a hd]

end PolynomialFamilies

section EvaluatedFamilies

variable {ι : Type*} {p n : ℕ}

/-- Rowwise padding allows each polynomial equation to retain its own
finite support and leaves the entire evaluated system unchanged. -/
theorem polynomialFamilyEvaluation_zeroPadCoefficients {E : Type*}
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (w : E → Fin p → ℝ) (z : E → ι → ℝ) :
    polynomialFamilyEvaluation s (fun i => zeroPadCoefficients (s i) (a i)) w z =
      polynomialFamilyEvaluation s a w z := by
  funext x i
  change MvPolynomial.eval (z x)
      (∑ d ∈ s i, MvPolynomial.monomial d (zeroPadCoefficients (s i) (a i) d (w x))) =
    MvPolynomial.eval (z x) (∑ d ∈ s i, MvPolynomial.monomial d (a i d (w x)))
  exact congrArg (MvPolynomial.eval (z x))
    (sum_monomial_zeroPadCoefficients (s i) (a i) (w x))

/-- Both the coefficient-partial block and the symbol-partial block of
the formal Jacobian are unchanged by rowwise padding. In the first block,
equality of supported functions is used before taking their derivatives. -/
theorem polynomialFamilyFormalJacobian_zeroPadCoefficients
    (s : Fin n → Finset (ι →₀ ℕ))
    (a : Fin n → (ι →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (u : Fin p → ℝ) (z : ι → ℝ) :
    polynomialFamilyFormalJacobian s (fun i => zeroPadCoefficients (s i) (a i)) u z =
      polynomialFamilyFormalJacobian s a u z := by
  funext i j
  cases j with
  | inl j =>
    change MvPolynomial.eval z
      (∑ d ∈ s i, MvPolynomial.monomial d
        (fderiv ℝ (zeroPadCoefficients (s i) (a i) d) u (Pi.single j 1))) =
      MvPolynomial.eval z (∑ d ∈ s i, MvPolynomial.monomial d
        (fderiv ℝ (a i d) u (Pi.single j 1)))
    exact congrArg (MvPolynomial.eval z)
      (sum_monomial_fderiv_zeroPadCoefficients (s i) (a i) u (Pi.single j 1))
  | inr j =>
    change MvPolynomial.eval z (MvPolynomial.pderiv j
      (∑ d ∈ s i, MvPolynomial.monomial d (zeroPadCoefficients (s i) (a i) d u))) =
      MvPolynomial.eval z (MvPolynomial.pderiv j
        (∑ d ∈ s i, MvPolynomial.monomial d (a i d u)))
    exact congrArg (fun Q => MvPolynomial.eval z (MvPolynomial.pderiv j Q))
      (sum_monomial_zeroPadCoefficients (s i) (a i) u)

end EvaluatedFamilies

end AbelFormalization
