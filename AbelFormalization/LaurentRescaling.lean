import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Integer-weight Laurent rescaling

Flattening the Laurent and polynomial exponents identifies rescaling with an
actual additive monoid automorphism. The coefficient formula records the
absence of cancellation between different original Laurent exponents at a
fixed polynomial monomial, which is the key algebraic fact in the paper's
full initial-ideal construction.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*} [CommSemiring R]

/-- Integer rescaling is a shear of the Laurent exponent by the polynomial
monomial's weight. No sign restriction on the variable weights is needed. -/
def laurentExponentShear (ω : ι → ℤ) :
    (ℤ × (ι →₀ ℕ)) ≃+ (ℤ × (ι →₀ ℕ)) where
  toFun a := (a.1 + Finsupp.weight ω a.2, a.2)
  invFun a := (a.1 - Finsupp.weight ω a.2, a.2)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

@[simp]
theorem laurentExponentShear_apply (ω : ι → ℤ) (n : ℤ) (d : ι →₀ ℕ) :
    laurentExponentShear ω (n, d) = (n + Finsupp.weight ω d, d) := rfl

@[simp]
theorem laurentExponentShear_symm_apply (ω : ι → ℤ) (n : ℤ) (d : ι →₀ ℕ) :
    (laurentExponentShear ω).symm (n, d) = (n - Finsupp.weight ω d, d) := rfl

/-- Flattening separates the integer Laurent exponent from the natural
polynomial multi-index. -/
def laurentPolynomialFlatten :
    LaurentPolynomial (MvPolynomial ι R) ≃ₐ[R]
      AddMonoidAlgebra R (ℤ × (ι →₀ ℕ)) :=
  (AddMonoidAlgebra.curryAlgEquiv R).symm

@[simp]
theorem laurentPolynomialFlatten_coeff
    (f : LaurentPolynomial (MvPolynomial ι R)) (n : ℤ) (d : ι →₀ ℕ) :
    (laurentPolynomialFlatten f).coeff (n, d) = (f.coeff n).coeff d := rfl

@[simp]
theorem laurentPolynomialFlatten_symm_coeff
    (f : AddMonoidAlgebra R (ℤ × (ι →₀ ℕ))) (n : ℤ) (d : ι →₀ ℕ) :
    ((laurentPolynomialFlatten.symm f).coeff n).coeff d =
      f.coeff (n, d) := rfl

@[simp]
theorem laurentPolynomialFlatten_monomial (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    laurentPolynomialFlatten
      (LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n) =
      AddMonoidAlgebra.single (n, d) c := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← MvPolynomial.single_eq_monomial]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single n d c

@[simp]
theorem laurentPolynomialFlatten_symm_single (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    laurentPolynomialFlatten.symm (AddMonoidAlgebra.single (n, d) c) =
      LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n := by
  rw [← laurentPolynomialFlatten_monomial]
  exact laurentPolynomialFlatten.symm_apply_apply _

/-- The actual coefficient-fixing automorphism `zᵢ ↦ τ^(ωᵢ) zᵢ`, with
the Laurent parameter `τ` fixed. -/
def laurentWeightRescaling (ω : ι → ℤ) :
    LaurentPolynomial (MvPolynomial ι R) ≃ₐ[R]
      LaurentPolynomial (MvPolynomial ι R) :=
  laurentPolynomialFlatten.trans
    ((AddMonoidAlgebra.domCongr R R (laurentExponentShear ω)).trans
      laurentPolynomialFlatten.symm)

/-- Exact action on every Laurent-polynomial monomial. -/
@[simp]
theorem laurentWeightRescaling_monomial (ω : ι → ℤ)
    (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    laurentWeightRescaling ω
      (LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n) =
      LaurentPolynomial.C (MvPolynomial.monomial d c) *
        LaurentPolynomial.T (n + Finsupp.weight ω d) := by
  simp [laurentWeightRescaling]

/-- Each resulting pair of exponents has exactly one preimage. In particular,
the deformation's polynomiality can be checked without a domain assumption. -/
@[simp]
theorem laurentWeightRescaling_coeff (ω : ι → ℤ)
    (f : LaurentPolynomial (MvPolynomial ι R)) (n : ℤ) (d : ι →₀ ℕ) :
    ((laurentWeightRescaling ω f).coeff n).coeff d =
      (f.coeff (n - Finsupp.weight ω d)).coeff d := by
  simp [laurentWeightRescaling]

/-- The inverse shifts each Laurent exponent by the opposite amount. -/
@[simp]
theorem laurentWeightRescaling_symm_monomial (ω : ι → ℤ)
    (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    (laurentWeightRescaling ω).symm
      (LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n) =
      LaurentPolynomial.C (MvPolynomial.monomial d c) *
        LaurentPolynomial.T (n - Finsupp.weight ω d) := by
  apply (laurentWeightRescaling ω).injective
  simp

@[simp]
theorem laurentWeightRescaling_T (ω : ι → ℤ) (n : ℤ) :
    laurentWeightRescaling (R := R) ω (LaurentPolynomial.T n) =
      LaurentPolynomial.T n := by
  simpa only [← MvPolynomial.one_def, map_one, one_mul, map_zero, add_zero] using
    laurentWeightRescaling_monomial (R := R) ω n 0 1

@[simp]
theorem laurentWeightRescaling_C_C (ω : ι → ℤ) (c : R) :
    laurentWeightRescaling ω (LaurentPolynomial.C (MvPolynomial.C c)) =
      LaurentPolynomial.C (MvPolynomial.C c) := by
  simpa only [← MvPolynomial.C_apply, LaurentPolynomial.T_zero, mul_one,
    map_zero, add_zero] using laurentWeightRescaling_monomial ω 0 0 c

@[simp]
theorem laurentWeightRescaling_C_X (ω : ι → ℤ) (i : ι) :
    laurentWeightRescaling (R := R) ω (LaurentPolynomial.C (MvPolynomial.X i)) =
      LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T (ω i) := by
  simpa only [← MvPolynomial.X_pow_eq_monomial, pow_one,
    LaurentPolynomial.T_zero, mul_one, zero_add, Finsupp.weight_single, one_smul] using
    laurentWeightRescaling_monomial (R := R) ω 0 (Finsupp.single i 1) 1

theorem finsupp_weight_neg (ω : ι → ℤ) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => -ω i) d = -Finsupp.weight ω d := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib]

theorem finsupp_weight_add (ω ν : ι → ℤ) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => ω i + ν i) d =
      Finsupp.weight ω d + Finsupp.weight ν d := by
  simp [Finsupp.weight_apply, Finsupp.sum, mul_add, Finset.sum_add_distrib]

/-- The inverse rescaling is the one with all variable weights negated. -/
theorem laurentWeightRescaling_symm (ω : ι → ℤ) :
    (laurentWeightRescaling (R := R) ω).symm =
      laurentWeightRescaling (fun i => -ω i) := by
  apply AlgEquiv.ext
  intro f
  apply (laurentWeightRescaling ω).injective
  rw [AlgEquiv.apply_symm_apply]
  apply LaurentPolynomial.ext
  intro n
  apply MvPolynomial.ext
  intro d
  simp only [laurentWeightRescaling_coeff, finsupp_weight_neg, sub_neg_eq_add,
    sub_add_cancel]

/-- Successive rescalings add their weight vectors. -/
theorem laurentWeightRescaling_trans (ω ν : ι → ℤ) :
    (laurentWeightRescaling (R := R) ω).trans (laurentWeightRescaling ν) =
      laurentWeightRescaling (fun i => ω i + ν i) := by
  apply AlgEquiv.ext
  intro f
  apply LaurentPolynomial.ext
  intro n
  apply MvPolynomial.ext
  intro d
  change ((laurentWeightRescaling ν (laurentWeightRescaling ω f)).coeff n).coeff d = _
  simp only [laurentWeightRescaling_coeff, finsupp_weight_add]
  congr 2
  abel_nf

end AbelFormalization
