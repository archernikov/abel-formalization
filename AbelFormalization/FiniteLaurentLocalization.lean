import AbelFormalization.LaurentIdealHeight
import AbelFormalization.MultivariateLaurentIdeal
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finsupp.Fintype

/-!
# The actual finite group algebra as a polynomial localization

Natural polynomial exponents embed
into integer-vector Laurent exponents. A single coordinatewise shift clears
every negative exponent of a Laurent polynomial, including over coefficient
rings with zero divisors.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

/-- The actual natural-to-integer embedding of finite polynomial exponents. -/
def finiteLaurentExponentHom (h : ℕ) : (Fin h →₀ ℕ) →+ (Fin h → ℤ) where
  toFun d i := d i
  map_zero' := rfl
  map_add' d e := by funext i; simp

@[simp]
theorem finiteLaurentExponentHom_apply (h : ℕ) (d : Fin h →₀ ℕ) (i : Fin h) :
    finiteLaurentExponentHom h d i = (d i : ℤ) := rfl

theorem finiteLaurentExponentHom_injective (h : ℕ) :
    Function.Injective (finiteLaurentExponentHom h) := by
  intro d e hde
  apply Finsupp.ext
  intro i
  have hi : (d i : ℤ) = (e i : ℤ) := congrFun hde i
  exact_mod_cast hi

/-- A natural exponent vector associated with an integer vector. Its image
is the original vector whenever that vector is coordinatewise nonnegative. -/
def finiteLaurentNatExponent {h : ℕ} (g : Fin h → ℤ) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (g i).toNat)

@[simp]
theorem finiteLaurentNatExponent_apply {h : ℕ} (g : Fin h → ℤ) (i : Fin h) :
    finiteLaurentNatExponent g i = (g i).toNat := rfl

theorem finiteLaurentExponentHom_natExponent {h : ℕ} (g : Fin h → ℤ)
    (hg : ∀ i, 0 ≤ g i) :
    finiteLaurentExponentHom h (finiteLaurentNatExponent g) = g := by
  funext i
  exact Int.toNat_of_nonneg (hg i)

variable (R : Type*) [CommRing R]

/-- The literal polynomial inclusion into the finite-rank Laurent ring. -/
def finiteLaurentPolynomialHom (h : ℕ) :
    MvPolynomial (Fin h) R →+* AddMonoidAlgebra R (Fin h → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom R (finiteLaurentExponentHom h)

theorem finiteLaurentPolynomialHom_injective (h : ℕ) :
    Function.Injective (finiteLaurentPolynomialHom R h) :=
  AddMonoidAlgebra.mapDomain_injective (finiteLaurentExponentHom_injective h)

@[simp]
theorem finiteLaurentPolynomialHom_monomial (h : ℕ) (d : Fin h →₀ ℕ) (c : R) :
    finiteLaurentPolynomialHom R h (MvPolynomial.monomial d c) =
      AddMonoidAlgebra.single (finiteLaurentExponentHom h d) c := by
  change AddMonoidAlgebra.mapDomain (finiteLaurentExponentHom h)
    (AddMonoidAlgebra.single d c) = _
  exact AddMonoidAlgebra.mapDomain_single

@[simp]
theorem finiteLaurentPolynomialHom_X (h : ℕ) (i : Fin h) :
    finiteLaurentPolynomialHom R h (MvPolynomial.X i) =
      AddMonoidAlgebra.single
        (finiteLaurentExponentHom h (Finsupp.single i 1)) (1 : R) := by
  simpa only [← MvPolynomial.X_pow_eq_monomial, pow_one] using
    finiteLaurentPolynomialHom_monomial R h (Finsupp.single i 1) 1

/-- A single natural shift large enough for the whole finite Laurent support. -/
def finiteLaurentDenominatorExponent {h : ℕ}
    (f : AddMonoidAlgebra R (Fin h → ℤ)) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i => f.coeff.support.sup (fun g => (-g i).toNat))

theorem finiteLaurentDenominatorExponent_nonneg {h : ℕ}
    (f : AddMonoidAlgebra R (Fin h → ℤ)) {g : Fin h → ℤ}
    (hg : g ∈ f.coeff.support) (i : Fin h) :
    0 ≤ (g + finiteLaurentExponentHom h (finiteLaurentDenominatorExponent R f)) i := by
  classical
  have hi : (-g i).toNat ≤ f.coeff.support.sup (fun a => (-a i).toNat) :=
    Finset.le_sup (f := fun a : Fin h → ℤ => (-a i).toNat) hg
  have hnat : -g i ≤ ((-g i).toNat : ℤ) := Int.self_le_toNat (-g i)
  change 0 ≤ g i + ((f.coeff.support.sup (fun a => (-a i).toNat) : ℕ) : ℤ)
  omega

/-- Clearing all negative exponents produces a genuine polynomial with
the same finite coefficient list. -/
theorem finiteLaurentPolynomialHom_clear_denominators (h : ℕ)
    (f : AddMonoidAlgebra R (Fin h → ℤ)) :
    ∃ p : MvPolynomial (Fin h) R, ∃ d : Fin h →₀ ℕ,
      f * finiteLaurentPolynomialHom R h (MvPolynomial.monomial d 1) =
        finiteLaurentPolynomialHom R h p := by
  classical
  let d := finiteLaurentDenominatorExponent R f
  let p : MvPolynomial (Fin h) R :=
    ∑ g ∈ f.coeff.support,
      MvPolynomial.monomial
        (finiteLaurentNatExponent (g + finiteLaurentExponentHom h d)) (f.coeff g)
  have hp : finiteLaurentPolynomialHom R h p =
      ∑ g ∈ f.coeff.support,
        AddMonoidAlgebra.single (g + finiteLaurentExponentHom h d) (f.coeff g) := by
    dsimp only [p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [finiteLaurentPolynomialHom_monomial,
      finiteLaurentExponentHom_natExponent _
        (finiteLaurentDenominatorExponent_nonneg R f hg)]
  refine ⟨p, d, ?_⟩
  rw [finiteLaurentPolynomialHom_monomial, hp]
  calc
    f * AddMonoidAlgebra.single (finiteLaurentExponentHom h d) 1 =
        (f.coeff.sum (fun g c => AddMonoidAlgebra.single g c)) *
          AddMonoidAlgebra.single (finiteLaurentExponentHom h d) 1 :=
      congrArg (fun q => q * AddMonoidAlgebra.single (finiteLaurentExponentHom h d) 1)
        (AddMonoidAlgebra.sum_coeff_single f).symm
    _ = _ := by
      simp only [Finsupp.sum, Finset.sum_mul,
        AddMonoidAlgebra.single_mul_single, mul_one]

/-- Every coefficient-one monomial is a product of the inverted variables. -/
theorem finiteLaurent_monomial_mem_variableSubmonoid (h : ℕ) (d : Fin h →₀ ℕ) :
    MvPolynomial.monomial d (1 : R) ∈ laurentVariableSubmonoid (Fin h) R := by
  classical
  rw [MvPolynomial.monic_monomial_eq, Finsupp.prod]
  apply Submonoid.prod_mem
  intro i hi
  apply Submonoid.pow_mem
  exact Submonoid.subset_closure ⟨i, rfl⟩

/-- Every Laurent group monomial has its literal opposite-exponent inverse. -/
theorem finiteLaurent_single_isUnit (h : ℕ) (g : Fin h → ℤ) :
    IsUnit (AddMonoidAlgebra.single g (1 : R)) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨AddMonoidAlgebra.single (-g) 1, by simp [AddMonoidAlgebra.one_def]⟩

/-- The polynomial algebra structure uses precisely the exponent embedding. -/
instance finiteLaurentPolynomialAlgebra (h : ℕ) :
    Algebra (MvPolynomial (Fin h) R) (AddMonoidAlgebra R (Fin h → ℤ)) :=
  (finiteLaurentPolynomialHom R h).toAlgebra

@[simp]
theorem finiteLaurentPolynomial_algebraMap (h : ℕ) (p : MvPolynomial (Fin h) R) :
    algebraMap (MvPolynomial (Fin h) R) (AddMonoidAlgebra R (Fin h → ℤ)) p =
      finiteLaurentPolynomialHom R h p := rfl

/-- The genuine finite group algebra is the localization of the polynomial
ring at exactly the multiplicative set generated by its variables. -/
instance finiteLaurent_isLocalization (h : ℕ) :
    IsLocalization (laurentVariableSubmonoid (Fin h) R)
      (AddMonoidAlgebra R (Fin h → ℤ)) where
  map_units := by
    rintro ⟨s, hs⟩
    change IsUnit (finiteLaurentPolynomialHom R h s)
    induction hs using Submonoid.closure_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := ha
        rw [finiteLaurentPolynomialHom_X]
        exact finiteLaurent_single_isUnit R h _
    | one => simpa only [map_one] using (isUnit_one : IsUnit (1 : AddMonoidAlgebra R _))
    | mul a b ha hb iha ihb =>
        simpa only [map_mul] using iha.mul ihb
  surj f := by
    obtain ⟨p, d, hpd⟩ := finiteLaurentPolynomialHom_clear_denominators R h f
    refine ⟨(p, ⟨MvPolynomial.monomial d 1,
      finiteLaurent_monomial_mem_variableSubmonoid R h d⟩), ?_⟩
    exact hpd
  exists_of_eq := by
    intro p q hpq
    have heq : p = q := finiteLaurentPolynomialHom_injective R h hpq
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using heq⟩

end AbelFormalization
