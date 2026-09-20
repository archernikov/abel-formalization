import AbelFormalization.IdealHeight
import Mathlib.Algebra.Polynomial.Laurent

/-! # Coefficient ideals and full Laurent contractions

A Laurent series here is a finite Laurent polynomial. Coefficient extension
is characterized by membership of every coefficient, and contraction to the
ordinary polynomial subring recovers the coefficient-extended ideal. This
connects the manuscript's literal Laurent deformation to the checked height
invariance under localization and polynomial extension.
-/

noncomputable section

namespace AbelFormalization

open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- Extending a coefficient ideal to Laurent polynomials is exactly requiring
every Laurent coefficient to belong to the original ideal. -/
theorem laurentPolynomial_mem_map_C_iff (I : Ideal R) (f : LaurentPolynomial R) :
    f ∈ I.map LaurentPolynomial.C ↔ ∀ n : ℤ, f.coeff n ∈ I := by
  classical
  let L : LaurentPolynomial R →+* LaurentPolynomial (R ⧸ I) :=
    AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk I)
  have hker : I.map LaurentPolynomial.C ≤ RingHom.ker L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change L (LaurentPolynomial.C a) = 0
    change AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk I)
      (AddMonoidAlgebra.single 0 a) = 0
    rw [AddMonoidAlgebra.mapRingHom_single, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    simp
  constructor
  · intro hf n
    have hzero : L f = 0 := hker hf
    have he := congrArg (fun g : LaurentPolynomial (R ⧸ I) => g.coeff n) hzero
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [L, AddMonoidAlgebra.coeff_mapRingHom,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he
  · intro hf
    rw [← AddMonoidAlgebra.sum_coeff_single f]
    change (∑ n ∈ f.coeff.support, AddMonoidAlgebra.single n (f.coeff n)) ∈
      I.map LaurentPolynomial.C
    apply Ideal.sum_mem
    intro n hn
    rw [LaurentPolynomial.single_eq_C_mul_T]
    exact (I.map LaurentPolynomial.C).mul_mem_right _ (Ideal.mem_map_of_mem _ (hf n))

/-- Ordinary polynomial coefficients occupy the nonnegative Laurent exponents. -/
@[simp]
theorem polynomial_toLaurent_coeff_nat (f : R[X]) (n : ℕ) :
    (Polynomial.toLaurent f).coeff (n : ℤ) = f.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ) f.toFinsupp.coeff)
    ((Nat.castEmbedding : ℕ ↪ ℤ) n) = f.coeff n
  exact (Finsupp.mapDomain_apply_of_injective
    (Nat.castEmbedding : ℕ ↪ ℤ).injective f.toFinsupp.coeff n).trans
      (Polynomial.toFinsupp_apply f n)

/-- An ordinary polynomial has no negative Laurent coefficient. -/
theorem polynomial_toLaurent_coeff_neg (f : R[X]) (n : ℤ) (hn : n < 0) :
    (Polynomial.toLaurent f).coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, rfl⟩
  exact (not_le_of_gt hn) (Int.natCast_nonneg k)

/-- The coefficient extension contracts from the Laurent ring to its ordinary
polynomial coefficient extension. This is valid without Noetherianity. -/
theorem laurentPolynomial_map_C_comap_toLaurent (I : Ideal R) :
    (I.map LaurentPolynomial.C).comap Polynomial.toLaurent = I.map Polynomial.C := by
  ext f
  rw [Ideal.mem_comap, laurentPolynomial_mem_map_C_iff, Ideal.mem_map_C_iff]
  constructor
  · intro h n
    simpa only [polynomial_toLaurent_coeff_nat] using h (n : ℤ)
  · intro h n
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      rw [polynomial_toLaurent_coeff_nat]
      exact h n
    · rw [polynomial_toLaurent_coeff_neg f n (lt_of_not_ge hn)]
      exact I.zero_mem

/-- Every Laurent contraction is saturated with respect to the ordinary
polynomial variable. -/
theorem laurentPolynomial_comap_cancel_X (J : Ideal (LaurentPolynomial R))
    (f : R[X]) (hf : Polynomial.X * f ∈ J.comap Polynomial.toLaurent) :
    f ∈ J.comap Polynomial.toLaurent := by
  change Polynomial.toLaurent (Polynomial.X * f) ∈ J at hf
  rw [map_mul, Polynomial.toLaurent_X] at hf
  exact (J.unit_mul_mem_iff_mem (LaurentPolynomial.isUnit_T 1)).mp hf

section Height

variable [IsNoetherianRing R]

/-- The arbitrary-ideal polynomial extension height theorem in the literal
univariate polynomial convention. -/
theorem polynomialIdeal_height_map_C (I : Ideal R) :
    (I.map Polynomial.C).height = I.height := by
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  have he : e.toRingEquiv.toRingHom.comp MvPolynomial.C = Polynomial.C := by
    apply RingHom.ext
    intro r
    exact e.commutes r
  calc
    (I.map Polynomial.C).height =
        ((I.map (MvPolynomial.C (σ := Unit))).map e.toRingEquiv.toRingHom).height := by
      rw [Ideal.map_map, he]
    _ = (I.map (MvPolynomial.C (σ := Unit))).height := e.toRingEquiv.height_map _
    _ = I.height := mvPolynomial_height_map_C I

/-- Coefficient extension preserves height in the literal Laurent polynomial
ring, including for nonprime ideals. -/
theorem laurentPolynomialIdeal_height_map_C (I : Ideal R) :
    (I.map LaurentPolynomial.C).height = I.height := by
  calc
    (I.map LaurentPolynomial.C).height =
        ((I.map LaurentPolynomial.C).comap Polynomial.toLaurent).height := by
      exact (idealHeight_localization_under (Submonoid.powers (Polynomial.X : R[X]))
        (I.map LaurentPolynomial.C)).symm
    _ = (I.map Polynomial.C).height := by rw [laurentPolynomial_map_C_comap_toLaurent]
    _ = I.height := polynomialIdeal_height_map_C I

/-- Applying an actual Laurent ring automorphism and then contracting to
ordinary polynomials preserves the original ideal's height. This is the
height step for full homogenization and full weighted deformations. -/
theorem laurentPolynomial_automorphic_contraction_height
    (I : Ideal R) (e : LaurentPolynomial R ≃+* LaurentPolynomial R) :
    (((I.map LaurentPolynomial.C).map e.toRingHom).comap Polynomial.toLaurent).height =
      I.height := by
  calc
    _ = ((I.map LaurentPolynomial.C).map e.toRingHom).height :=
      idealHeight_localization_under (Submonoid.powers (Polynomial.X : R[X])) _
    _ = (I.map LaurentPolynomial.C).height := e.height_map _
    _ = I.height := laurentPolynomialIdeal_height_map_C I

end Height

end AbelFormalization
