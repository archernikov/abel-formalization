import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Height under polynomial extension and contraction

This proves part (1) of the paper's Lemma `lem:height`. Heights take values in
`ℕ∞`; both the addition and subtraction formulations are supplied. It also
proves height preservation under polynomial extension, a step used in part (2).
The finite-dimensional hypothesis in the paper is not needed for these facts.
-/

noncomputable section

namespace AbelFormalization

open Ideal

variable {R : Type*} [CommRing R]

/-- Localization preserves the height of any contracted ideal. -/
theorem idealHeight_localization_under (M : Submonoid R) {S : Type*} [CommRing S]
    [Algebra R S] [IsLocalization M S] (J : Ideal S) :
    (J.comap (algebraMap R S)).height = J.height :=
  IsLocalization.height_under M J

variable [IsNoetherianRing R] {ι : Type*} [Finite ι]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- A prime of a finite polynomial ring has height at most the height of its
contraction plus the number of polynomial variables. -/
theorem mvPolynomial_prime_height_le_comap_add_card
    (P : Ideal (MvPolynomial ι R)) [P.IsPrime] :
    P.height ≤ (P.comap MvPolynomial.C).height + Nat.card ι := by
  let p : Ideal R := P.comap MvPolynomial.C
  let Rₚ := Localization.AtPrime p
  let P' : Ideal (MvPolynomial ι Rₚ) := P.map (algebraMap _ _)
  have hdisj : Disjoint (↑(p.primeCompl.map (MvPolynomial.C (σ := ι))) :
      Set (MvPolynomial ι R)) P := by
    refine Set.disjoint_left.mpr ?_
    rintro a ⟨b, hb, rfl⟩ ha
    exact hb ha
  have hP' : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (p.primeCompl.map MvPolynomial.C)
      (MvPolynomial ι Rₚ) P inferInstance hdisj
  have hheight : P'.height = P.height :=
    IsLocalization.height_map_of_disjoint (p.primeCompl.map MvPolynomial.C) P hdisj
  have hdim := Ideal.height_le_ringKrullDim_of_isPrime (I := P')
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ, hheight] at hdim
  exact_mod_cast hdim

/-- The height inequality for an arbitrary ideal in finitely many polynomial
variables. This is Lemma `lem:height`(1), in addition form. -/
theorem mvPolynomial_height_le_comap_add_card (I : Ideal (MvPolynomial ι R)) :
    I.height ≤ (I.comap MvPolynomial.C).height + Nat.card ι := by
  rw [(I.comap MvPolynomial.C).height_eq_inf_minimalPrimes, ENat.iInf₂_add]
  refine le_iInf₂ fun p hp ↦ ?_
  obtain ⟨P, hP, hcontract⟩ :=
    Ideal.exists_minimalPrimes_comap_eq MvPolynomial.C p hp
  have : P.IsPrime := hP.isPrime
  exact (Ideal.height_mono hP.le).trans
    ((mvPolynomial_prime_height_le_comap_add_card P).trans_eq (by rw [hcontract]))

/-- The same contraction bound with a specified number of variables. -/
theorem mvPolynomial_height_le_comap_add (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) :
    I.height ≤ (I.comap MvPolynomial.C).height + n := by
  simpa using mvPolynomial_height_le_comap_add_card I

/-- The subtraction form used in the manuscript. -/
theorem mvPolynomial_height_sub_card_le_comap (I : Ideal (MvPolynomial ι R)) :
    I.height - Nat.card ι ≤ (I.comap MvPolynomial.C).height :=
  tsub_le_iff_right.mpr (mvPolynomial_height_le_comap_add_card I)

/-- Under going down, contraction cannot increase ideal height. -/
theorem idealHeight_comap_le_of_hasGoingDown {S : Type*} [CommRing S]
    [Algebra R S] [IsNoetherianRing S] [Algebra.HasGoingDown R S] (I : Ideal S) :
    (I.comap (algebraMap R S)).height ≤ I.height := by
  rw [I.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun P hP ↦ ?_
  have : P.IsPrime := hP.isPrime
  refine (Ideal.height_mono (Ideal.comap_mono hP.le)).trans ?_
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  exact le_self_add

omit [IsNoetherianRing R] [Finite ι] in
private theorem mvPolynomial_comap_map_C (I : Ideal R) :
    (I.map (MvPolynomial.C (σ := ι))).comap MvPolynomial.C = I := by
  classical
  ext x
  change MvPolynomial.C x ∈ I.map MvPolynomial.C ↔ x ∈ I
  rw [MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h d
    by_cases hd : 0 = d <;> simp [MvPolynomial.coeff_C, hd, h]

/-- Extending a prime ideal to a polynomial ring preserves its height. -/
theorem mvPolynomial_prime_height_map_C (p : Ideal R) [p.IsPrime] :
    (p.map (MvPolynomial.C (σ := ι))).height = p.height := by
  have hker : p.map (MvPolynomial.C (σ := ι)) =
      RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk p)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  have : (p.map (MvPolynomial.C (σ := ι))).IsPrime := by
    rw [hker]
    exact RingHom.ker_isPrime _
  have : (p.map (MvPolynomial.C (σ := ι))).LiesOver p :=
    ⟨(mvPolynomial_comap_map_C p).symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p]
  change p.height + ((p.map (MvPolynomial.C (σ := ι))).map
    (Ideal.Quotient.mk (p.map (MvPolynomial.C (σ := ι))))).height = p.height
  rw [Ideal.map_quotient_self, Ideal.height_bot, add_zero]

/-- Extending any ideal to a finite polynomial ring preserves its height.
This is the polynomial-extension step in Lemma `lem:height`(2). -/
theorem mvPolynomial_height_map_C (I : Ideal R) :
    (I.map (MvPolynomial.C (σ := ι))).height = I.height := by
  apply le_antisymm
  · rw [I.height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun p hp ↦ ?_
    have : p.IsPrime := hp.isPrime
    exact (Ideal.height_mono (Ideal.map_mono hp.le)).trans_eq
      (mvPolynomial_prime_height_map_C p)
  · simpa only [MvPolynomial.algebraMap_eq, mvPolynomial_comap_map_C] using
      (idealHeight_comap_le_of_hasGoingDown (R := R)
        (I.map (MvPolynomial.C (σ := ι))))

end AbelFormalization
