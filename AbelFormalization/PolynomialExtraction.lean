import AbelFormalization.IdealHeight
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Monic

/-! # Polynomial extraction at maximum height

Polynomial ideals of maximum height over a finite-dimensional augmented
Noetherian local coefficient ring contain monic scalar polynomials in each
chosen variable. The proof derives maximality and coefficient contraction
from height, then combines the finitely many minimal-prime relations.
-/

noncomputable section

namespace AbelFormalization

open scoped Polynomial

section FieldPolynomial

variable {k : Type*} [Field k] {m : ℕ}

/-- A maximal ideal in a polynomial algebra over a field contains a monic
univariate polynomial in every chosen coordinate. -/
theorem maximal_mvPolynomial_contains_monic_univariate
    (P : Ideal (MvPolynomial (Fin m) k)) [P.IsMaximal] (i : Fin m) :
    ∃ f : k[X], f.Monic ∧ f.toMvPolynomial i ∈ P := by
  have hint := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing P
  obtain ⟨f, hmonic, hroot⟩ := hint (Ideal.Quotient.mk P (MvPolynomial.X i))
  refine ⟨f, hmonic, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ k P) (Polynomial.aeval (MvPolynomial.X i) f) = 0
  rw [← Polynomial.aeval_algHom_apply]
  exact hroot

end FieldPolynomial

section CoefficientEmbedding

variable (k B : Type*) [Field k] [CommRing B] [Algebra k B] {m : ℕ}

/-- The literal copy of `k[X]` in the selected coordinate of `B[t]`. -/
def scalarUnivariateEmbedding (i : Fin m) : k[X] →+* MvPolynomial (Fin m) B :=
  (MvPolynomial.map (algebraMap k B)).comp
    (Polynomial.toMvPolynomial i).toRingHom

variable {k B}

theorem augmentation_surjective (ε : B →ₐ[k] k) : Function.Surjective ε := by
  intro c
  refine ⟨algebraMap k B c, ?_⟩
  simp

/-- Coefficient specialization retracts the embedded scalar polynomial. -/
theorem map_scalarUnivariateEmbedding (ε : B →ₐ[k] k) (i : Fin m) (f : k[X]) :
    MvPolynomial.map ε.toRingHom (scalarUnivariateEmbedding k B i f) =
      f.toMvPolynomial i := by
  have he : ε.toRingHom.comp (algebraMap k B) = RingHom.id k := by
    apply RingHom.ext
    intro c
    simp
  rw [scalarUnivariateEmbedding, RingHom.comp_apply, MvPolynomial.map_map,
    he, MvPolynomial.map_id]
  rfl

theorem scalarUnivariateEmbedding_injective (ε : B →ₐ[k] k) (i : Fin m) :
    Function.Injective (scalarUnivariateEmbedding k B i) := by
  intro f g h
  apply Polynomial.toMvPolynomial_injective i
  have he := congrArg (MvPolynomial.map ε.toRingHom) h
  simpa only [map_scalarUnivariateEmbedding] using he

end CoefficientEmbedding

section LocalHeight

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [IsNoetherianRing B] [IsLocalRing B]

omit [IsNoetherianRing B] in
/-- An actual field augmentation identifies the unique maximal ideal. -/
theorem augmentation_ker_eq_maximalIdeal (ε : B →ₐ[k] k) :
    RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal B :=
  IsLocalRing.ker_eq_maximalIdeal ε.toRingHom (augmentation_surjective ε)

/-- At the largest possible height, both the polynomial prime and its
coefficient contraction are maximal. -/
theorem mvPolynomial_prime_maximal_and_contraction_of_height
    (p m : ℕ) (hdim : ringKrullDim B = p)
    (P : Ideal (MvPolynomial (Fin m) B)) [P.IsPrime]
    (hP : (p + m : ℕ∞) ≤ P.height) :
    P.IsMaximal ∧ P.comap MvPolynomial.C = IsLocalRing.maximalIdeal B := by
  have hdimS : ringKrullDim (MvPolynomial (Fin m) B) = (p + m : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, hdim]
    simp
  have hnat (n : ℕ) : (n : WithBot ℕ∞) ≠ ⊥ ∧ (n : WithBot ℕ∞) ≠ ⊤ := by
    refine ⟨by simp, ?_⟩
    change ((n : ℕ∞) : WithBot ℕ∞) ≠ ⊤
    exact fun h => ENat.natCast_ne_top n (WithBot.coe_eq_top.mp h)
  let : FiniteRingKrullDim B :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (hdim ▸ hnat p)
  let : FiniteRingKrullDim (MvPolynomial (Fin m) B) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (hdimS ▸ hnat (p + m))
  have hheight : (P.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin m) B) := by
    apply le_antisymm Ideal.height_le_ringKrullDim_of_isPrime
    rw [hdimS]
    exact_mod_cast hP
  refine ⟨Ideal.isMaximal_of_height_eq_ringKrullDim hheight, ?_⟩
  have hcontract := mvPolynomial_prime_height_le_comap_add_card P
  have hlow : (p : ℕ∞) ≤ (P.comap MvPolynomial.C).height := by
    apply (ENat.add_le_add_iff_right (by simp : (m : ℕ∞) ≠ ⊤)).mp
    exact hP.trans (by simpa using hcontract)
  have hcheight : ((P.comap MvPolynomial.C).height : WithBot ℕ∞) = ringKrullDim B := by
    apply le_antisymm Ideal.height_le_ringKrullDim_of_isPrime
    rw [hdim]
    exact_mod_cast hlow
  exact Ideal.height_eq_ringKrullDim_iff.mp hcheight

/-- The prime-level extraction statement over an augmented local coefficient
ring. Every maximality and kernel-containment fact is derived from the height. -/
theorem mvPolynomial_prime_contains_monic_univariate_of_height
    (ε : B →ₐ[k] k) (p m : ℕ) (hdim : ringKrullDim B = p)
    (P : Ideal (MvPolynomial (Fin m) B)) [P.IsPrime]
    (hP : (p + m : ℕ∞) ≤ P.height) (i : Fin m) :
    ∃ f : k[X], f.Monic ∧ scalarUnivariateEmbedding k B i f ∈ P := by
  obtain ⟨hPmax, hcontract⟩ :=
    mvPolynomial_prime_maximal_and_contraction_of_height p m hdim P hP
  let : P.IsMaximal := hPmax
  let ν : MvPolynomial (Fin m) B →+* MvPolynomial (Fin m) k :=
    MvPolynomial.map ε.toRingHom
  have hν : Function.Surjective ν :=
    MvPolynomial.map_surjective ε.toRingHom (augmentation_surjective ε)
  have hker : RingHom.ker ν ≤ P := by
    dsimp only [ν]
    rw [MvPolynomial.ker_map, augmentation_ker_eq_maximalIdeal ε, ← hcontract]
    exact Ideal.map_le_iff_le_comap.mpr le_rfl
  let P₀ : Ideal (MvPolynomial (Fin m) k) := P.map ν
  let : P₀.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hν hker
  obtain ⟨f, hmonic, hf⟩ := maximal_mvPolynomial_contains_monic_univariate P₀ i
  refine ⟨f, hmonic, ?_⟩
  have hcomap : P₀.comap ν = P := by
    dsimp only [P₀]
    rw [Ideal.comap_map_of_surjective ν hν,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  rw [← hcomap]
  change ν (scalarUnivariateEmbedding k B i f) ∈ P₀
  rw [map_scalarUnivariateEmbedding]
  exact hf

end LocalHeight

section FiniteMinimalPrimes

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [IsNoetherianRing B] {m : ℕ}

/-- Monic coordinate relations in every minimal prime combine into a monic
coordinate relation in the ideal itself. This includes the empty-prime-family
case of the unit ideal. -/
theorem mvPolynomial_contains_monic_univariate_of_minimalPrimes
    (I : Ideal (MvPolynomial (Fin m) B)) (i : Fin m)
    (h : ∀ P ∈ I.minimalPrimes,
      ∃ f : k[X], f.Monic ∧ scalarUnivariateEmbedding k B i f ∈ P) :
    ∃ f : k[X], f.Monic ∧ scalarUnivariateEmbedding k B i f ∈ I := by
  classical
  let : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) B)).fintype
  choose f hmonic hmem using fun P : I.minimalPrimes => h P.val P.property
  let g : k[X] := ∏ P : I.minimalPrimes, f P
  have hg : g.Monic := Polynomial.monic_prod_of_monic Finset.univ f (fun P _ => hmonic P)
  have hrad : scalarUnivariateEmbedding k B i g ∈ I.radical := by
    rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    dsimp only [g]
    rw [map_prod]
    exact Ideal.prod_mem P (Finset.mem_univ (⟨P, hP⟩ : I.minimalPrimes))
      (hmem ⟨P, hP⟩)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨g ^ n, hg.pow n, ?_⟩
  simpa only [map_pow] using hn

end FiniteMinimalPrimes

section Extraction

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [IsNoetherianRing B] [IsLocalRing B]

/-- Maximum-height polynomial ideals over a finite-dimensional augmented
Noetherian local coefficient ring contain monic scalar polynomials in every
chosen coordinate. This implies Lemma `lem:height`(3) over the real germ ring. -/
theorem mvPolynomial_contains_monic_univariate_of_height
    (ε : B →ₐ[k] k) (p m : ℕ) (hdim : ringKrullDim B = p)
    (I : Ideal (MvPolynomial (Fin m) B))
    (hI : (p + m : ℕ∞) ≤ I.height) (i : Fin m) :
    ∃ f : k[X], f.Monic ∧ scalarUnivariateEmbedding k B i f ∈ I := by
  apply mvPolynomial_contains_monic_univariate_of_minimalPrimes I i
  intro P hP
  let : P.IsPrime := hP.isPrime
  exact mvPolynomial_prime_contains_monic_univariate_of_height ε p m hdim P
    (hI.trans (Ideal.height_mono hP.le)) i

/-- The nonvanishing formulation requested in the manuscript. -/
theorem mvPolynomial_contains_nonzero_univariate_of_height
    (ε : B →ₐ[k] k) (p m : ℕ) (hdim : ringKrullDim B = p)
    (I : Ideal (MvPolynomial (Fin m) B))
    (hI : (p + m : ℕ∞) ≤ I.height) (i : Fin m) :
    ∃ f : k[X], f ≠ 0 ∧ scalarUnivariateEmbedding k B i f ≠ 0 ∧
      scalarUnivariateEmbedding k B i f ∈ I := by
  obtain ⟨f, hf, hmem⟩ :=
    mvPolynomial_contains_monic_univariate_of_height ε p m hdim I hI i
  refine ⟨f, hf.ne_zero, ?_, hmem⟩
  intro hz
  apply hf.ne_zero
  exact scalarUnivariateEmbedding_injective ε i (hz.trans (map_zero _).symm)

end Extraction

end AbelFormalization
