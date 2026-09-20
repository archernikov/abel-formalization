import AbelFormalization.TerminalReindexedLocalizationContraction
import Mathlib.RingTheory.Polynomial.Basic

set_option autoImplicit false

/-!
# Principal saturation and injectivity after quotienting

If an ideal `K` is saturated with respect to an element `s`, then the part of
the principal ideal `(s)` lying in `K` is exactly `(s)K`.  It follows that a
surjective quotient map with kernel `(s)` is injective on the interval of
ideals between `(s)K` and `K`.

The final declarations specialize this observation to the contraction of an
ideal from a localization and then to coefficient localization and reduction
for multivariate polynomial rings.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

universe u v

/- `MvPolynomial.isLocalization` uses this canonical polynomial algebra
structure. -/
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The abstract saturated interval -/

/-- Saturation by `s` identifies the intersection of `K` with `(s)` as the
product `(s)K`. -/
theorem inf_span_singleton_eq_span_singleton_mul_of_saturated
    {A : Type u} [CommRing A]
    (s : A) (K : Ideal A)
    (hsaturated : ∀ x : A, s * x ∈ K → x ∈ K) :
    K ⊓ Ideal.span {s} = Ideal.span {s} * K := by
  apply le_antisymm
  · rintro x ⟨hxK, hxspan⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxspan
    have hsax : s * a = x := by
      simpa only [mul_comm] using ha
    have haK : a ∈ K := hsaturated a (by
      rw [hsax]
      exact hxK)
    exact Ideal.mem_span_singleton_mul.mpr ⟨a, haK, hsax⟩
  · exact le_inf Ideal.mul_le_right Ideal.mul_le_left

/-- The preceding intersection identity with the principal ideal presented as
the kernel of a ring homomorphism. -/
theorem inf_ker_eq_span_singleton_mul_of_saturated
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    (q : A →+* T) (s : A) (K : Ideal A)
    (hker : RingHom.ker q = Ideal.span {s})
    (hsaturated : ∀ x : A, s * x ∈ K → x ∈ K) :
    K ⊓ RingHom.ker q = Ideal.span {s} * K := by
  rw [hker]
  exact inf_span_singleton_eq_span_singleton_mul_of_saturated
    s K hsaturated

/-- A surjective map with principal kernel is injective on the interval
`[(s)K, K]` when `K` is saturated by `s`. -/
theorem eq_of_map_eq_of_span_singleton_mul_le_of_le_of_saturated
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    (q : A →+* T) (hq : Function.Surjective q)
    (s : A) (K N₁ N₂ : Ideal A)
    (hker : RingHom.ker q = Ideal.span {s})
    (hsaturated : ∀ x : A, s * x ∈ K → x ∈ K)
    (h₁lower : Ideal.span {s} * K ≤ N₁) (h₁upper : N₁ ≤ K)
    (h₂lower : Ideal.span {s} * K ≤ N₂) (h₂upper : N₂ ≤ K)
    (hmap : N₁.map q = N₂.map q) :
    N₁ = N₂ := by
  have hintersection : K ⊓ RingHom.ker q = Ideal.span {s} * K :=
    inf_ker_eq_span_singleton_mul_of_saturated
      q s K hker hsaturated
  have hle (P Q : Ideal A)
      (hPlower : Ideal.span {s} * K ≤ P) (hPupper : P ≤ K)
      (hQlower : Ideal.span {s} * K ≤ Q) (hQupper : Q ≤ K)
      (hPQ : P.map q = Q.map q) : P ≤ Q := by
    intro x hxP
    have hqx : q x ∈ Q.map q := by
      rw [← hPQ]
      exact Ideal.mem_map_of_mem q hxP
    obtain ⟨y, hyQ, hyq⟩ :=
      (Ideal.mem_map_iff_of_surjective q hq).mp hqx
    have hxyker : x - y ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_sub, hyq, sub_self]
    have hxyK : x - y ∈ K :=
      K.sub_mem (hPupper hxP) (hQupper hyQ)
    have hxyQ : x - y ∈ Q := by
      apply hQlower
      rw [← hintersection]
      exact ⟨hxyK, hxyker⟩
    have hadd := Q.add_mem hxyQ hyQ
    rwa [sub_add_cancel] at hadd
  exact le_antisymm
    (hle N₁ N₂ h₁lower h₁upper h₂lower h₂upper hmap)
    (hle N₂ N₁ h₂lower h₂upper h₁lower h₁upper hmap.symm)

/-! ## Saturation of a localization contraction -/

/-- Multiplication by an element of the localizing submonoid does not change
membership in a contracted ideal. -/
theorem mul_mem_idealLocalizationContraction_iff
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [Algebra A T]
    (M : Submonoid A) [IsLocalization M T]
    (L : Ideal T) (s : M) (x : A) :
    (s : A) * x ∈ L.comap (algebraMap A T) ↔
      x ∈ L.comap (algebraMap A T) := by
  change algebraMap A T ((s : A) * x) ∈ L ↔
    algebraMap A T x ∈ L
  rw [map_mul]
  exact Ideal.unit_mul_mem_iff_mem L (IsLocalization.map_units T s)

/-- A localization contraction is saturated by every element of the
localizing submonoid. -/
theorem idealLocalizationContraction_saturated
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [Algebra A T]
    (M : Submonoid A) [IsLocalization M T]
    (L : Ideal T) (s : M) :
    ∀ x : A, (s : A) * x ∈ L.comap (algebraMap A T) →
      x ∈ L.comap (algebraMap A T) := by
  intro x hx
  exact (mul_mem_idealLocalizationContraction_iff M L s x).mp hx

/-! ## Coefficient localization and principal coefficient quotient -/

/-- Coefficientwise reduction modulo `(b)`. -/
def mvPolynomialPrincipalCoefficientQuotientMap
    {B : Type u} [CommRing B] (σ : Type v) (b : B) :
    MvPolynomial σ B →+*
      MvPolynomial σ (B ⧸ Ideal.span {b}) :=
  MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {b}))

/-- Coefficientwise reduction modulo `(b)` is surjective. -/
theorem mvPolynomialPrincipalCoefficientQuotientMap_surjective
    {B : Type u} [CommRing B] (σ : Type v) (b : B) :
    Function.Surjective
      (mvPolynomialPrincipalCoefficientQuotientMap σ b) := by
  simpa only [mvPolynomialPrincipalCoefficientQuotientMap] using
    (MvPolynomial.map_surjective (σ := σ)
      (Ideal.Quotient.mk (Ideal.span {b}))
      Ideal.Quotient.mk_surjective)

/-- The kernel of coefficientwise reduction modulo `(b)` is the polynomial
ideal generated by the constant polynomial `C b`. -/
theorem mvPolynomialPrincipalCoefficientQuotientMap_ker
    {B : Type u} [CommRing B] (σ : Type v) (b : B) :
    RingHom.ker (mvPolynomialPrincipalCoefficientQuotientMap σ b) =
      Ideal.span {MvPolynomial.C b} := by
  rw [mvPolynomialPrincipalCoefficientQuotientMap,
    MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span,
    Set.image_singleton]

/-- A polynomial ideal contracted from a coefficient localization is
saturated by each constant denominator `C b`. -/
theorem mvPolynomial_C_mul_mem_localizationContraction_iff
    {B : Type u} [CommRing B] {σ : Type v}
    (S : Submonoid B)
    (L : Ideal (MvPolynomial σ (Localization S)))
    (b : S) (P : MvPolynomial σ B) :
    MvPolynomial.C (b : B) * P ∈
        L.comap (MvPolynomial.map (algebraMap B (Localization S))) ↔
      P ∈ L.comap
        (MvPolynomial.map (algebraMap B (Localization S))) := by
  let A := MvPolynomial σ B
  let T := MvPolynomial σ (Localization S)
  let polynomialS : Submonoid A :=
    S.map (MvPolynomial.C : B →+* A)
  let cb : polynomialS :=
    ⟨MvPolynomial.C (b : B),
      Submonoid.mem_map_of_mem
        (MvPolynomial.C : B →+* A) b.property⟩
  simpa only [A, T, cb, MvPolynomial.algebraMap_def] using
    (mul_mem_idealLocalizationContraction_iff
      polynomialS L cb P)

/-- Coefficientwise reduction modulo `(b)` is injective on the interval
between `(C b)K` and a localization contraction `K`.  This is the ideal-level
quotient step needed after denominator clearing. -/
theorem eq_of_map_mvPolynomialPrincipalCoefficientQuotientMap_eq_of_sandwich
    {B : Type u} [CommRing B] {σ : Type v}
    (S : Submonoid B)
    (L : Ideal (MvPolynomial σ (Localization S)))
    (b : S) (N₁ N₂ : Ideal (MvPolynomial σ B))
    (h₁lower :
      Ideal.span {MvPolynomial.C (b : B)} *
          L.comap (MvPolynomial.map (algebraMap B (Localization S))) ≤ N₁)
    (h₁upper : N₁ ≤
      L.comap (MvPolynomial.map (algebraMap B (Localization S))))
    (h₂lower :
      Ideal.span {MvPolynomial.C (b : B)} *
          L.comap (MvPolynomial.map (algebraMap B (Localization S))) ≤ N₂)
    (h₂upper : N₂ ≤
      L.comap (MvPolynomial.map (algebraMap B (Localization S))))
    (hmap : N₁.map
        (mvPolynomialPrincipalCoefficientQuotientMap σ (b : B)) =
      N₂.map (mvPolynomialPrincipalCoefficientQuotientMap σ (b : B))) :
    N₁ = N₂ := by
  let K : Ideal (MvPolynomial σ B) :=
    L.comap (MvPolynomial.map (algebraMap B (Localization S)))
  apply eq_of_map_eq_of_span_singleton_mul_le_of_le_of_saturated
    (mvPolynomialPrincipalCoefficientQuotientMap σ (b : B))
    (mvPolynomialPrincipalCoefficientQuotientMap_surjective σ (b : B))
    (MvPolynomial.C (b : B)) K N₁ N₂
    (mvPolynomialPrincipalCoefficientQuotientMap_ker σ (b : B))
  · intro P hP
    exact (mvPolynomial_C_mul_mem_localizationContraction_iff
      S L b P).mp (by simpa only [K] using hP)
  · simpa only [K] using h₁lower
  · simpa only [K] using h₁upper
  · simpa only [K] using h₂lower
  · simpa only [K] using h₂upper
  · exact hmap

end AbelFormalization
