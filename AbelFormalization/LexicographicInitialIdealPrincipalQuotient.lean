import AbelFormalization.LexicographicInitialIdealLocalization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Basic

set_option autoImplicit false

/-!
# Lexicographic initial ideals and saturated principal quotients

For an arbitrary coefficient map, mapping an initial ideal into the initial
ideal of the image is formal.  The reverse inclusion can fail because lower
weight components of a lift may be killed by the coefficient map.

This file gives the exact condition that repairs the reverse inclusion.  Let
`N ≤ K`, assume that `K` is homogeneous for the lexicographic weight, and
assume

`K ∩ ker (MvPolynomial.map f) ≤ N`.

Then every killed lower component of a lift belongs to `N` and can be
subtracted.  This is the unbounded polynomial version of the finite-product
prefix-subtraction argument.

For the quotient `B → B/(b)`, the kernel condition follows from the
sandwich `C(b)K ≤ N ≤ K` when `K` is saturated by `C(b)`.
-/

noncomputable section

namespace AbelFormalization

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section LowerComponents

variable {R ι : Type*} [CommRing R] {h : ℕ}

/-- Every component strictly below the actual lexicographic minimum is
zero. -/
theorem weightedHomogeneousComponent_eq_zero_of_lt_lexicographicMinimum
    (weight : ι → Fin h → ℤ) (p : MvPolynomial ι R)
    {degree : Lex (Fin h → ℤ)}
    (hdegree : degree < lexicographicMinimumWeight weight p) :
    MvPolynomial.weightedHomogeneousComponent
        (fun i => toLex (weight i)) degree p = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · by_contra hcoeff
    have hle := lexicographicMinimumWeight_le weight p
      (MvPolynomial.mem_support_iff.mpr hcoeff)
    rw [hd] at hle
    exact (not_le_of_gt hdegree) hle
  · rfl

end LowerComponents

section SurjectiveBaseChange

variable {R S ι : Type*} [CommRing R] [CommRing S] {h : ℕ}

/-- Full lexicographic initial formation commutes with a surjective
coefficient map provided all kernel elements that lie in a homogeneous
upper ideal `K` already lie in the source ideal `N`.

The kernel condition is the precise algebraic content of the manuscript's
principal-quotient sandwich. -/
theorem lexicographicInitialIdeal_map_eq_of_surjective_of_homogeneous_kernel
    (f : R →+* S) (hf : Function.Surjective f)
    (weight : ι → Fin h → ℤ)
    (N K : Ideal (MvPolynomial ι R))
    (hNK : N ≤ K)
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i => toLex (weight i))))
    (hkernel : K ⊓ RingHom.ker (MvPolynomial.map f) ≤ N) :
    (lexicographicInitialIdeal weight N).map (MvPolynomial.map f) =
      lexicographicInitialIdeal weight
        (N.map (MvPolynomial.map f)) := by
  classical
  let phi : MvPolynomial ι R →+* MvPolynomial ι S :=
    MvPolynomial.map f
  have hphi : Function.Surjective phi :=
    MvPolynomial.map_surjective f hf
  apply le_antisymm
  · exact lexicographicInitialIdeal_map_le f weight N
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    by_cases hgzero : g = 0
    · rw [hgzero, lexicographicInitialForm_zero]
      exact Ideal.zero_mem _
    obtain ⟨p, hpN, hpmap⟩ :=
      (Ideal.mem_map_iff_of_surjective phi hphi).mp hg
    let omega : ι → Lex (Fin h → ℤ) := fun i => toLex (weight i)
    let alpha : Lex (Fin h → ℤ) :=
      lexicographicMinimumWeight weight g
    let lowerWeights : Finset (Lex (Fin h → ℤ)) :=
      (p.support.image (Finsupp.weight omega)).filter
        (fun degree => degree < alpha)
    let lower : MvPolynomial ι R :=
      ∑ degree ∈ lowerWeights,
        MvPolynomial.weightedHomogeneousComponent omega degree p
    let p' : MvPolynomial ι R := p - lower
    have hpK : p ∈ K := hNK hpN
    have hdegree_lt (degree : Lex (Fin h → ℤ))
        (hdegree : degree ∈ lowerWeights) : degree < alpha :=
      (Finset.mem_filter.mp hdegree).2
    have hcomponent_map_zero (degree : Lex (Fin h → ℤ))
        (hdegree : degree ∈ lowerWeights) :
        phi (MvPolynomial.weightedHomogeneousComponent
          omega degree p) = 0 := by
      calc
        phi (MvPolynomial.weightedHomogeneousComponent omega degree p) =
            MvPolynomial.weightedHomogeneousComponent
              omega degree (phi p) :=
          mvPolynomial_map_weightedHomogeneousComponent
            f omega degree p
        _ = MvPolynomial.weightedHomogeneousComponent
              omega degree g := by rw [hpmap]
        _ = 0 := by
          exact weightedHomogeneousComponent_eq_zero_of_lt_lexicographicMinimum
            weight g (hdegree_lt degree hdegree)
    have hcomponent_mem_N (degree : Lex (Fin h → ℤ))
        (hdegree : degree ∈ lowerWeights) :
        MvPolynomial.weightedHomogeneousComponent
            omega degree p ∈ N := by
      apply hkernel
      constructor
      · exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem
          R omega hK hpK degree
      · exact (RingHom.mem_ker).mpr
          (hcomponent_map_zero degree hdegree)
    have hlowerN : lower ∈ N := by
      dsimp only [lower]
      apply Ideal.sum_mem
      intro degree hdegree
      exact hcomponent_mem_N degree hdegree
    have hlower_map : phi lower = 0 := by
      dsimp only [lower]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro degree hdegree
      exact hcomponent_map_zero degree hdegree
    have hp'N : p' ∈ N := by
      exact N.sub_mem hpN hlowerN
    have hp'map : phi p' = g := by
      dsimp only [p']
      rw [map_sub, hpmap, hlower_map, sub_zero]
    have hlower_coeff (d : ι →₀ ℕ)
        (hdp : d ∈ p.support)
        (hdlt : Finsupp.weight omega d < alpha) :
        lower.coeff d = p.coeff d := by
      dsimp only [lower]
      simp only [MvPolynomial.coeff_sum,
        MvPolynomial.coeff_weightedHomogeneousComponent]
      rw [Finset.sum_eq_single (Finsupp.weight omega d)]
      · simp
      · intro degree hdegree hne
        simp [Ne.symm hne]
      · intro hnot
        exfalso
        apply hnot
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨d, hdp, rfl⟩, hdlt⟩
    have hp'bound : ∀ d ∈ p'.support,
        alpha ≤ Finsupp.weight omega d := by
      intro d hdp'
      by_contra hnot
      have hdlt : Finsupp.weight omega d < alpha := lt_of_not_ge hnot
      have hdp : d ∈ p.support := by
        apply MvPolynomial.mem_support_iff.mpr
        intro hpzero
        have hlowerzero : lower.coeff d = 0 := by
          dsimp only [lower]
          simp only [MvPolynomial.coeff_sum,
            MvPolynomial.coeff_weightedHomogeneousComponent,
            hpzero, ite_self, Finset.sum_const_zero]
        apply MvPolynomial.mem_support_iff.mp hdp'
        dsimp only [p']
        simp only [MvPolynomial.coeff_sub, hpzero, hlowerzero, sub_zero]
      have hp'zero : p'.coeff d = 0 := by
        dsimp only [p']
        rw [MvPolynomial.coeff_sub,
          hlower_coeff d hdp hdlt, sub_self]
      exact (MvPolynomial.mem_support_iff.mp hdp') hp'zero
    have hcomponent_map :
        phi (MvPolynomial.weightedHomogeneousComponent
          omega alpha p') = lexicographicInitialForm weight g := by
      calc
        phi (MvPolynomial.weightedHomogeneousComponent omega alpha p') =
            MvPolynomial.weightedHomogeneousComponent
              omega alpha (phi p') :=
          mvPolynomial_map_weightedHomogeneousComponent
            f omega alpha p'
        _ = MvPolynomial.weightedHomogeneousComponent omega alpha g := by
          rw [hp'map]
        _ = lexicographicInitialForm weight g := rfl
    have hcomponent_ne :
        MvPolynomial.weightedHomogeneousComponent omega alpha p' ≠ 0 := by
      intro hzero
      apply lexicographicInitialForm_ne_zero weight hgzero
      rw [← hcomponent_map, hzero, map_zero]
    have hp'minimum :
        lexicographicMinimumWeight weight p' = alpha :=
      lexicographicMinimumWeight_eq_of_component_ne_zero
        weight p' alpha hp'bound hcomponent_ne
    have hform_map :
        phi (lexicographicInitialForm weight p') =
          lexicographicInitialForm weight g := by
      simpa only [lexicographicInitialForm, hp'minimum]
        using hcomponent_map
    rw [← hform_map]
    exact Ideal.mem_map_of_mem phi
      (lexicographicInitialForm_mem_initialIdeal weight N hp'N)

end SurjectiveBaseChange

section PrincipalKernel

variable {R S ι : Type*} [CommRing R] [CommRing S] {h : ℕ}

/-- A contraction along a map which sends `c` to a unit is saturated by
`c`. -/
theorem ideal_comap_saturatedBy_of_isUnit_map
    (psi : R →+* S) (L : Ideal S) (c : R)
    (hc : IsUnit (psi c)) {x : R}
    (hx : c * x ∈ L.comap psi) : x ∈ L.comap psi := by
  change psi x ∈ L
  change psi (c * x) ∈ L at hx
  rw [map_mul] at hx
  exact (Ideal.unit_mul_mem_iff_mem L hc).mp hx

/-- A polynomial ideal contracted from a coefficient localization is
saturated by every constant whose coefficient lies in the localization
submonoid. -/
theorem mvPolynomial_localization_comap_saturatedBy_C
    {A : Type*} [CommRing A] (T : Submonoid A)
    (L : Ideal (MvPolynomial ι (Localization T))) (b : T)
    {p : MvPolynomial ι A}
    (hp : MvPolynomial.C (b : A) * p ∈
      L.comap (MvPolynomial.map (algebraMap A (Localization T)))) :
    p ∈ L.comap
      (MvPolynomial.map (algebraMap A (Localization T))) := by
  apply ideal_comap_saturatedBy_of_isUnit_map
    (MvPolynomial.map (algebraMap A (Localization T))) L
      (MvPolynomial.C (b : A))
  · have hb : IsUnit (algebraMap A (Localization T) (b : A)) :=
      IsLocalization.map_units (Localization T) b
    simpa only [MvPolynomial.map_C] using
      hb.map (MvPolynomial.C : Localization T →+*
        MvPolynomial ι (Localization T))
  · exact hp

/-- A principal coefficient kernel remains principal after applying the
multivariate-polynomial functor. -/
theorem ker_mvPolynomial_map_eq_span_C_of_ker_eq_span
    (f : R →+* S) (b : R)
    (hfker : RingHom.ker f = Ideal.span {b}) :
    RingHom.ker (MvPolynomial.map (σ := ι) f) =
      Ideal.span {MvPolynomial.C b} := by
  rw [MvPolynomial.ker_map, hfker, Ideal.map_span,
    Set.image_singleton]

/-- Saturation identifies the part of the polynomial-map kernel lying in
`K` with the ideal product `C(b)K`. -/
theorem inf_ker_mvPolynomial_map_eq_principal_mul_of_saturated
    (f : R →+* S) (b : R)
    (hfker : RingHom.ker f = Ideal.span {b})
    (K : Ideal (MvPolynomial ι R))
    (hKsat : ∀ p : MvPolynomial ι R,
      MvPolynomial.C b * p ∈ K → p ∈ K) :
    K ⊓ RingHom.ker (MvPolynomial.map f) =
      Ideal.span {MvPolynomial.C b} * K := by
  apply le_antisymm
  · intro p hp
    have hpCb : p ∈ Ideal.span {MvPolynomial.C b} := by
      rw [← ker_mvPolynomial_map_eq_span_C_of_ker_eq_span
        (ι := ι) f b hfker]
      exact hp.2
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hpCb
    have hCbq : MvPolynomial.C b * q = p := by
      simpa only [mul_comm] using hq
    have hqK : q ∈ K := by
      apply hKsat q
      rw [hCbq]
      exact hp.1
    exact (Ideal.mem_span_singleton_mul).mpr ⟨q, hqK, hCbq⟩
  · intro p hp
    obtain ⟨q, hqK, hCbq⟩ :=
      (Ideal.mem_span_singleton_mul).mp hp
    constructor
    · rw [← hCbq]
      exact K.mul_mem_left (MvPolynomial.C b) hqK
    · rw [ker_mvPolynomial_map_eq_span_C_of_ker_eq_span
        (ι := ι) f b hfker]
      exact Ideal.mem_span_singleton'.mpr
        ⟨q, by simpa only [mul_comm] using hCbq⟩

/-- If the coefficient kernel is `(b)`, saturation of `K` by `C b` and the
sandwich `C(b)K ≤ N ≤ K` imply the homogeneous-kernel hypothesis of the
general base-change theorem. -/
theorem lexicographicInitialIdeal_map_eq_of_principal_saturated_sandwich
    (f : R →+* S) (hf : Function.Surjective f)
    (b : R) (hfker : RingHom.ker f = Ideal.span {b})
    (weight : ι → Fin h → ℤ)
    (N K : Ideal (MvPolynomial ι R))
    (hNK : N ≤ K)
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i => toLex (weight i))))
    (hKsat : ∀ p : MvPolynomial ι R,
      MvPolynomial.C b * p ∈ K → p ∈ K)
    (hbKN : Ideal.span {MvPolynomial.C b} * K ≤ N) :
    (lexicographicInitialIdeal weight N).map (MvPolynomial.map f) =
      lexicographicInitialIdeal weight
        (N.map (MvPolynomial.map f)) := by
  apply lexicographicInitialIdeal_map_eq_of_surjective_of_homogeneous_kernel
    f hf weight N K hNK hK
  rw [inf_ker_mvPolynomial_map_eq_principal_mul_of_saturated
    (ι := ι) f b hfker K hKsat]
  exact hbKN

/-- Concrete coefficient quotient by the principal ideal `(b)`. -/
theorem lexicographicInitialIdeal_map_principalQuotient
    (b : R) (weight : ι → Fin h → ℤ)
    (N K : Ideal (MvPolynomial ι R))
    (hNK : N ≤ K)
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i => toLex (weight i))))
    (hKsat : ∀ p : MvPolynomial ι R,
      MvPolynomial.C b * p ∈ K → p ∈ K)
    (hbKN : Ideal.span {MvPolynomial.C b} * K ≤ N) :
    (lexicographicInitialIdeal weight N).map
        (MvPolynomial.map
          (Ideal.Quotient.mk (Ideal.span {b}))) =
      lexicographicInitialIdeal weight
        (N.map (MvPolynomial.map
          (Ideal.Quotient.mk (Ideal.span {b})))) := by
  exact lexicographicInitialIdeal_map_eq_of_principal_saturated_sandwich
    (Ideal.Quotient.mk (Ideal.span {b}))
    Ideal.Quotient.mk_surjective b Ideal.mk_ker weight N K
    hNK hK hKsat hbKN

end PrincipalKernel

end AbelFormalization
