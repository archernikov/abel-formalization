import AbelFormalization.LexicographicInitialIdealLocalization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false

/-!
# Lexicographic initial ideals commute with coefficient localization

The forward inclusion is valid for every coefficient homomorphism and is
proved in `LexicographicInitialIdealLocalization`.  For the reverse
inclusion, write a polynomial in the extended ideal with one constant
denominator and numerator `p ∈ I`.  Every coefficient of `p` below the
least surviving weight maps to zero.  Since there are only finitely many of
them, one element of the localization submonoid annihilates all of them.
After multiplying `p` by this common annihilator, its actual initial form
maps to a unit times the desired localized initial form.
-/

noncomputable section

namespace AbelFormalization

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## Two denominator-clearing lemmas -/

/-- Finitely many elements, each annihilated by some member of a commutative
submonoid, have a common annihilator in that submonoid. -/
theorem exists_submonoid_common_annihilator
    {R κ : Type*} [CommRing R]
    (S : Submonoid R) (indices : Finset κ) (a : κ → R)
    (h : ∀ i ∈ indices, ∃ s : S, (s : R) * a i = 0) :
    ∃ s : S, ∀ i ∈ indices, (s : R) * a i = 0 := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      exact ⟨1, by simp⟩
  | @insert i indices hi ih =>
      obtain ⟨si, hsi⟩ := h i (Finset.mem_insert_self i indices)
      obtain ⟨st, hst⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
      refine ⟨si * st, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · change ((si : R) * (st : R)) * a j = 0
        calc
          ((si : R) * (st : R)) * a j =
              (st : R) * ((si : R) * a j) := by ac_rfl
          _ = (st : R) * ((si : R) * a i) := by rw [hji]
          _ = 0 := by rw [hsi, mul_zero]
      · change ((si : R) * (st : R)) * a j = 0
        rw [mul_assoc, hst j hj, mul_zero]

/-- Membership in the extension of an ideal to a coefficient localization
can be expressed with a numerator in the source ideal and one constant
denominator. -/
theorem exists_mul_C_eq_map_of_mem_localizedIdeal
    {R ι : Type*} [CommRing R]
    (S : Submonoid R) (I : Ideal (MvPolynomial ι R))
    {g : MvPolynomial ι (Localization S)}
    (hg : g ∈ I.map
      (MvPolynomial.map (algebraMap R (Localization S)))) :
    ∃ p ∈ I, ∃ s : S,
      g * MvPolynomial.C (algebraMap R (Localization S) (s : R)) =
        MvPolynomial.map (algebraMap R (Localization S)) p := by
  have hg' : g ∈ I.map
      (algebraMap (MvPolynomial ι R)
        (MvPolynomial ι (Localization S))) := by
    simpa only [MvPolynomial.algebraMap_def] using hg
  obtain ⟨⟨⟨p, hp⟩, denominator⟩, hdenominator⟩ :=
    (IsLocalization.mem_map_algebraMap_iff
      (S.map (MvPolynomial.C : R →+* MvPolynomial ι R))
      (MvPolynomial ι (Localization S))).mp hg'
  obtain ⟨s, hs, hsdenominator⟩ := denominator.property
  refine ⟨p, hp, ⟨s, hs⟩, ?_⟩
  rw [← hsdenominator] at hdenominator
  simpa only [MvPolynomial.algebraMap_def,
    MvPolynomial.map_C] using hdenominator

/-! ## Clearing the killed lower components -/

/-- The initial form of every element of a localized ideal belongs to the
localization of the source initial ideal. -/
theorem lexicographicInitialForm_mem_map_initialIdeal_localization
    {R ι : Type*} [CommRing R]
    (S : Submonoid R) {h : ℕ} (weight : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial ι R))
    {g : MvPolynomial ι (Localization S)}
    (hg : g ∈ I.map
      (MvPolynomial.map (algebraMap R (Localization S)))) :
    lexicographicInitialForm weight g ∈
      (lexicographicInitialIdeal weight I).map
        (MvPolynomial.map (algebraMap R (Localization S))) := by
  classical
  let f : R →+* Localization S := algebraMap R (Localization S)
  let Φ : MvPolynomial ι R →+* MvPolynomial ι (Localization S) :=
    MvPolynomial.map f
  by_cases hgzero : g = 0
  · rw [hgzero, lexicographicInitialForm_zero]
    exact Ideal.zero_mem _
  obtain ⟨p, hp, s, hps⟩ :=
    exists_mul_C_eq_map_of_mem_localizedIdeal S I hg
  let α := lexicographicMinimumWeight weight g
  let lower : Finset (ι →₀ ℕ) :=
    p.support.filter (fun d ↦
      Finsupp.weight (fun i ↦ toLex (weight i)) d < α)
  have hlower_map_zero : ∀ d ∈ lower, f (p.coeff d) = 0 := by
    intro d hd
    have hdweight :
        Finsupp.weight (fun i ↦ toLex (weight i)) d < α :=
      (Finset.mem_filter.mp hd).2
    have hgcoeff : g.coeff d = 0 := by
      by_contra hgd
      have hle := lexicographicMinimumWeight_le weight g
        (MvPolynomial.mem_support_iff.mpr hgd)
      exact (not_le_of_gt hdweight) hle
    have hcoeff := congrArg
      (fun q : MvPolynomial ι (Localization S) ↦ q.coeff d) hps
    simpa only [f, MvPolynomial.coeff_map,
      mul_comm g (MvPolynomial.C (algebraMap R (Localization S) (s : R))),
      MvPolynomial.coeff_C_mul, hgcoeff, mul_zero] using hcoeff.symm
  obtain ⟨t, ht⟩ : ∃ t : S, ∀ d ∈ lower,
      (t : R) * p.coeff d = 0 := by
    apply exists_submonoid_common_annihilator S lower p.coeff
    intro d hd
    exact (IsLocalization.map_eq_zero_iff S (Localization S)
      (p.coeff d)).mp (hlower_map_zero d hd)
  let q : MvPolynomial ι R := MvPolynomial.C (t : R) * p
  have hqI : q ∈ I := I.mul_mem_left (MvPolynomial.C (t : R)) hp
  have hqbound : ∀ d ∈ q.support,
      α ≤ Finsupp.weight (fun i ↦ toLex (weight i)) d := by
    intro d hdq
    by_contra hnot
    have hdlt : Finsupp.weight (fun i ↦ toLex (weight i)) d < α :=
      lt_of_not_ge hnot
    have hpd : d ∈ p.support := by
      apply MvPolynomial.mem_support_iff.mpr
      intro hpzero
      apply MvPolynomial.mem_support_iff.mp hdq
      simp only [q, MvPolynomial.coeff_C_mul, hpzero, mul_zero]
    have hdlower : d ∈ lower :=
      Finset.mem_filter.mpr ⟨hpd, hdlt⟩
    apply MvPolynomial.mem_support_iff.mp hdq
    simpa only [q, MvPolynomial.coeff_C_mul] using ht d hdlower
  have hmapq : Φ q =
      MvPolynomial.C (f ((t * s : S) : R)) * g := by
    change MvPolynomial.map f (MvPolynomial.C (t : R) * p) = _
    rw [map_mul, MvPolynomial.map_C]
    change MvPolynomial.C (f (t : R)) *
        MvPolynomial.map (algebraMap R (Localization S)) p = _
    rw [← hps]
    simp only [f, map_mul, Submonoid.coe_mul, MvPolynomial.C_mul]
    ac_rfl
  have hcomponent_map :
      Φ (MvPolynomial.weightedHomogeneousComponent
        (fun i ↦ toLex (weight i)) α q) =
        MvPolynomial.C (f ((t * s : S) : R)) *
          lexicographicInitialForm weight g := by
    calc
      Φ (MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (weight i)) α q) =
          MvPolynomial.weightedHomogeneousComponent
            (fun i ↦ toLex (weight i)) α (Φ q) :=
        mvPolynomial_map_weightedHomogeneousComponent f
          (fun i ↦ toLex (weight i)) α q
      _ = MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (weight i)) α
          (MvPolynomial.C (f ((t * s : S) : R)) * g) := by rw [hmapq]
      _ = MvPolynomial.C (f ((t * s : S) : R)) *
          MvPolynomial.weightedHomogeneousComponent
            (fun i ↦ toLex (weight i)) α g :=
        MvPolynomial.weightedHomogeneousComponent_C_mul
          (w := fun i ↦ toLex (weight i)) g α
          (f ((t * s : S) : R))
      _ = MvPolynomial.C (f ((t * s : S) : R)) *
          lexicographicInitialForm weight g := by rfl
  have hunitCoefficient : IsUnit (f ((t * s : S) : R)) := by
    exact IsLocalization.map_units (Localization S) (t * s)
  have hunitPolynomial :
      IsUnit (MvPolynomial.C (f ((t * s : S) : R))) :=
    hunitCoefficient.map
      (MvPolynomial.C : Localization S →+*
        MvPolynomial ι (Localization S))
  have hcomponent_ne :
      MvPolynomial.weightedHomogeneousComponent
        (fun i ↦ toLex (weight i)) α q ≠ 0 := by
    intro hzero
    have hproduct_zero :
        MvPolynomial.C (f ((t * s : S) : R)) *
          lexicographicInitialForm weight g = 0 := by
      rw [← hcomponent_map, hzero, map_zero]
    apply lexicographicInitialForm_ne_zero weight hgzero
    exact hunitPolynomial.mul_left_cancel (by
      simpa only [mul_zero] using hproduct_zero)
  have hqminimum : lexicographicMinimumWeight weight q = α :=
    lexicographicMinimumWeight_eq_of_component_ne_zero
      weight q α hqbound hcomponent_ne
  have hinitial_map :
      Φ (lexicographicInitialForm weight q) =
        MvPolynomial.C (f ((t * s : S) : R)) *
          lexicographicInitialForm weight g := by
    simpa only [lexicographicInitialForm, hqminimum] using hcomponent_map
  have hunit_multiple_mem :
      MvPolynomial.C (f ((t * s : S) : R)) *
          lexicographicInitialForm weight g ∈
        (lexicographicInitialIdeal weight I).map Φ := by
    rw [← hinitial_map]
    exact Ideal.mem_map_of_mem Φ
      (lexicographicInitialForm_mem_initialIdeal weight I hqI)
  exact (Ideal.unit_mul_mem_iff_mem _ hunitPolynomial).mp hunit_multiple_mem

/-! ## Equality after localization -/

/-- Full lexicographic initial formation commutes with localization of the
coefficient ring. -/
theorem lexicographicInitialIdeal_map_localization
    {R ι : Type*} [CommRing R]
    (S : Submonoid R) {h : ℕ} (weight : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial ι R)) :
    (lexicographicInitialIdeal weight I).map
        (MvPolynomial.map (algebraMap R (Localization S))) =
      lexicographicInitialIdeal weight
        (I.map (MvPolynomial.map (algebraMap R (Localization S)))) := by
  apply le_antisymm
  · exact lexicographicInitialIdeal_map_le
      (algebraMap R (Localization S)) weight I
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    exact lexicographicInitialForm_mem_map_initialIdeal_localization
      S weight I hg

end AbelFormalization
