import AbelFormalization.MonomialUpperSetBoxes
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Set.Card

/-!
# Actual monomial submodules and finite degree-count fibers

An upper set gives the ideal generated
by its coefficient-one monomials. A finite family gives a genuine submodule
of a finite free polynomial module by taking these ideals componentwise.
Containment is exactly componentwise containment of exponent upper sets.

The combinatorial degree counts below count selected module monomials.
Their identification with dimensions of arbitrary leading-monomial modules
is a separate subsequent theorem; it is not assumed here.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {n : ℕ} {κ R : Type*} [CommSemiring R]

/-- The actual monomial ideal attached to a coordinatewise exponent upper set. -/
def monomialUpperSetIdeal (U : UpperSet (Fin n → ℕ)) : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span ((fun d : Fin n →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
    {d | (d : Fin n → ℕ) ∈ U})

/-- Mathlib's actual monomial-ideal membership theorem simplifies to
membership of every supported exponent in the given upper set. -/
theorem mem_monomialUpperSetIdeal (U : UpperSet (Fin n → ℕ))
    (P : MvPolynomial (Fin n) R) :
    P ∈ monomialUpperSetIdeal U ↔ ∀ d ∈ P.support, (d : Fin n → ℕ) ∈ U := by
  rw [monomialUpperSetIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h d hd
    obtain ⟨e, he, hed⟩ := h d hd
    exact U.upper hed he
  · intro h d hd
    exact ⟨d, h d hd, le_rfl⟩

/-- Each coefficient-one monomial tests exactly one exponent in the upper set. -/
theorem monomial_one_mem_monomialUpperSetIdeal [Nontrivial R]
    (U : UpperSet (Fin n → ℕ)) (d : Fin n →₀ ℕ) :
    MvPolynomial.monomial d (1 : R) ∈ monomialUpperSetIdeal U ↔
      (d : Fin n → ℕ) ∈ U := by
  classical
  rw [mem_monomialUpperSetIdeal]
  simp [MvPolynomial.support_monomial]

/-- Ideal containment is literal exponent-set containment. The nontrivial
coefficient semiring prevents coefficient-one monomials from vanishing. -/
theorem monomialUpperSetIdeal_le_iff [Nontrivial R]
    (U V : UpperSet (Fin n → ℕ)) :
    monomialUpperSetIdeal (R := R) U ≤ monomialUpperSetIdeal V ↔
      (U : Set (Fin n → ℕ)) ⊆ V := by
  constructor
  · intro h x hx
    let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm x
    have hd : (d : Fin n → ℕ) = x := rfl
    have hmon : MvPolynomial.monomial d (1 : R) ∈ monomialUpperSetIdeal U :=
      (monomial_one_mem_monomialUpperSetIdeal U d).mpr (hd.symm ▸ hx)
    have hV := (monomial_one_mem_monomialUpperSetIdeal V d).mp (h hmon)
    rwa [hd] at hV
  · intro h P hP
    apply (mem_monomialUpperSetIdeal V P).mpr
    intro d hd
    exact h ((mem_monomialUpperSetIdeal U P).mp hP d hd)

/-- Componentwise monomial ideals form an actual submodule over the
polynomial ring; for finite κ its ambient module is finite free. -/
def monomialUpperFamilySubmodule (U : κ → UpperSet (Fin n → ℕ)) :
    Submodule (MvPolynomial (Fin n) R) (κ → MvPolynomial (Fin n) R) :=
  Submodule.pi Set.univ (fun k => monomialUpperSetIdeal (R := R) (U k))

theorem mem_monomialUpperFamilySubmodule (U : κ → UpperSet (Fin n → ℕ))
    (P : κ → MvPolynomial (Fin n) R) :
    P ∈ monomialUpperFamilySubmodule U ↔
      ∀ k d, d ∈ (P k).support → (d : Fin n → ℕ) ∈ U k := by
  simp only [monomialUpperFamilySubmodule, Submodule.mem_pi, Set.mem_univ,
    forall_true_left, mem_monomialUpperSetIdeal]

/-- Exact componentwise containment of the encoded polynomial submodules. -/
theorem monomialUpperFamilySubmodule_le_iff [Nontrivial R]
    (U V : κ → UpperSet (Fin n → ℕ)) :
    monomialUpperFamilySubmodule (R := R) U ≤ monomialUpperFamilySubmodule V ↔
      ∀ k, (U k : Set (Fin n → ℕ)) ⊆ V k := by
  classical
  constructor
  · intro h k
    apply (monomialUpperSetIdeal_le_iff (R := R) (U k) (V k)).mp
    intro P hP
    have hsingle : Pi.single k P ∈ monomialUpperFamilySubmodule U := by
      change ∀ j ∈ (Set.univ : Set κ),
        (Pi.single k P : κ → MvPolynomial (Fin n) R) j ∈
          monomialUpperSetIdeal (R := R) (U j)
      intro j hj
      by_cases hjk : j = k
      · subst j
        simpa using hP
      · simp [hjk]
    have htarget := h hsingle
    have hk := htarget k (Set.mem_univ k)
    simpa using hk
  · intro h P hP
    apply (mem_monomialUpperFamilySubmodule V P).mpr
    intro k d hd
    exact h k ((mem_monomialUpperFamilySubmodule U P).mp hP k d hd)

/-- The encoding is injective, with order reversal only coming from the
bundled reverse-inclusion convention for UpperSet. -/
theorem monomialUpperFamilySubmodule_injective [Nontrivial R] :
    Function.Injective
      (monomialUpperFamilySubmodule (R := R) :
        (κ → UpperSet (Fin n → ℕ)) →
          Submodule (MvPolynomial (Fin n) R) (κ → MvPolynomial (Fin n) R)) := by
  intro U V h
  have hUV := (monomialUpperFamilySubmodule_le_iff U V).mp h.le
  have hVU := (monomialUpperFamilySubmodule_le_iff V U).mp h.ge
  funext k
  exact SetLike.coe_injective (Set.Subset.antisymm (hUV k) (hVU k))

section DegreeCounts

variable [Finite κ]

/-- The finite set of selected component monomials in one ordinary degree. -/
def monomialUpperFamilyDegreeSlice (U : κ → UpperSet (Fin n → ℕ)) (d : ℕ) :
    Set (κ × (Fin n →₀ ℕ)) :=
  {t | (t.2 : Fin n → ℕ) ∈ U t.1 ∧ t.2.degree = d}

theorem monomialUpperFamilyDegreeSlice_finite
    (U : κ → UpperSet (Fin n → ℕ)) (d : ℕ) :
    (monomialUpperFamilyDegreeSlice U d).Finite := by
  apply ((Set.finite_univ : (Set.univ : Set κ).Finite).prod
    (Finsupp.finite_of_degree_eq (σ := Fin n) d)).subset
  intro t ht
  exact ⟨Set.mem_univ _, ht.2⟩

/-- The number of selected monomial basis terms in an ordinary degree. -/
def monomialUpperFamilyDegreeCount (U : κ → UpperSet (Fin n → ℕ)) (d : ℕ) : ℕ :=
  (monomialUpperFamilyDegreeSlice U d).ncard

/-- Comparable exponent families with identical finite degree counts
are equal: inclusion and equal finite cardinality agree degree by degree. -/
theorem monomialUpperFamily_eq_of_le_of_degreeCount_eq
    (U V : κ → UpperSet (Fin n → ℕ)) (hUV : U ≤ V)
    (hcount : ∀ d, monomialUpperFamilyDegreeCount U d = monomialUpperFamilyDegreeCount V d) :
    U = V := by
  have hslices (d : ℕ) : monomialUpperFamilyDegreeSlice V d =
      monomialUpperFamilyDegreeSlice U d := by
    apply Set.eq_of_subset_of_ncard_le ?_ (hcount d).le
      (monomialUpperFamilyDegreeSlice_finite U d)
    intro t ht
    exact ⟨hUV t.1 ht.1, ht.2⟩
  funext k
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm x
    have hd : (d : Fin n → ℕ) = x := rfl
    have hmem : (k, d) ∈ monomialUpperFamilyDegreeSlice U d.degree := ⟨hd.symm ▸ hx, rfl⟩
    rw [← hslices d.degree] at hmem
    have hV := hmem.1
    rwa [hd] at hV
  · intro hx
    exact hUV k hx

/-- Equal degree-count data define an antichain in the actual reverse
componentwise inclusion order. -/
theorem monomialUpperFamily_fixed_degreeCounts_antichain (h : ℕ → ℕ) :
    IsAntichain (· ≤ ·)
      {U : κ → UpperSet (Fin n → ℕ) | ∀ d, monomialUpperFamilyDegreeCount U d = h d} := by
  intro U hU V hV hne hUV
  exact hne (monomialUpperFamily_eq_of_le_of_degreeCount_eq U V hUV
    (fun d => (hU d).trans (hV d).symm))

/-- The actual Higman/Maclagan consequence makes every fixed degree-count
fiber finite; no separate finiteness hypothesis is introduced. -/
theorem monomialUpperFamily_fixed_degreeCounts_finite (h : ℕ → ℕ) :
    {U : κ → UpperSet (Fin n → ℕ) | ∀ d, monomialUpperFamilyDegreeCount U d = h d}.Finite :=
  monomialUpperSetFamily_antichain_finite n κ
    (monomialUpperFamily_fixed_degreeCounts_antichain h)

end DegreeCounts

end AbelFormalization
