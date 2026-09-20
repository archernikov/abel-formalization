import AbelFormalization.WeightedMonomialCountFiniteness
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

/-!
# Finite leading covers and a uniform bound for a finite upper-family set

Dickson supplies actual exponent generators in each component. For a finite
set of upper-set families, the union of the
selected finite covers has bounded integer degree under any fixed grading.
The bound is chosen before the member of the family.
-/

noncomputable section

namespace AbelFormalization

variable {κ : Type*} [Finite κ] {n : ℕ}

/-- Every actual componentwise exponent upper family has a finite cover by
its own module terms. Every term of the family is divisible componentwise
by one of these selected terms. -/
theorem exists_finset_monomialUpperFamily_cover
    (U : κ → UpperSet (Fin n → ℕ)) :
    ∃ s : Finset (κ × (Fin n →₀ ℕ)),
      (∀ t ∈ s, (t.2 : Fin n → ℕ) ∈ U t.1) ∧
      ∀ k (d : Fin n →₀ ℕ), (d : Fin n → ℕ) ∈ U k →
        ∃ u ∈ s, u.1 = k ∧ u.2 ≤ d := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  choose a ha using fun k : κ => monomialUpperSet_exists_finset_generators (U k)
  let A := Σ k : κ, {x : Fin n → ℕ // x ∈ a k}
  let term : A → κ × (Fin n →₀ ℕ) :=
    fun t => (t.1, Finsupp.equivFunOnFinite.symm t.2.val)
  let s : Finset (κ × (Fin n →₀ ℕ)) := Finset.univ.image term
  refine ⟨s, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
    exact (ha u.1 u.2.val).mpr ⟨u.2.val, u.2.property, le_rfl⟩
  · intro k d hd
    obtain ⟨x, hx, hxd⟩ := (ha k (d : Fin n → ℕ)).mp hd
    let u : A := ⟨k, ⟨x, hx⟩⟩
    refine ⟨term u, Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩, rfl, ?_⟩
    exact hxd

/-- A finite family of actual monomial upper families has finite covers
whose degrees are bounded by one natural number. Integer degrees may be
negative. No additivity or finite-fiber assumption on the grading is used
in this finite-family step. -/
theorem finite_monomialUpperFamily_cover_degree_bound
    (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (F : Set (κ → UpperSet (Fin n → ℕ))) (hF : F.Finite) :
    ∃ D : ℕ, ∀ U ∈ F, ∃ s : Finset (κ × (Fin n →₀ ℕ)),
      (∀ t ∈ s, (t.2 : Fin n → ℕ) ∈ U t.1) ∧
      (∀ k (d : Fin n →₀ ℕ), (d : Fin n → ℕ) ∈ U k →
        ∃ u ∈ s, u.1 = k ∧ u.2 ≤ d) ∧
      ∀ t ∈ s, grade t ≤ (D : ℤ) := by
  classical
  let : Fintype F := hF.fintype
  choose s hmember hcover using fun U : F => exists_finset_monomialUpperFamily_cover U.val
  let D : ℕ := Finset.univ.sup (fun U : F => (s U).sup (fun t => (grade t).toNat))
  refine ⟨D, ?_⟩
  intro U hUF
  let u : F := ⟨U, hUF⟩
  refine ⟨s u, hmember u, hcover u, ?_⟩
  intro t ht
  have hfirst : (grade t).toNat ≤ (s u).sup (fun v => (grade v).toNat) :=
    Finset.le_sup (f := fun v => (grade v).toNat) ht
  have hsecond : (s u).sup (fun v => (grade v).toNat) ≤ D :=
    Finset.le_sup (f := fun U : F => (s U).sup (fun v => (grade v).toNat))
      (Finset.mem_univ u)
  exact (Int.self_le_toNat (grade t)).trans (Int.ofNat_le.mpr (hfirst.trans hsecond))

/-- Fixed positive weighted count data give one bound on finite covers
for every actual upper family realizing those data. -/
theorem monomialUpperFamily_fixed_weightedCounts_cover_degree_bound
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : κ → ℤ) (h : ℤ → ℕ) :
    ∃ D : ℕ, ∀ U : κ → UpperSet (Fin n → ℕ),
      (∀ degree, monomialUpperFamilyWeightedDegreeCount weight shift U degree = h degree) →
      ∃ s : Finset (κ × (Fin n →₀ ℕ)),
        (∀ t ∈ s, (t.2 : Fin n → ℕ) ∈ U t.1) ∧
        (∀ k (d : Fin n →₀ ℕ), (d : Fin n → ℕ) ∈ U k →
          ∃ u ∈ s, u.1 = k ∧ u.2 ≤ d) ∧
        ∀ t ∈ s, shiftedModuleMonomialDegree weight shift t ≤ (D : ℤ) :=
  finite_monomialUpperFamily_cover_degree_bound
    (shiftedModuleMonomialDegree weight shift)
    {U | ∀ degree, monomialUpperFamilyWeightedDegreeCount weight shift U degree = h degree}
    (monomialUpperFamily_fixed_weightedDegreeCounts_finite weight hweight shift h)

end AbelFormalization
