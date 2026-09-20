import AbelFormalization.MonomialSubmoduleEncoding
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite monomial coordinates in shifted positive weighted degrees

The ambient module is the actual finite
free module `κ → MvPolynomial (Fin n) K`. Variable degrees are arbitrary
positive natural numbers and component shifts are arbitrary integers.
Each homogeneous piece is identified with finitely supported coordinates
on the finite set of module monomials of that weighted degree.

For the actual monomial submodule encoded by exponent upper sets, its
homogeneous-piece dimension is the number of selected degree monomials.
This does not yet prove that initial formation preserves the dimensions of
an arbitrary polynomial submodule.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {K κ : Type*} [Field K] [Finite κ] {n : ℕ}

/-- The actual coefficient array of a finite tuple of polynomials, bundled
as a linear equivalence rather than an assumed coordinate representation. -/
def polynomialModuleCoeffEquiv :
    (κ → MvPolynomial (Fin n) K) ≃ₗ[K] (κ × (Fin n →₀ ℕ)) →₀ K :=
  ((LinearEquiv.piCongrRight (fun _ : κ =>
      (AddMonoidAlgebra.coeffLinearEquiv K :
        MvPolynomial (Fin n) K ≃ₗ[K] (Fin n →₀ ℕ) →₀ K))).trans
    (Finsupp.linearEquivFunOnFinite K ((Fin n →₀ ℕ) →₀ K) κ).symm).trans
    (Finsupp.curryLinearEquiv K).symm

@[simp]
theorem polynomialModuleCoeffEquiv_apply
    (P : κ → MvPolynomial (Fin n) K) (k : κ) (d : Fin n →₀ ℕ) :
    polynomialModuleCoeffEquiv P (k, d) = (P k).coeff d := by
  rfl

/-- The actual coefficient subspace supported on any set of component
monomials. The set need not be finite to define the subspace. -/
def polynomialModuleSupported (S : Set (κ × (Fin n →₀ ℕ))) :
    Submodule K (κ → MvPolynomial (Fin n) K) :=
  (Finsupp.supported K K S).comap polynomialModuleCoeffEquiv.toLinearMap

theorem mem_polynomialModuleSupported (S : Set (κ × (Fin n →₀ ℕ)))
    (P : κ → MvPolynomial (Fin n) K) :
    P ∈ polynomialModuleSupported S ↔
      ∀ k d, (P k).coeff d ≠ 0 → (k, d) ∈ S := by
  rw [polynomialModuleSupported, Submodule.mem_comap, Finsupp.mem_supported]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    Prod.forall, LinearEquiv.coe_coe, polynomialModuleCoeffEquiv_apply]

/-- Restricting the genuine coefficient equivalence identifies the support
subspace with exactly the coordinates indexed by its allowed monomials. -/
def polynomialModuleSupportedEquiv (S : Set (κ × (Fin n →₀ ℕ))) :
    polynomialModuleSupported (K := K) S ≃ₗ[K] S →₀ K :=
  (polynomialModuleCoeffEquiv.ofSubmodule' (Finsupp.supported K K S)).trans
    (Finsupp.supportedEquivFinsupp (R := K) S)

/-- A finite set of allowed component monomials gives precisely that
dimension in the actual polynomial module. -/
theorem finrank_polynomialModuleSupported
    (S : Set (κ × (Fin n →₀ ℕ))) (hS : S.Finite) :
    Module.finrank K (polynomialModuleSupported (K := K) S) = S.ncard := by
  let : Fintype S := hS.fintype
  calc
    Module.finrank K (polynomialModuleSupported (K := K) S) =
        Module.finrank K (S →₀ K) := (polynomialModuleSupportedEquiv S).finrank_eq
    _ = Fintype.card S := Module.finrank_finsupp_self K
    _ = S.ncard := Set.fintypeCard_eq_ncard S

/-- Weighted ordinary degree of a module monomial, including its arbitrary
integer component shift. -/
def shiftedModuleMonomialDegree (weight : Fin n → ℕ) (shift : κ → ℤ)
    (t : κ × (Fin n →₀ ℕ)) : ℤ :=
  (Finsupp.weight weight t.2 : ℤ) + shift t.1

/-- The component monomials in one shifted weighted ordinary degree. -/
def shiftedModuleDegreeTerms (weight : Fin n → ℕ) (shift : κ → ℤ) (degree : ℤ) :
    Set (κ × (Fin n →₀ ℕ)) :=
  {t | shiftedModuleMonomialDegree weight shift t = degree}

/-- Strictly positive variable degrees make every shifted degree slice
finite, including negative degrees and arbitrary integer shifts. -/
theorem shiftedModuleDegreeTerms_finite (weight : Fin n → ℕ)
    (hweight : ∀ i, 0 < weight i) (shift : κ → ℤ) (degree : ℤ) :
    (shiftedModuleDegreeTerms weight shift degree).Finite := by
  have hcomponent (k : κ) :
      {d : Fin n →₀ ℕ | (Finsupp.weight weight d : ℤ) + shift k = degree}.Finite := by
    apply (Finsupp.finite_of_nat_weight_le weight (fun i => (hweight i).ne')
      (degree - shift k).toNat).subset
    intro d hd
    have he : (Finsupp.weight weight d : ℤ) = degree - shift k := eq_sub_of_add_eq hd
    exact Int.ofNat_le.mp (he.trans_le (Int.self_le_toNat _))
  have hfinite := Set.finite_iUnion (fun k : κ => (hcomponent k).image (Prod.mk k))
  apply hfinite.subset
  intro t ht
  exact Set.mem_iUnion.mpr ⟨t.1, ⟨t.2, ht, rfl⟩⟩

/-- The ordinary homogeneous piece as an actual scalar subspace of the
finite free polynomial module, allowing positive weighted degrees. -/
def weightedPolynomialModulePiece (weight : Fin n → ℕ) (shift : κ → ℤ) (degree : ℤ) :
    Submodule K (κ → MvPolynomial (Fin n) K) :=
  polynomialModuleSupported (shiftedModuleDegreeTerms weight shift degree)

theorem finrank_weightedPolynomialModulePiece (weight : Fin n → ℕ)
    (hweight : ∀ i, 0 < weight i) (shift : κ → ℤ) (degree : ℤ) :
    Module.finrank K (weightedPolynomialModulePiece (K := K) weight shift degree) =
      (shiftedModuleDegreeTerms weight shift degree).ncard :=
  finrank_polynomialModuleSupported _ (shiftedModuleDegreeTerms_finite weight hweight shift degree)

/-- The selected monomials of a componentwise monomial submodule. -/
def monomialUpperFamilyTerms (U : κ → UpperSet (Fin n → ℕ)) : Set (κ × (Fin n →₀ ℕ)) :=
  {t | (t.2 : Fin n → ℕ) ∈ U t.1}

/-- Intersecting an actual monomial polynomial submodule with a weighted
homogeneous piece selects exactly the corresponding component monomials. -/
theorem monomialUpperFamily_weightedPiece_eq_supported
    (U : κ → UpperSet (Fin n → ℕ))
    (weight : Fin n → ℕ) (shift : κ → ℤ) (degree : ℤ) :
    (monomialUpperFamilySubmodule (R := K) U).restrictScalars K ⊓
        weightedPolynomialModulePiece weight shift degree =
      polynomialModuleSupported
        (monomialUpperFamilyTerms U ∩ shiftedModuleDegreeTerms weight shift degree) := by
  ext P
  constructor
  · rintro ⟨hU, hdegree⟩
    apply (mem_polynomialModuleSupported _ P).mpr
    intro k d hd
    refine ⟨?_, ?_⟩
    · exact (mem_monomialUpperFamilySubmodule U P).mp hU k d
        (MvPolynomial.mem_support_iff.mpr hd)
    · exact (mem_polynomialModuleSupported _ P).mp hdegree k d hd
  · intro h
    have hterm := (mem_polynomialModuleSupported _ P).mp h
    refine ⟨?_, ?_⟩
    · apply (mem_monomialUpperFamilySubmodule U P).mpr
      intro k d hd
      exact (hterm k d (MvPolynomial.mem_support_iff.mp hd)).1
    · apply (mem_polynomialModuleSupported _ P).mpr
      intro k d hd
      exact (hterm k d hd).2

/-- The precise weighted-and-shifted degree-count dimension identity for
the actual monomial submodule. -/
theorem finrank_monomialUpperFamily_weightedPiece
    (U : κ → UpperSet (Fin n → ℕ))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : κ → ℤ) (degree : ℤ) :
    Module.finrank K
        (((monomialUpperFamilySubmodule (R := K) U).restrictScalars K ⊓
          weightedPolynomialModulePiece weight shift degree) :
            Submodule K (κ → MvPolynomial (Fin n) K)) =
      (monomialUpperFamilyTerms U ∩ shiftedModuleDegreeTerms weight shift degree).ncard := by
  rw [monomialUpperFamily_weightedPiece_eq_supported]
  exact finrank_polynomialModuleSupported _
    ((shiftedModuleDegreeTerms_finite weight hweight shift degree).subset Set.inter_subset_right)

end AbelFormalization
