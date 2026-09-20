import AbelFormalization.WeightedPolynomialModulePieces

set_option autoImplicit false

/-!
# Finiteness of monomial submodules with fixed weighted degree counts

First, an arbitrary integer grading with finite fibers is used to compare
actual exponent upper-set families. Equal finite
counts force equality for comparable families, so the proved reverse-
inclusion well-quasi-order makes every fixed-count family finite.

Positive natural variable degrees and arbitrary integer component shifts
satisfy the finite-fiber hypothesis. For actual monomial polynomial
submodules, the counts equal the already proved homogeneous-piece dimensions.
No claim about initial modules of arbitrary polynomial submodules is assumed.
-/

noncomputable section

namespace AbelFormalization

variable {κ : Type*} {n : ℕ}

/-- Selected actual component monomials in a fiber of an integer grading. -/
def monomialUpperFamilyGradedSlice (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (U : κ → UpperSet (Fin n → ℕ)) (degree : ℤ) : Set (κ × (Fin n →₀ ℕ)) :=
  {t | (t.2 : Fin n → ℕ) ∈ U t.1 ∧ grade t = degree}

/-- The selected slice is finite whenever the entire grading fiber is. -/
theorem monomialUpperFamilyGradedSlice_finite
    (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (hfinite : ∀ degree, {t | grade t = degree}.Finite)
    (U : κ → UpperSet (Fin n → ℕ)) (degree : ℤ) :
    (monomialUpperFamilyGradedSlice grade U degree).Finite :=
  (hfinite degree).subset (fun _ ht => ht.2)

/-- The finite count of selected actual monomials in the specified fiber. -/
def monomialUpperFamilyGradedCount (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (U : κ → UpperSet (Fin n → ℕ)) (degree : ℤ) : ℕ :=
  (monomialUpperFamilyGradedSlice grade U degree).ncard

/-- Comparable actual exponent families with the same finite counts are
equal, degree by degree. The grading need not be additive or nonnegative. -/
theorem monomialUpperFamily_eq_of_le_of_gradedCount_eq
    (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (hfinite : ∀ degree, {t | grade t = degree}.Finite)
    (U V : κ → UpperSet (Fin n → ℕ)) (hUV : U ≤ V)
    (hcount : ∀ degree, monomialUpperFamilyGradedCount grade U degree =
      monomialUpperFamilyGradedCount grade V degree) : U = V := by
  have hslices (degree : ℤ) : monomialUpperFamilyGradedSlice grade V degree =
      monomialUpperFamilyGradedSlice grade U degree := by
    apply Set.eq_of_subset_of_ncard_le ?_ (hcount degree).le
      (monomialUpperFamilyGradedSlice_finite grade hfinite U degree)
    intro t ht
    exact ⟨hUV t.1 ht.1, ht.2⟩
  funext k
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm x
    have hd : (d : Fin n → ℕ) = x := rfl
    have hmem : (k, d) ∈ monomialUpperFamilyGradedSlice grade U (grade (k, d)) :=
      ⟨hd.symm ▸ hx, rfl⟩
    rw [← hslices (grade (k, d))] at hmem
    have hV := hmem.1
    rwa [hd] at hV
  · intro hx
    exact hUV k hx

/-- A fixed full integer count function determines an antichain of actual
upper-set families, using the bundled reverse-inclusion order. -/
theorem monomialUpperFamily_fixed_gradedCounts_antichain
    (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (hfinite : ∀ degree, {t | grade t = degree}.Finite) (h : ℤ → ℕ) :
    IsAntichain (· ≤ ·) {U : κ → UpperSet (Fin n → ℕ) |
      ∀ degree, monomialUpperFamilyGradedCount grade U degree = h degree} := by
  intro U hU V hV hne hUV
  exact hne (monomialUpperFamily_eq_of_le_of_gradedCount_eq grade hfinite U V hUV
    (fun degree => (hU degree).trans (hV degree).symm))

/-- The actual Higman/Maclagan theorem implies finiteness of the entire
fixed-count family when the component set is finite. -/
theorem monomialUpperFamily_fixed_gradedCounts_finite [Finite κ]
    (grade : κ × (Fin n →₀ ℕ) → ℤ)
    (hfinite : ∀ degree, {t | grade t = degree}.Finite) (h : ℤ → ℕ) :
    {U : κ → UpperSet (Fin n → ℕ) |
      ∀ degree, monomialUpperFamilyGradedCount grade U degree = h degree}.Finite :=
  monomialUpperSetFamily_antichain_finite n κ
    (monomialUpperFamily_fixed_gradedCounts_antichain grade hfinite h)

/-- Positive weighted ordinary degrees with arbitrary component shifts. -/
def monomialUpperFamilyWeightedDegreeCount (weight : Fin n → ℕ) (shift : κ → ℤ)
    (U : κ → UpperSet (Fin n → ℕ)) (degree : ℤ) : ℕ :=
  monomialUpperFamilyGradedCount (shiftedModuleMonomialDegree weight shift) U degree

/-- The relevant generic slice is exactly the selected weighted
homogeneous-piece monomial set, not a different grading. -/
theorem monomialUpperFamilyGradedSlice_weighted
    (weight : Fin n → ℕ) (shift : κ → ℤ)
    (U : κ → UpperSet (Fin n → ℕ)) (degree : ℤ) :
    monomialUpperFamilyGradedSlice (shiftedModuleMonomialDegree weight shift) U degree =
      monomialUpperFamilyTerms U ∩ shiftedModuleDegreeTerms weight shift degree := rfl

/-- Equal shifted weighted degree counts force equality of comparable
actual upper-set families. -/
theorem monomialUpperFamily_eq_of_le_of_weightedDegreeCount_eq [Finite κ]
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i) (shift : κ → ℤ)
    (U V : κ → UpperSet (Fin n → ℕ)) (hUV : U ≤ V)
    (hcount : ∀ degree, monomialUpperFamilyWeightedDegreeCount weight shift U degree =
      monomialUpperFamilyWeightedDegreeCount weight shift V degree) : U = V :=
  monomialUpperFamily_eq_of_le_of_gradedCount_eq
    (shiftedModuleMonomialDegree weight shift)
    (shiftedModuleDegreeTerms_finite weight hweight shift) U V hUV hcount

/-- Every fixed weighted count family is finite; all integer degrees and
all integer component shifts are retained. -/
theorem monomialUpperFamily_fixed_weightedDegreeCounts_finite [Finite κ]
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i) (shift : κ → ℤ) (h : ℤ → ℕ) :
    {U : κ → UpperSet (Fin n → ℕ) |
      ∀ degree, monomialUpperFamilyWeightedDegreeCount weight shift U degree =
        h degree}.Finite :=
  monomialUpperFamily_fixed_gradedCounts_finite
    (shiftedModuleMonomialDegree weight shift)
    (shiftedModuleDegreeTerms_finite weight hweight shift) h

section ActualPolynomialSubmodules

variable {K : Type*} [Field K] [Finite κ]

/-- The weighted counts are the dimensions of the corresponding pieces
of the actual monomial polynomial submodule. -/
theorem finrank_monomialUpperFamily_weightedPiece_eq_count
    (U : κ → UpperSet (Fin n → ℕ))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : κ → ℤ) (degree : ℤ) :
    Module.finrank K
        (((monomialUpperFamilySubmodule (R := K) U).restrictScalars K ⊓
          weightedPolynomialModulePiece weight shift degree) :
            Submodule K (κ → MvPolynomial (Fin n) K)) =
      monomialUpperFamilyWeightedDegreeCount weight shift U degree := by
  rw [finrank_monomialUpperFamily_weightedPiece (K := K) U weight hweight shift degree]
  rfl

/-- Among the actual monomial polynomial submodules, fixing all weighted
piece dimensions leaves only finitely many submodules. This assertion
uses their actual componentwise monomial encoding. -/
theorem monomialUpperFamily_fixed_weightedPieceDimensions_finite
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : κ → ℤ) (h : ℤ → ℕ) :
    {N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K) |
      ∃ U : κ → UpperSet (Fin n → ℕ), N = monomialUpperFamilySubmodule U ∧
        ∀ degree, Module.finrank K
          ((N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) :
            Submodule K (κ → MvPolynomial (Fin n) K)) = h degree}.Finite := by
  have hfinite := (monomialUpperFamily_fixed_weightedDegreeCounts_finite
    weight hweight shift h).image (monomialUpperFamilySubmodule (R := K))
  apply hfinite.subset
  rintro N ⟨U, rfl, hU⟩
  refine ⟨U, ?_, rfl⟩
  intro degree
  rw [← finrank_monomialUpperFamily_weightedPiece_eq_count (K := K)
    U weight hweight shift degree]
  exact hU degree

end ActualPolynomialSubmodules

end AbelFormalization
