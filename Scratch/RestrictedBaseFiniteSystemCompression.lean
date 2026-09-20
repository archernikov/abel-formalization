import AbelFormalization.PaperRankCoordinates
import AbelFormalization.RestrictedExpressionBaseAnalyticPolynomial
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Finite-system compression for the restricted expression base

A finite family of base expressions first has polynomial representatives in
the possibly infinite symbol type
`Fin a ⊕ (Fin m ⊕ (ι × ℕ))`.  This file takes the union of the Abel-jet
variables used by those representatives, enumerates that finite union by a
`Fin b`, and renames the whole family into the paper's symbol type
`PaperRankSymbols m a b`.

The coefficients remain actual representatives analytic near the fixed
closed box.  A second finite union records every coefficient which occurs in
the support of the renamed polynomial family.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- A finite list of named Abel jets, evaluated as a map on the paper's
parameter variables `(s,w)`. -/
def restrictedSelectedAbelJets
    (A : ℝ → ℝ) {m p b : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ) :
    PaperRankParameterSpace m p → PaperRankRealSpace b :=
  fun sw j =>
    iteratedDeriv (selected j).2 A
      (sw.1 (representative (selected j).1) +
        (offset (selected j).1 : RestrictedBoxSpace p → ℝ) sw.2)

/-- Include the paper symbols `y,s,V` into the unrestricted base symbol
type, using `selected` to interpret each finite `V`-coordinate as a named
Abel jet. -/
def restrictedBasePaperSymbolMap {m a b : ℕ}
    (selected : Fin b → ι × ℕ) :
    PaperRankSymbols m a b → RestrictedBasePolynomialSymbol ι m a :=
  Sum.map id (Sum.map id selected)

theorem restrictedBasePaperSymbolMap_injective {m a b : ℕ}
    {selected : Fin b → ι × ℕ} (hselected : Function.Injective selected) :
    Function.Injective (restrictedBasePaperSymbolMap (m := m) (a := a) selected) := by
  unfold restrictedBasePaperSymbolMap
  exact Function.injective_id.sumMap
    (Function.injective_id.sumMap hselected)

/-- The full base-symbol valuation restricted along the finite symbol map is
exactly the paper valuation `y,s,V(s,w)`. -/
theorem restrictedBasePolynomialSymbolValue_comp_paperSymbolMap
    (A : ℝ → ℝ) {m p a b : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ) (x : RestrictedSource m p a) :
    restrictedBasePolynomialSymbolValue A representative offset x ∘
        restrictedBasePaperSymbolMap selected =
      paperRankSymbolArgument
        (restrictedSelectedAbelJets A representative offset selected) x := by
  funext z
  rcases z with k | z
  · rfl
  · rcases z with i | j
    · rfl
    · rfl

/-- Evaluate a polynomial already expressed in the paper's finite symbol
type, with analytic-box representatives as coefficients. -/
def restrictedPaperPolynomialValue
    (A : ℝ → ℝ) {m p a b : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ)
    (P : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    RestrictedSource m p a → ℝ :=
  fun x =>
    MvPolynomial.eval₂
      (subalgebraPointEval
        (RestrictedBox.analyticNearClosedBoxSubalgebra D) x.1.2)
      (paperRankSymbolArgument
        (restrictedSelectedAbelJets A representative offset selected) x) P

/-- Renaming a paper polynomial into the full base symbol type does not
change its value. -/
theorem restrictedBasePolynomialValue_rename_paper
    (A : ℝ → ℝ) {m p a b : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ)
    (P : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    restrictedBasePolynomialValue A D representative offset
        (MvPolynomial.rename (restrictedBasePaperSymbolMap selected) P) =
      restrictedPaperPolynomialValue A D representative offset selected P := by
  funext x
  unfold restrictedBasePolynomialValue restrictedPaperPolynomialValue
  rw [MvPolynomial.eval₂_rename]
  rw [restrictedBasePolynomialSymbolValue_comp_paperSymbolMap]

/-- Abel-jet variables occurring in one unrestricted base polynomial. -/
noncomputable def restrictedBasePolynomialJetVariables
    {m a : ℕ}
    {B : Type*} [CommSemiring B]
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B) :
    Finset (ι × ℕ) := by
  classical
  exact P.vars.biUnion fun z =>
    match z with
    | Sum.inr (Sum.inr kr) => {kr}
    | _ => ∅

@[simp]
theorem mem_restrictedBasePolynomialJetVariables_iff
    {m a : ℕ}
    {B : Type*} [CommSemiring B]
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B)
    (kr : ι × ℕ) :
    kr ∈ restrictedBasePolynomialJetVariables P ↔
      Sum.inr (Sum.inr kr) ∈ P.vars := by
  classical
  constructor
  · intro hkr
    simp only [restrictedBasePolynomialJetVariables,
      Finset.mem_biUnion] at hkr
    obtain ⟨z, hz, hkrz⟩ := hkr
    rcases z with k | z
    · simp at hkrz
    · rcases z with i | kr'
      · simp at hkrz
      · have hEq : kr = kr' := by simpa using hkrz
        simpa [hEq] using hz
  · intro hkr
    simp only [restrictedBasePolynomialJetVariables,
      Finset.mem_biUnion]
    refine ⟨Sum.inr (Sum.inr kr), hkr, ?_⟩
    simp

/-- The common finite set of Abel-jet variables used by a finite polynomial
family. -/
noncomputable def restrictedBasePolynomialFamilyJetVariables
    {m a n : ℕ}
    {B : Type*} [CommSemiring B]
    (P : Fin n → MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B) :
    Finset (ι × ℕ) := by
  classical
  exact Finset.univ.biUnion fun i =>
    restrictedBasePolynomialJetVariables (P i)

theorem restrictedBasePolynomialJetVariables_subset_family
    {m a n : ℕ}
    {B : Type*} [CommSemiring B]
    (P : Fin n → MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B)
    (i : Fin n) :
    restrictedBasePolynomialJetVariables (P i) ⊆
      restrictedBasePolynomialFamilyJetVariables P := by
  classical
  intro kr hkr
  simp only [restrictedBasePolynomialFamilyJetVariables,
    Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, hkr⟩

@[simp]
theorem mem_restrictedBasePolynomialFamilyJetVariables_iff
    {m a n : ℕ}
    {B : Type*} [CommSemiring B]
    (P : Fin n → MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B)
    (kr : ι × ℕ) :
    kr ∈ restrictedBasePolynomialFamilyJetVariables P ↔
      ∃ i : Fin n, Sum.inr (Sum.inr kr) ∈ (P i).vars := by
  classical
  simp [restrictedBasePolynomialFamilyJetVariables,
    mem_restrictedBasePolynomialJetVariables_iff]

/-- A canonical duplicate-free enumeration of a finite set of named Abel
jets. -/
noncomputable def restrictedJetEnumeration (S : Finset (ι × ℕ)) :
    Fin S.card → ι × ℕ :=
  fun j => (S.equivFin.symm j).1

theorem restrictedJetEnumeration_injective (S : Finset (ι × ℕ)) :
    Function.Injective (restrictedJetEnumeration S) := by
  unfold restrictedJetEnumeration
  exact Subtype.val_injective.comp S.equivFin.symm.injective

@[simp]
theorem restrictedJetEnumeration_equivFin
    (S : Finset (ι × ℕ)) (kr : S) :
    restrictedJetEnumeration S (S.equivFin kr) = kr.1 := by
  simp [restrictedJetEnumeration]

/-- If `S` contains every jet variable of `P`, then the full variable set of
`P` lies in the range of the paper-symbol inclusion determined by `S`. -/
theorem restrictedBasePolynomial_vars_subset_range_paperSymbolMap
    {m a : ℕ}
    {B : Type*} [CommSemiring B]
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B)
    (S : Finset (ι × ℕ))
    (hS : restrictedBasePolynomialJetVariables P ⊆ S) :
    (↑P.vars : Set (RestrictedBasePolynomialSymbol ι m a)) ⊆
      Set.range (restrictedBasePaperSymbolMap
        (m := m) (a := a) (restrictedJetEnumeration S)) := by
  classical
  intro z hz
  rcases z with k | z
  · exact ⟨Sum.inl k, rfl⟩
  · rcases z with i | kr
    · exact ⟨Sum.inr (Sum.inl i), rfl⟩
    · have hkrP : kr ∈ restrictedBasePolynomialJetVariables P :=
        (mem_restrictedBasePolynomialJetVariables_iff P kr).2 hz
      have hkrS : kr ∈ S := hS hkrP
      refine ⟨Sum.inr (Sum.inr (S.equivFin ⟨kr, hkrS⟩)), ?_⟩
      simp [restrictedBasePaperSymbolMap, restrictedJetEnumeration]

/-- Simultaneously rename a finite family of unrestricted base polynomials
into one common `PaperRankSymbols` type.  The final equivalence identifies
the chosen finite jet set exactly with the jets occurring in the input
family. -/
theorem exists_restrictedPaperPolynomialFamily_rename
    {m a n : ℕ}
    {B : Type*} [CommSemiring B]
    (P : Fin n → MvPolynomial (RestrictedBasePolynomialSymbol ι m a) B) :
    ∃ S : Finset (ι × ℕ),
      ∃ Q : Fin n → MvPolynomial (PaperRankSymbols m a S.card) B,
        (∀ i, MvPolynomial.rename
          (restrictedBasePaperSymbolMap
            (m := m) (a := a) (restrictedJetEnumeration S)) (Q i) = P i) ∧
        (∀ kr, kr ∈ S ↔
          ∃ i : Fin n, Sum.inr (Sum.inr kr) ∈ (P i).vars) := by
  classical
  let S := restrictedBasePolynomialFamilyJetVariables P
  have hchoice : ∀ i : Fin n,
      ∃ Q : MvPolynomial (PaperRankSymbols m a S.card) B,
        MvPolynomial.rename
          (restrictedBasePaperSymbolMap
            (m := m) (a := a) (restrictedJetEnumeration S)) Q = P i := by
    intro i
    exact MvPolynomial.exists_rename_eq_of_vars_subset_range
      (P i)
      (restrictedBasePaperSymbolMap
        (m := m) (a := a) (restrictedJetEnumeration S))
      (restrictedBasePaperSymbolMap_injective
        (restrictedJetEnumeration_injective S))
      (restrictedBasePolynomial_vars_subset_range_paperSymbolMap
        (P i) S (restrictedBasePolynomialJetVariables_subset_family P i))
  choose Q hQ using hchoice
  refine ⟨S, Q, hQ, ?_⟩
  intro kr
  exact mem_restrictedBasePolynomialFamilyJetVariables_iff P kr

/-- All analytic coefficients actually used by a finite polynomial family.
Only coefficients of supported monomials are recorded. -/
noncomputable def restrictedPolynomialFamilyCoefficients
    {n : ℕ} {σ B : Type*} [CommSemiring B]
    (Q : Fin n → MvPolynomial σ B) : Finset B := by
  classical
  exact Finset.univ.biUnion fun i =>
    (Q i).support.image (Q i).coeff

theorem coeff_mem_restrictedPolynomialFamilyCoefficients
    {n : ℕ} {σ B : Type*} [CommSemiring B]
    (Q : Fin n → MvPolynomial σ B)
    (i : Fin n) (d : σ →₀ ℕ) (hd : d ∈ (Q i).support) :
    (Q i).coeff d ∈ restrictedPolynomialFamilyCoefficients Q := by
  classical
  simp only [restrictedPolynomialFamilyCoefficients,
    Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- A finite family of restricted base expressions is one finite polynomial
system in the paper's variables.  `S` records the selected representative
labels and derivative orders; `C` records every analytic coefficient used in
the polynomial supports. -/
theorem exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    ∃ S : Finset (ι × ℕ),
      ∃ Q : Fin n → MvPolynomial (PaperRankSymbols m a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
      ∃ C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D),
        (∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C) ∧
        ∀ i, restrictedPaperPolynomialValue A D representative offset
          (restrictedJetEnumeration S) (Q i) = F i := by
  classical
  have hrepresentative : ∀ i : Fin n,
      ∃ P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
        restrictedBasePolynomialValue A D representative offset P = F i := by
    intro i
    exact exists_restrictedBasePolynomialValue_eq_of_mem
      A D representative offset (hF i)
  choose P hP using hrepresentative
  obtain ⟨S, Q, hrename, hS⟩ :=
    exists_restrictedPaperPolynomialFamily_rename P
  let C := restrictedPolynomialFamilyCoefficients Q
  refine ⟨S, Q, C, ?_, ?_⟩
  · intro i d hd
    exact coeff_mem_restrictedPolynomialFamilyCoefficients Q i d hd
  · intro i
    calc
      restrictedPaperPolynomialValue A D representative offset
          (restrictedJetEnumeration S) (Q i) =
          restrictedBasePolynomialValue A D representative offset
            (MvPolynomial.rename
              (restrictedBasePaperSymbolMap
                (m := m) (a := a) (restrictedJetEnumeration S)) (Q i)) :=
        (restrictedBasePolynomialValue_rename_paper
          A D representative offset (restrictedJetEnumeration S) (Q i)).symm
      _ = restrictedBasePolynomialValue A D representative offset (P i) := by
        rw [hrename i]
      _ = F i := hP i

/-- The same compression theorem stated for level zero of an arbitrary
restricted exponential tower.  This is the tower-level form used by the
outer base case. -/
theorem RestrictedExpressionTower.exists_restrictedPaperPolynomialFamily_of_mem_level_zero
    (A : ℝ → ℝ) {m p a n ell : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (F : Fin n → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ T.level 0) :
    ∃ S : Finset (ι × ℕ),
      ∃ Q : Fin n → MvPolynomial (PaperRankSymbols m a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
      ∃ C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D),
        (∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C) ∧
        ∀ i, restrictedPaperPolynomialValue A D representative offset
          (restrictedJetEnumeration S) (Q i) = F i := by
  apply exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
    A D representative offset F
  intro i
  simpa only [T.level_zero] using hF i

end AbelFormalization
