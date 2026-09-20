import AbelFormalization.PolynomialModuleHomogeneous
import AbelFormalization.PolynomialModuleLeadingSubmodule
import AbelFormalization.WeightedMonomialCountFiniteness
import AbelFormalization.FiniteLeadingCoordinateDimension
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
# Actual leading-term Hilbert correspondence in shifted weighted degrees

The dimension of a polynomial subspace supported on a finite term set is
derived from its actual coefficient coordinates and
the proved greatest-coordinate dimension theorem. For a homogeneous module,
projection to a leading term's own degree identifies these coordinates with
the corresponding slice of the full leading monomial submodule.
-/

noncomputable section

namespace AbelFormalization

variable {K : Type*} [Field K] {n r q : ℕ}

/-- A fresh type copy avoids the unrelated coordinatewise order already
present on subtypes of module terms. -/
private structure PolynomialModuleTermOrderCopy (α : Type*) where
  val : α

private def polynomialModuleTermOrderCopyEquiv (α : Type*) :
    PolynomialModuleTermOrderCopy α ≃ α where
  toFun := PolynomialModuleTermOrderCopy.val
  invFun := fun x => ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- All actual leading terms of vectors in the scalar subspace. -/
def polynomialModuleLeadingTerms (m : MonomialOrder (Fin n))
    (U : Submodule K (Fin r → MvPolynomial (Fin n) K)) :
    Set (Fin r × (Fin n →₀ ℕ)) :=
  {t | ∃ P ∈ U, IsPolynomialModuleLeadingTerm m P t}

/-- Actual coefficient coordinates indexed by a chosen enumeration of S. -/
def polynomialModuleCoefficientCoordinates {S : Set (Fin r × (Fin n →₀ ℕ))}
    (e : Fin q ≃ S) : (Fin r → MvPolynomial (Fin n) K) →ₗ[K] (Fin q → K) :=
  LinearMap.pi (fun i => (MvPolynomial.lcoeff K (e i).val.2).comp
    (LinearMap.proj (e i).val.1))

@[simp]
theorem polynomialModuleCoefficientCoordinates_apply
    {S : Set (Fin r × (Fin n →₀ ℕ))} (e : Fin q ≃ S)
    (P : Fin r → MvPolynomial (Fin n) K) (i : Fin q) :
    polynomialModuleCoefficientCoordinates e P i = (P (e i).val.1).coeff (e i).val.2 := rfl

/-- If the subspace is supported on S, its actual S-coordinate map loses
no vector. The proof checks coefficients both inside and outside S. -/
theorem polynomialModuleCoefficientCoordinates_injective
    {S : Set (Fin r × (Fin n →₀ ℕ))} (e : Fin q ≃ S)
    (U : Submodule K (Fin r → MvPolynomial (Fin n) K))
    (hU : U ≤ polynomialModuleSupported S) :
    Function.Injective ((polynomialModuleCoefficientCoordinates e).domRestrict U) := by
  classical
  intro P Q h
  apply Subtype.ext
  funext k
  apply MvPolynomial.ext
  intro d
  by_cases ht : (k, d) ∈ S
  · have hi := congrFun h (e.symm ⟨(k, d), ht⟩)
    simpa only [LinearMap.domRestrict_apply, polynomialModuleCoefficientCoordinates_apply,
      e.apply_symm_apply] using hi
  · have hp : ((P : Fin r → MvPolynomial (Fin n) K) k).coeff d = 0 := by
      by_contra hp
      exact ht ((mem_polynomialModuleSupported S P.val).mp (hU P.property) k d hp)
    have hq : ((Q : Fin r → MvPolynomial (Fin n) K) k).coeff d = 0 := by
      by_contra hq
      exact ht ((mem_polynomialModuleSupported S Q.val).mp (hU Q.property) k d hq)
    exact hp.trans hq.symm

/-- Increasing enumeration makes greatest nonzero coordinate witnesses
exactly the original polynomial-module leading-term witnesses. -/
theorem finiteGreatestCoordinates_polynomialModuleCoordinates_iff
    (m : MonomialOrder (Fin n)) {S : Set (Fin r × (Fin n →₀ ℕ))} (e : Fin q ≃ S)
    (hsort : ∀ i j : Fin q, i < j ↔
      polynomialModuleTermKey m (e i).val < polynomialModuleTermKey m (e j).val)
    (U : Submodule K (Fin r → MvPolynomial (Fin n) K))
    (hU : U ≤ polynomialModuleSupported S) (i : Fin q) :
    i ∈ finiteGreatestCoordinates (U.map (polynomialModuleCoefficientCoordinates e)) ↔
      (e i).val ∈ polynomialModuleLeadingTerms m U := by
  classical
  constructor
  · rintro ⟨x, ⟨P, hPU, rfl⟩, hxi, hhigh⟩
    refine ⟨P, hPU, hxi, ?_⟩
    intro u hu
    have huS : u ∈ S := (mem_polynomialModuleSupported S P).mp (hU hPU) u.1 u.2 hu
    let j : Fin q := e.symm ⟨u, huS⟩
    have hej : (e j).val = u := congrArg Subtype.val (e.apply_symm_apply ⟨u, huS⟩)
    apply le_of_not_gt
    intro hgt
    have hij : i < j := (hsort i j).mpr (by rw [hej]; exact hgt)
    exact hu (by simpa only [polynomialModuleCoefficientCoordinates_apply, hej] using hhigh j hij)
  · rintro ⟨P, hPU, hP⟩
    refine ⟨polynomialModuleCoefficientCoordinates e P, ⟨P, hPU, rfl⟩, hP.1, ?_⟩
    intro j hij
    exact hP.coeff_eq_zero_of_lt ((hsort i j).mp hij)

/-- The enumerated coefficient-coordinate theorem gives an actual
leading-term count for any subspace supported on the enumerated finite set. -/
theorem finrank_polynomialModule_eq_leadingTerms_of_enumeration
    (m : MonomialOrder (Fin n)) {S : Set (Fin r × (Fin n →₀ ℕ))} (e : Fin q ≃ S)
    (hsort : ∀ i j : Fin q, i < j ↔
      polynomialModuleTermKey m (e i).val < polynomialModuleTermKey m (e j).val)
    (U : Submodule K (Fin r → MvPolynomial (Fin n) K))
    (hU : U ≤ polynomialModuleSupported S) :
    Module.finrank K U = (polynomialModuleLeadingTerms m U).ncard := by
  classical
  let L := polynomialModuleCoefficientCoordinates (K := K) e
  have hinj := polynomialModuleCoefficientCoordinates_injective e U hU
  have hdim : Module.finrank K (U.map L) = Module.finrank K U := by
    rw [← LinearMap.range_domRestrict U L]
    exact LinearMap.finrank_range_of_inj hinj
  have heinj : Function.Injective (fun i : Fin q => (e i).val) := by
    intro i j h
    exact e.injective (Subtype.ext h)
  have himage : (fun i : Fin q => (e i).val) '' finiteGreatestCoordinates (U.map L) =
      polynomialModuleLeadingTerms m U := by
    ext t
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (finiteGreatestCoordinates_polynomialModuleCoordinates_iff m e hsort U hU i).mp hi
    · intro ht
      obtain ⟨P, hPU, hP⟩ := ht
      have htS : t ∈ S := (mem_polynomialModuleSupported S P).mp (hU hPU) t.1 t.2 hP.1
      let i : Fin q := e.symm ⟨t, htS⟩
      have hei : (e i).val = t := congrArg Subtype.val (e.apply_symm_apply ⟨t, htS⟩)
      refine ⟨i, ?_, hei⟩
      apply (finiteGreatestCoordinates_polynomialModuleCoordinates_iff m e hsort U hU i).mpr
      rw [hei]
      exact ⟨P, hPU, hP⟩
  calc
    Module.finrank K U = Module.finrank K (U.map L) := hdim.symm
    _ = (finiteGreatestCoordinates (U.map L)).ncard :=
      finrank_eq_ncard_finiteGreatestCoordinates _
    _ = ((fun i : Fin q => (e i).val) '' finiteGreatestCoordinates (U.map L)).ncard :=
      (Set.ncard_image_of_injective _ heinj).symm
    _ = (polynomialModuleLeadingTerms m U).ncard := congrArg Set.ncard himage

/-- Sorting the actual finite term set supplies the required enumeration;
the dimension identity has no ordering or echelon-form hypothesis. -/
theorem finrank_polynomialModule_eq_leadingTerms
    (m : MonomialOrder (Fin n)) {S : Set (Fin r × (Fin n →₀ ℕ))} (hS : S.Finite)
    (U : Submodule K (Fin r → MvPolynomial (Fin n) K))
    (hU : U ≤ polynomialModuleSupported S) :
    Module.finrank K U = (polynomialModuleLeadingTerms m U).ncard := by
  classical
  let _ : Fintype S := hS.fintype
  let _ : Fintype (PolynomialModuleTermOrderCopy S) :=
    Fintype.ofEquiv S (polynomialModuleTermOrderCopyEquiv S).symm
  let _ : LinearOrder (PolynomialModuleTermOrderCopy S) := LinearOrder.lift'
    (fun t => polynomialModuleTermKey m t.val.val) (by
      intro a b hab
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      have hab' : a.val = b.val := polynomialModuleTermKey_injective m hab
      have hab'' : a = b := Subtype.ext hab'
      cases hab''
      rfl)
  let eo := Fintype.orderIsoFinOfCardEq (PolynomialModuleTermOrderCopy S) rfl
  let e := eo.toEquiv.trans (polynomialModuleTermOrderCopyEquiv S)
  apply finrank_polynomialModule_eq_leadingTerms_of_enumeration m e ?_ U hU
  intro i j
  exact eo.lt_iff_lt.symm

/-- In a homogeneous polynomial submodule, every leading term of the
specified degree has an actual witness in that degree piece. -/
theorem polynomialModuleLeadingTerms_weightedPiece
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hN : IsWeightedPolynomialModuleHomogeneous weight shift N) (degree : ℤ) :
    polynomialModuleLeadingTerms m
        (N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) =
      monomialUpperFamilyTerms (polynomialModuleLeadingUpperFamily m N) ∩
        shiftedModuleDegreeTerms weight shift degree := by
  ext t
  constructor
  · rintro ⟨P, ⟨hPN, hPdegree⟩, hP⟩
    refine ⟨?_, ?_⟩
    · exact (mem_polynomialModuleLeadingUpperFamily m N t.1 t.2).mpr ⟨P, hPN, hP⟩
    · exact (mem_weightedPolynomialModulePiece_iff weight shift degree P).mp hPdegree
        t.1 t.2 hP.1
  · rintro ⟨hfamily, hdegree⟩
    obtain ⟨P, hPN, hP⟩ := (mem_polynomialModuleLeadingUpperFamily m N t.1 t.2).mp hfamily
    obtain ⟨Q, hQN, hQdegree, hQ⟩ :=
      exists_homogeneous_polynomialModuleLeadingTerm m weight shift N hN hPN hP
    have hgrade : shiftedModuleMonomialDegree weight shift t = degree := hdegree
    rw [hgrade] at hQdegree
    exact ⟨Q, ⟨hQN, hQdegree⟩, hQ⟩

/-- The Hilbert function of an actual homogeneous submodule equals the
actual shifted weighted monomial counts of its full leading upper-family. -/
theorem finrank_polynomialModule_weightedPiece_eq_leadingCount
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hN : IsWeightedPolynomialModuleHomogeneous weight shift N) (degree : ℤ) :
    Module.finrank K
        ((N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) :
          Submodule K (Fin r → MvPolynomial (Fin n) K)) =
      monomialUpperFamilyWeightedDegreeCount weight shift
        (polynomialModuleLeadingUpperFamily m N) degree := by
  change Module.finrank K
      ((N.restrictScalars K ⊓
        polynomialModuleSupported (shiftedModuleDegreeTerms weight shift degree)) :
          Submodule K (Fin r → MvPolynomial (Fin n) K)) = _
  rw [finrank_polynomialModule_eq_leadingTerms m
    (shiftedModuleDegreeTerms_finite weight hweight shift degree) _ inf_le_right]
  have hlead := polynomialModuleLeadingTerms_weightedPiece m weight shift N hN degree
  change polynomialModuleLeadingTerms m
      (N.restrictScalars K ⊓
        polynomialModuleSupported (shiftedModuleDegreeTerms weight shift degree)) = _ at hlead
  rw [hlead]
  rfl

/-- Taking the full actual monomial leading submodule preserves every
shifted weighted homogeneous-piece dimension. -/
theorem finrank_polynomialModule_weightedPiece_eq_initial
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hN : IsWeightedPolynomialModuleHomogeneous weight shift N) (degree : ℤ) :
    Module.finrank K
        ((N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) :
          Submodule K (Fin r → MvPolynomial (Fin n) K)) =
      Module.finrank K
        (((monomialUpperFamilySubmodule (polynomialModuleLeadingUpperFamily m N)).restrictScalars K ⊓
          weightedPolynomialModulePiece weight shift degree) :
            Submodule K (Fin r → MvPolynomial (Fin n) K)) := by
  rw [finrank_polynomialModule_weightedPiece_eq_leadingCount m weight hweight shift N hN degree,
    finrank_monomialUpperFamily_weightedPiece_eq_count _ weight hweight shift degree]

end AbelFormalization
