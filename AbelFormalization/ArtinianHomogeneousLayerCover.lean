import AbelFormalization.ArtinianAmbientLayerFinite
import AbelFormalization.PolynomialModuleHomogeneous

set_option autoImplicit false

/-!
# Homogeneous constant covers of Artinian polynomial layers

This scratch module constructs the coordinate and grading data needed to
replace an arbitrary finite-module cover of an Artinian ambient layer by a
cover whose distinguished vectors are constant and weighted homogeneous.

The construction uses finite generators of each coefficient ideal power.  It
does not choose a section of the residue map.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

/-! ## Coordinatewise ideal action on a finite free module -/

/-- Multiplying the full finite function module by an ideal is exactly the
submodule of functions whose coordinates lie in that ideal. -/
theorem ideal_smul_top_eq_pi
    {A κ : Type*} [CommRing A] [Fintype κ] (J : Ideal A) :
    J • (⊤ : Submodule A (κ → A)) =
      Submodule.pi Set.univ (fun _ : κ => (J : Submodule A A)) := by
  classical
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha x hx
    rw [Submodule.mem_pi]
    intro k hk
    change a * x k ∈ J
    exact J.mul_mem_right (x k) ha
  · intro x hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro k hk
    have hxk : x k ∈ J := (Submodule.mem_pi.mp hx) k (Set.mem_univ k)
    have hsingle :
        x k • Pi.single k (1 : A) ∈ J • (⊤ : Submodule A (κ → A)) :=
      Submodule.smul_mem_smul hxk (Submodule.mem_top)
    simpa only [← Pi.single_smul', smul_eq_mul, mul_one] using hsingle

section PolynomialCoordinates

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- The ideal-power filtration of the free polynomial module is the
coordinatewise ideal-power filtration. -/
theorem artinianPolynomialIdealPowerSubmodule_eq_pi (I : Ideal B) (i : ℕ) :
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i =
      Submodule.pi Set.univ (fun _ : Fin r =>
        (artinianPolynomialCoefficientIdeal (n := n) I ^ i :
          Submodule (MvPolynomial (Fin n) B) (MvPolynomial (Fin n) B))) := by
  exact ideal_smul_top_eq_pi
    (artinianPolynomialCoefficientIdeal (n := n) I ^ i)

/-- Membership in the polynomial ideal-power filtration is coefficientwise
membership in the corresponding coefficient ideal power. -/
theorem mem_artinianPolynomialIdealPowerSubmodule_iff_coeff
    (I : Ideal B) (i : ℕ)
    (P : artinianFreePolynomialModule B n r) :
    P ∈ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i ↔
      ∀ k d, (P k).coeff d ∈ I ^ i := by
  rw [artinianPolynomialIdealPowerSubmodule_eq_pi]
  constructor
  · intro hP k d
    have hk := (Submodule.mem_pi.mp hP) k (Set.mem_univ k)
    change P k ∈ artinianPolynomialCoefficientIdeal (n := n) I ^ i at hk
    rw [artinianPolynomialCoefficientIdeal, ← Ideal.map_pow] at hk
    exact (MvPolynomial.mem_map_C_iff.mp hk) d
  · intro hP
    rw [Submodule.mem_pi]
    intro k hk
    change P k ∈ artinianPolynomialCoefficientIdeal (n := n) I ^ i
    rw [artinianPolynomialCoefficientIdeal, ← Ideal.map_pow]
    exact MvPolynomial.mem_map_C_iff.mpr (hP k)

/-! ## Weighted coefficient projections over the Artinian ring -/

/-- The shifted weighted coefficient projection over an arbitrary
commutative coefficient ring. -/
def artinianPolynomialModuleComponent
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianFreePolynomialModule B n r →ₗ[B]
      artinianFreePolynomialModule B n r := by
  classical
  exact
    { toFun := fun P => artinianPolynomialModuleCoeffEquiv.symm
        ((artinianPolynomialModuleCoeffEquiv P).filter
          (fun t => artinianPolynomialTermDegree weight shift t = degree))
      map_add' := by
        intro P Q
        simp only [map_add, Finsupp.filter_add]
      map_smul' := by
        intro c P
        simp only [map_smul, Finsupp.filter_smul, RingHom.id_apply] }

@[simp]
theorem artinianPolynomialModuleComponent_coeff
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (P : artinianFreePolynomialModule B n r)
    (k : Fin r) (d : Fin n →₀ ℕ) :
    (artinianPolynomialModuleComponent weight shift degree P k).coeff d =
      if artinianPolynomialTermDegree weight shift (k, d) = degree
      then (P k).coeff d else 0 := by
  classical
  change artinianPolynomialModuleCoeffEquiv
      (artinianPolynomialModuleComponent weight shift degree P) (k, d) = _
  change artinianPolynomialModuleCoeffEquiv
      (artinianPolynomialModuleCoeffEquiv.symm
        ((artinianPolynomialModuleCoeffEquiv P).filter
          (fun t => artinianPolynomialTermDegree weight shift t = degree)))
        (k, d) = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.filter_apply]
  rfl

/-- A weighted component has support only in its selected shifted degree. -/
theorem artinianPolynomialModuleComponent_mem_piece
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (P : artinianFreePolynomialModule B n r) :
    artinianPolynomialModuleComponent weight shift degree P ∈
      artinianPolynomialModulePiece (B := B) weight shift degree := by
  classical
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  change artinianPolynomialTermDegree weight shift (k, d) = degree
  by_contra hdegree
  exact hcoeff (by
    rw [artinianPolynomialModuleComponent_coeff, ite_eq_right hdegree])

/-- Projecting a vector already supported in one shifted degree fixes it. -/
theorem artinianPolynomialModuleComponent_eq_self
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    {P : artinianFreePolynomialModule B n r}
    (hP : P ∈ artinianPolynomialModulePiece (B := B) weight shift degree) :
    artinianPolynomialModuleComponent weight shift degree P = P := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleComponent_coeff]
  by_cases hd : artinianPolynomialTermDegree weight shift (k, d) = degree
  · exact ite_eq_left hd
  · rw [ite_eq_right hd]
    by_contra hcoeff
    exact hd ((mem_artinianPolynomialModuleSupported _ _).mp hP k d
      (Ne.symm hcoeff))

/-- Coefficient-ideal powers are stable under every weighted component
projection.  No positivity hypothesis on the weights is needed. -/
theorem artinianPolynomialModuleComponent_mem_idealPower
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    {P : artinianFreePolynomialModule B n r}
    (hP : P ∈ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) :
    artinianPolynomialModuleComponent weight shift degree P ∈
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i := by
  apply (mem_artinianPolynomialIdealPowerSubmodule_iff_coeff I i _).mpr
  intro k d
  rw [artinianPolynomialModuleComponent_coeff]
  split_ifs
  · exact (mem_artinianPolynomialIdealPowerSubmodule_iff_coeff I i P).mp hP k d
  · exact (I ^ i).zero_mem

/-- Coefficientwise residue reduction commutes with the shifted weighted
component projection. -/
theorem artinianPolynomialModuleComponent_residue
    (I : Ideal B)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (P : artinianFreePolynomialModule B n r) :
    (fun k => artinianPolynomialResidueMap (n := n) I
      (artinianPolynomialModuleComponent weight shift degree P k)) =
      artinianPolynomialModuleComponent (B := B ⧸ I) weight shift degree
        (fun k => artinianPolynomialResidueMap (n := n) I (P k)) := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  change
    (MvPolynomial.map (Ideal.Quotient.mk I)
      (artinianPolynomialModuleComponent weight shift degree P k)).coeff d =
    (artinianPolynomialModuleComponent (B := B ⧸ I) weight shift degree
      (fun l => MvPolynomial.map (Ideal.Quotient.mk I) (P l)) k).coeff d
  rw [MvPolynomial.coeff_map,
    artinianPolynomialModuleComponent_coeff,
    artinianPolynomialModuleComponent_coeff,
    MvPolynomial.coeff_map]
  split_ifs <;> simp

/-! ## Finite constant families -/

/-- A fixed finite free B-cover of one coefficient ideal power. -/
def artinianIdealPowerFiniteFreeCover [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) : FiniteFreeCover B {x : B // x ∈ I ^ i} := by
  let _ : Module.Finite B {x : B // x ∈ I ^ i} := inferInstance
  exact FiniteFreeCover.ofModuleFinite B {x : B // x ∈ I ^ i}

/-- The distinguished coefficient generators obtained by applying the cover
to the standard coordinate vectors. -/
def artinianIdealPowerCoverGenerator [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ)
    (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
      {x : B // x ∈ I ^ i} :=
  (artinianIdealPowerFiniteFreeCover I i).map (Pi.single s 1)

/-- The distinguished coefficient generators span the entire ideal-power
subtype over B. -/
theorem artinianIdealPowerCoverGenerator_span_eq_top [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) :
    Submodule.span B
      (Set.range (artinianIdealPowerCoverGenerator I i)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨c, hc⟩ := (artinianIdealPowerFiniteFreeCover I i).surjective x
  rw [← hc, ← Finset.univ_sum_single c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsingle :
      Pi.single s (c s) = c s • Pi.single s (1 : B) := by
    rw [← Pi.single_smul']
    simp only [smul_eq_mul, mul_one]
  rw [hsingle, map_smul]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self s))

/-- Insert one coefficient-ideal generator as a constant polynomial in one
original free coordinate. -/
def artinianPolynomialIdealPowerConstantGenerator [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (k : Fin r)
    (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    artinianFreePolynomialModule B n r :=
  Pi.single k (MvPolynomial.C
    ((artinianIdealPowerCoverGenerator I i s : {x : B // x ∈ I ^ i}) : B))

/-- Every distinguished constant vector lies in the required polynomial
ideal-power numerator. -/
theorem artinianPolynomialIdealPowerConstantGenerator_mem
    [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (k : Fin r)
    (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    artinianPolynomialIdealPowerConstantGenerator (n := n) (r := r) I i k s ∈
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i := by
  classical
  apply (mem_artinianPolynomialIdealPowerSubmodule_iff_coeff I i _).mpr
  intro l d
  by_cases hl : l = k
  · subst l
    by_cases hd : d = 0
    · subst d
      simpa [artinianPolynomialIdealPowerConstantGenerator] using
        (artinianIdealPowerCoverGenerator I i s).property
    · simpa [artinianPolynomialIdealPowerConstantGenerator, Ne.symm hd] using
        (I ^ i).zero_mem
  · simpa [artinianPolynomialIdealPowerConstantGenerator, Pi.single_apply, hl] using
      (I ^ i).zero_mem

/-- Every distinguished constant vector is homogeneous of the original
component shift.  The ideal-layer index and coefficient-generator index add
no degree shift. -/
theorem artinianPolynomialIdealPowerConstantGenerator_mem_piece
    [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (k : Fin r) (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    artinianPolynomialIdealPowerConstantGenerator (n := n) (r := r) I i k s ∈
      artinianPolynomialModulePiece (B := B) weight shift (shift k) := by
  classical
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro l d hcoeff
  have hl : l = k := by
    by_contra hl
    simpa [artinianPolynomialIdealPowerConstantGenerator, Pi.single_apply, hl] using hcoeff
  subst l
  have hd : d = 0 := by
    by_contra hd
    simpa [artinianPolynomialIdealPowerConstantGenerator, Ne.symm hd] using hcoeff
  subst d
  simp [artinianPolynomialDegreeTerms, artinianPolynomialTermDegree]

/-- The quotient class of a distinguished constant generator in one fixed
ambient layer. -/
def artinianPolynomialAmbientLayerConstantGenerator [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (k : Fin r)
    (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    artinianPolynomialAmbientLayer (n := n) (r := r) I i :=
  Submodule.Quotient.mk
    (⟨artinianPolynomialIdealPowerConstantGenerator
        (n := n) (r := r) I i k s,
      artinianPolynomialIdealPowerConstantGenerator_mem
        (n := n) (r := r) I i k s⟩ :
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)

/-- Homogeneity of a quotient-layer element, expressed without pretending
that a degree projection is linear over the whole residue polynomial ring. -/
def IsArtinianPolynomialAmbientLayerHomogeneous
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : artinianPolynomialAmbientLayer (n := n) (r := r) I i) : Prop :=
  ∃ P : artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i,
    (P : artinianFreePolynomialModule B n r) ∈
      artinianPolynomialModulePiece (B := B) weight shift degree ∧
    Submodule.Quotient.mk P = x

/-- The constant quotient generators are homogeneous of precisely the
original free-coordinate shift. -/
theorem artinianPolynomialAmbientLayerConstantGenerator_homogeneous
    [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (k : Fin r) (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    IsArtinianPolynomialAmbientLayerHomogeneous
      (n := n) (r := r) I i weight shift (shift k)
      (artinianPolynomialAmbientLayerConstantGenerator
        (n := n) (r := r) I i k s) := by
  refine ⟨⟨artinianPolynomialIdealPowerConstantGenerator
      (n := n) (r := r) I i k s,
    artinianPolynomialIdealPowerConstantGenerator_mem
      (n := n) (r := r) I i k s⟩, ?_, rfl⟩
  exact artinianPolynomialIdealPowerConstantGenerator_mem_piece
    (n := n) (r := r) I i weight shift k s

/-- Projection to the generator's shifted degree fixes its chosen numerator
representative. -/
theorem artinianPolynomialModuleComponent_constantGenerator
    [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (k : Fin r) (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    artinianPolynomialModuleComponent weight shift (shift k)
        (artinianPolynomialIdealPowerConstantGenerator
          (n := n) (r := r) I i k s) =
      artinianPolynomialIdealPowerConstantGenerator
        (n := n) (r := r) I i k s :=
  artinianPolynomialModuleComponent_eq_self
    (B := B) (n := n) (r := r) weight shift (shift k)
    (artinianPolynomialIdealPowerConstantGenerator_mem_piece
      (n := n) (r := r) I i weight shift k s)

end PolynomialCoordinates

end AbelFormalization
