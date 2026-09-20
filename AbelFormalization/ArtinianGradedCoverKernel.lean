import AbelFormalization.ArtinianGradedLayerCover

set_option autoImplicit false

/-!
# Homogeneous kernels of the graded Artinian layer cover

The constant generators in `ArtinianGradedLayerCover` carry the shifts of
their original free coordinates.  Consequently, the explicit finite free
cover intertwines the shifted weighted coefficient projections on its source
with the pointwise projections on the ambient layer sum.

The source component is only linear over the residue coefficient ring, and
the target component is only additive.  The cover itself remains linear over
the residue polynomial ring.  No section of the coefficient quotient map is
chosen: a preimage is used only locally to prove the scalar-generator
identity.
-/

noncomputable section

namespace AbelFormalization

/-! ## Components of coordinate vectors -/

/-- A weighted component of a single free coordinate is still supported in
that coordinate.  Recording the surviving coefficient by evaluation avoids
introducing a second scalar-polynomial component operator. -/
theorem artinianPolynomialModuleComponent_single
    {C : Type*} [CommRing C] {n m : ℕ}
    (weight : Fin n → ℕ) (coordinateShift : Fin m → ℤ)
    (degree : ℤ) (j : Fin m) (p : MvPolynomial (Fin n) C) :
    artinianPolynomialModuleComponent weight coordinateShift degree
        (Pi.single j p) =
      Pi.single j
        (artinianPolynomialModuleComponent weight coordinateShift degree
          (Pi.single j p) j) := by
  classical
  funext k
  by_cases hkj : k = j
  · subst k
    simp only [Pi.single_eq_same]
  · apply MvPolynomial.ext
    intro d
    simp [artinianPolynomialModuleComponent_coeff, Pi.single_apply, hkj]

/-- Multiplying a distinguished constant numerator by a scalar polynomial
translates scalar degree into module degree by the shift of its coordinate.
The scalar component is expressed as the corresponding coordinate of a
single-coordinate module component, which works over every commutative
coefficient ring. -/
theorem artinianPolynomialModuleComponent_smul_constantGenerator
    {B : Type*} [CommRing B] {n r m : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (coordinateShift : Fin m → ℤ) (j : Fin m)
    (k : Fin r) (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank)
    (hshift : coordinateShift j = shift k)
    (a : MvPolynomial (Fin n) B) :
    artinianPolynomialModuleComponent weight shift degree
        (a • artinianPolynomialIdealPowerConstantGenerator
          (n := n) (r := r) I i k s) =
      (artinianPolynomialModuleComponent weight coordinateShift degree
          (Pi.single j a) j) •
        artinianPolynomialIdealPowerConstantGenerator
          (n := n) (r := r) I i k s := by
  classical
  funext l
  apply MvPolynomial.ext
  intro d
  by_cases hlk : l = k
  · subst l
    rw [artinianPolynomialModuleComponent_coeff]
    simp only [Pi.smul_apply,
      artinianPolynomialIdealPowerConstantGenerator, Pi.single_eq_same,
      smul_eq_mul]
    rw [mul_comm a (MvPolynomial.C
        ((artinianIdealPowerCoverGenerator I i s :
          {x : B // x ∈ I ^ i}) : B)),
      MvPolynomial.coeff_C_mul]
    rw [mul_comm
        (artinianPolynomialModuleComponent weight coordinateShift degree
          (Pi.single j a) j)
        (MvPolynomial.C
          ((artinianIdealPowerCoverGenerator I i s :
            {x : B // x ∈ I ^ i}) : B)),
      MvPolynomial.coeff_C_mul,
      artinianPolynomialModuleComponent_coeff]
    simp only [Pi.single_eq_same, artinianPolynomialTermDegree]
    rw [hshift]
    by_cases hd : (Finsupp.weight weight d : ℤ) + shift k = degree
    · simp [hd]
    · simp [hd]
  · simp [artinianPolynomialModuleComponent_coeff,
      artinianPolynomialIdealPowerConstantGenerator, Pi.single_apply, hlk]

/-- Coefficientwise residue reduction commutes with the selected coordinate
of the component of a single-coordinate vector. -/
theorem artinianPolynomialModuleComponent_residue_single_apply
    {B : Type*} [CommRing B] {n m : ℕ}
    (I : Ideal B) (weight : Fin n → ℕ)
    (coordinateShift : Fin m → ℤ) (degree : ℤ)
    (j : Fin m) (a : MvPolynomial (Fin n) B) :
    artinianPolynomialResidueMap (n := n) I
        (artinianPolynomialModuleComponent weight coordinateShift degree
          (Pi.single j a) j) =
      artinianPolynomialModuleComponent (B := B ⧸ I)
          weight coordinateShift degree
          (Pi.single j (artinianPolynomialResidueMap (n := n) I a)) j := by
  classical
  have hmap :
      (fun k : Fin m => artinianPolynomialResidueMap (n := n) I
        ((Pi.single j a : Fin m → MvPolynomial (Fin n) B) k)) =
        (Pi.single j (artinianPolynomialResidueMap (n := n) I a) :
          Fin m → MvPolynomial (Fin n) (B ⧸ I)) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp only [Pi.single_eq_same]
    · simp [Pi.single_apply, hkj]
  have hresidue := artinianPolynomialModuleComponent_residue
    (B := B) (n := n) (r := m) I weight coordinateShift degree
      (Pi.single j a)
  rw [hmap] at hresidue
  exact congrFun hresidue j

/-! ## Comparison with the field polynomial-module component -/

/-- Over a field, the arbitrary-coefficient component used for Artinian
layers is the earlier field polynomial-module component.  Both are defined
from the actual coefficient array; this theorem supplies the explicit bridge
needed by the field uniform-generator theorem. -/
theorem artinianPolynomialModuleComponent_eq_weightedPolynomialModuleComponent
    {K : Type*} [Field K] {n m : ℕ}
    (weight : Fin n → ℕ) (coordinateShift : Fin m → ℤ) (degree : ℤ) :
    artinianPolynomialModuleComponent (B := K)
        weight coordinateShift degree =
      weightedPolynomialModuleComponent (K := K)
        weight coordinateShift degree := by
  apply LinearMap.ext
  intro P
  funext k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleComponent_coeff,
    weightedPolynomialModuleComponent_coeff]
  rfl

/-- Thus the two closure predicates agree over a field. -/
theorem isArtinianPolynomialSubmoduleHomogeneous_iff_isWeightedPolynomialModuleHomogeneous
    {K : Type*} [Field K] {n m : ℕ}
    (weight : Fin n → ℕ) (coordinateShift : Fin m → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K)
      (Fin m → MvPolynomial (Fin n) K)) :
    IsArtinianPolynomialSubmoduleHomogeneous weight coordinateShift N ↔
      IsWeightedPolynomialModuleHomogeneous weight coordinateShift N := by
  rw [IsArtinianPolynomialSubmoduleHomogeneous,
    IsWeightedPolynomialModuleHomogeneous]
  simp only
    [artinianPolynomialModuleComponent_eq_weightedPolynomialModuleComponent]

/-- Every coefficient-filter component is idempotent. -/
theorem artinianPolynomialModuleComponent_idempotent
    {C : Type*} [CommRing C] {n m : ℕ}
    (weight : Fin n → ℕ) (coordinateShift : Fin m → ℤ)
    (degree : ℤ) (P : Fin m → MvPolynomial (Fin n) C) :
    artinianPolynomialModuleComponent weight coordinateShift degree
        (artinianPolynomialModuleComponent weight coordinateShift degree P) =
      artinianPolynomialModuleComponent weight coordinateShift degree P := by
  exact artinianPolynomialModuleComponent_eq_self
    (B := C) weight coordinateShift degree
      (artinianPolynomialModuleComponent_mem_piece
        (B := C) weight coordinateShift degree P)

/-- Coefficient scalar multiplication on a free polynomial module is the
same as multiplication by the corresponding constant polynomial. -/
theorem mvPolynomialPi_C_smul_eq
    {C : Type*} [CommRing C] {n m : ℕ}
    (c : C) (P : Fin m → MvPolynomial (Fin n) C) :
    (MvPolynomial.C c : MvPolynomial (Fin n) C) • P = c • P := by
  funext j
  change MvPolynomial.C c * P j = c • P j
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-! ## A scalar polynomial times one distinguished quotient generator -/

/-- The component of a scalar multiple of one constant quotient generator is
the scalar component dictated by that generator's shift, times the same
generator.  Surjectivity of the residue map is used locally in the proof; no
section is retained in the construction. -/
theorem artinianPolynomialAmbientLayerComponent_smul_constantGenerator
    {B : Type*} [CommRing B] {n r m : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (coordinateShift : Fin m → ℤ) (j : Fin m)
    (k : Fin r) (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank)
    (hshift : coordinateShift j = shift k)
    (p : MvPolynomial (Fin n) (B ⧸ I)) :
    letI := artinianPolynomialAmbientLayerModule
      (n := n) (r := r) I i
    artinianPolynomialAmbientLayerComponent I i weight shift degree
        (p • artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s) =
      (artinianPolynomialModuleComponent (B := B ⧸ I)
          weight coordinateShift degree (Pi.single j p) j) •
        artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s := by
  classical
  let _ := artinianPolynomialAmbientLayerModule
    (n := n) (r := r) I i
  obtain ⟨a, rfl⟩ := artinianPolynomialResidueMap_surjective
    (n := n) I p
  let b : MvPolynomial (Fin n) B :=
    artinianPolynomialModuleComponent weight coordinateShift degree
      (Pi.single j a) j
  let P : artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i :=
    ⟨artinianPolynomialIdealPowerConstantGenerator
        (n := n) (r := r) I i k s,
      artinianPolynomialIdealPowerConstantGenerator_mem
        (n := n) (r := r) I i k s⟩
  have hgenerator :
      artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s =
        Submodule.Quotient.mk P := rfl
  have hb :
      artinianPolynomialResidueMap (n := n) I b =
        artinianPolynomialModuleComponent (B := B ⧸ I)
          weight coordinateShift degree
          (Pi.single j (artinianPolynomialResidueMap (n := n) I a)) j := by
    exact artinianPolynomialModuleComponent_residue_single_apply
      (n := n) (m := m) I weight coordinateShift degree j a
  have hnumerator :
      artinianPolynomialModuleComponent weight shift degree
          (a • artinianPolynomialIdealPowerConstantGenerator
            (n := n) (r := r) I i k s) =
        b • artinianPolynomialIdealPowerConstantGenerator
          (n := n) (r := r) I i k s := by
    exact artinianPolynomialModuleComponent_smul_constantGenerator
      (n := n) (r := r) I i weight shift degree coordinateShift j k s
        hshift a
  calc
    artinianPolynomialAmbientLayerComponent I i weight shift degree
        (artinianPolynomialResidueMap (n := n) I a •
          artinianPolynomialAmbientLayerConstantGenerator
            (n := n) (r := r) I i k s) =
      artinianPolynomialAmbientLayerComponent I i weight shift degree
        (a • artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s) := by
        exact congrArg
          (artinianPolynomialAmbientLayerComponent
            I i weight shift degree)
          (artinianPolynomialAmbientLayer_residue_smul_eq_original
            (n := n) (r := r) I i a
              (artinianPolynomialAmbientLayerConstantGenerator
                (n := n) (r := r) I i k s))
    _ = Submodule.Quotient.mk
        (artinianPolynomialIdealPowerComponent
          I i weight shift degree (a • P)) := by
      rw [hgenerator, ← Submodule.Quotient.mk_smul,
        artinianPolynomialAmbientLayerComponent_mk]
    _ = Submodule.Quotient.mk (b • P) := by
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      change artinianPolynomialModuleComponent weight shift degree
          (a • artinianPolynomialIdealPowerConstantGenerator
            (n := n) (r := r) I i k s) =
        b • artinianPolynomialIdealPowerConstantGenerator
          (n := n) (r := r) I i k s
      exact hnumerator
    _ = b • artinianPolynomialAmbientLayerConstantGenerator
        (n := n) (r := r) I i k s := by
      rw [hgenerator, Submodule.Quotient.mk_smul]
    _ = artinianPolynomialResidueMap (n := n) I b •
        artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s := by
      exact (artinianPolynomialAmbientLayer_residue_smul_eq_original
        (n := n) (r := r) I i b
          (artinianPolynomialAmbientLayerConstantGenerator
            (n := n) (r := r) I i k s)).symm
    _ = (artinianPolynomialModuleComponent (B := B ⧸ I)
          weight coordinateShift degree
          (Pi.single j (artinianPolynomialResidueMap (n := n) I a)) j) •
        artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s := by
      rw [hb]

/-! ## Intertwining the graded finite free cover -/

/-- Pointwise projection of a scalar multiple of one distinguished graded
generator retains precisely the matching scalar component. -/
theorem artinianPolynomialAmbientLayerSumComponent_smul_gradedGenerator
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (j : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r))
    (p : MvPolynomial (Fin n) (B ⧸ I)) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (p • artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) (r := r) I e j) =
      (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree (Pi.single j p) j) •
        artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) (r := r) I e j := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let g : artinianPolynomialAmbientLayerRawGeneratorIndex I e r :=
    (artinianPolynomialAmbientLayerRawGeneratorEquivFin I e r).symm j
  funext i
  by_cases hi : i = g.1
  · subst i
    simpa only [artinianPolynomialAmbientLayerSumComponent_apply,
      Pi.smul_apply, artinianPolynomialAmbientLayerSumGradedGenerator,
      artinianPolynomialAmbientLayerSumRawGenerator, g, Pi.single_eq_same]
      using
        (artinianPolynomialAmbientLayerComponent_smul_constantGenerator
          (n := n) (r := r) I g.1.1 weight shift degree
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          j g.2.1 g.2.2 (by rfl) p)
  · simp [artinianPolynomialAmbientLayerSumComponent_apply,
      artinianPolynomialAmbientLayerSumGradedGenerator,
      artinianPolynomialAmbientLayerSumRawGenerator, g,
      Pi.single_apply, hi]

/-- The graded cover intertwines source and target components on a single
free coordinate. -/
theorem artinianPolynomialAmbientLayerSumGradedCover_component_single
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (j : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r))
    (p : MvPolynomial (Fin n) (B ⧸ I)) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e (Pi.single j p)) =
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree (Pi.single j p)) := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let D := artinianPolynomialModuleComponent (B := B ⧸ I) weight
    (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift) degree
  have hsingle : D (Pi.single j p) =
      Pi.single j (D (Pi.single j p) j) :=
    artinianPolynomialModuleComponent_single
      (C := B ⧸ I) weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      degree j p
  calc
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e (Pi.single j p)) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (p • artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) (r := r) I e j) := by
      rw [artinianPolynomialAmbientLayerSumGradedCover,
        Fintype.linearCombination_apply_single]
    _ = D (Pi.single j p) j •
        artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) (r := r) I e j := by
      exact artinianPolynomialAmbientLayerSumComponent_smul_gradedGenerator
        (n := n) (r := r) I e weight shift degree j p
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
          (Pi.single j (D (Pi.single j p) j)) := by
      rw [artinianPolynomialAmbientLayerSumGradedCover,
        Fintype.linearCombination_apply_single]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e (D (Pi.single j p)) := by
      rw [← hsingle]

/-- The explicit finite free cover commutes with every shifted weighted
component.  This is the component identity needed to pull stable target
submodules back to ordinary homogeneous submodules of a fixed free module. -/
theorem artinianPolynomialAmbientLayerSumGradedCover_component
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
      MvPolynomial (Fin n) (B ⧸ I)) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e x) =
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x) := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  calc
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e x) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e
            (∑ j, Pi.single j (x j))) := by
      rw [Finset.univ_sum_single]
    _ = ∑ j,
        artinianPolynomialAmbientLayerSumComponent I e weight shift degree
          (artinianPolynomialAmbientLayerSumGradedCover
            (n := n) (r := r) I e (Pi.single j (x j))) := by
      simp only [map_sum]
    _ = ∑ j,
        artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e
          (artinianPolynomialModuleComponent (B := B ⧸ I) weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree (Pi.single j (x j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact artinianPolynomialAmbientLayerSumGradedCover_component_single
        (n := n) (r := r) I e weight shift degree j (x j)
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree (∑ j, Pi.single j (x j))) := by
      simp only [map_sum]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x) := by
      rw [Finset.univ_sum_single]

/-! ## Residue-coefficient-linear component maps -/

/-- Restrict the residue-polynomial action on the ambient layer sum along
the constant-polynomial map. -/
def artinianPolynomialAmbientLayerSumResidueModule
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Module (B ⧸ I)
      (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact Module.compHom
    (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e)
    (MvPolynomial.C : (B ⧸ I) →+*
      MvPolynomial (Fin n) (B ⧸ I))

/-- The pointwise ambient layer-sum component commutes with residue-field
scalar multiplication. -/
theorem artinianPolynomialAmbientLayerSumComponent_smul_residue
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (c : B ⧸ I)
    (x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (c • x) =
      c • artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree x := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  obtain ⟨v, rfl⟩ :=
    artinianPolynomialAmbientLayerSumGradedCover_surjective
      (n := n) (r := r) I e x
  calc
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (c • artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e v) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) •
          artinianPolynomialAmbientLayerSumGradedCover
            (n := n) (r := r) I e v) := by
      rfl
    _ = artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e
          ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • v)) := by
      rw [(artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e).map_smul]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree
          ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • v)) := by
      exact artinianPolynomialAmbientLayerSumGradedCover_component
        (n := n) (r := r) I e weight shift degree _
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree (c • v)) := by
      rw [mvPolynomialPi_C_smul_eq]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (c • artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree v) := by
      rw [(artinianPolynomialModuleComponent (B := B ⧸ I) weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree).map_smul]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) •
          artinianPolynomialModuleComponent (B := B ⧸ I) weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree v) := by
      rw [mvPolynomialPi_C_smul_eq]
    _ = (MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) •
        artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e
          (artinianPolynomialModuleComponent (B := B ⧸ I) weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree v) := by
      rw [(artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e).map_smul]
    _ = c • artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree v) := by
      rfl
    _ = c • artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e v) := by
      rw [artinianPolynomialAmbientLayerSumGradedCover_component]

/-- The pointwise ambient component bundled as a residue-coefficient-linear
map. -/
def artinianPolynomialAmbientLayerSumComponentLinear
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSum (n := n) (r := r) I e →ₗ[B ⧸ I]
      artinianPolynomialAmbientLayerSum (n := n) (r := r) I e := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  exact
    { toFun := artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree
      map_add' := (artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree).map_add
      map_smul' := artinianPolynomialAmbientLayerSumComponent_smul_residue
        (n := n) (r := r) I e weight shift degree }

@[simp]
theorem artinianPolynomialAmbientLayerSumComponentLinear_apply
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSumComponentLinear
        I e weight shift degree x =
      artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree x := rfl

/-- Pointwise ambient projection is idempotent. -/
theorem artinianPolynomialAmbientLayerSumComponent_idempotent
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumComponent
          I e weight shift degree x) =
      artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree x := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  obtain ⟨v, rfl⟩ :=
    artinianPolynomialAmbientLayerSumGradedCover_surjective
      (n := n) (r := r) I e x
  calc
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumComponent I e weight shift degree
          (artinianPolynomialAmbientLayerSumGradedCover
            (n := n) (r := r) I e v)) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e
          (artinianPolynomialModuleComponent (B := B ⧸ I) weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree v)) := by
      rw [artinianPolynomialAmbientLayerSumGradedCover_component]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree
          (artinianPolynomialModuleComponent (B := B ⧸ I) weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree v)) := by
      rw [artinianPolynomialAmbientLayerSumGradedCover_component]
    _ = artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree v) := by
      rw [artinianPolynomialModuleComponent_idempotent]
    _ = artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e v) := by
      rw [artinianPolynomialAmbientLayerSumGradedCover_component]

@[simp]
theorem artinianPolynomialAmbientLayerSumComponentLinear_idempotent
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSumComponentLinear I e weight shift degree
        (artinianPolynomialAmbientLayerSumComponentLinear
          I e weight shift degree x) =
      artinianPolynomialAmbientLayerSumComponentLinear
        I e weight shift degree x := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  exact artinianPolynomialAmbientLayerSumComponent_idempotent
    (n := n) (r := r) I e weight shift degree x

/-- The range of the ambient component projection is its fixed-point
subspace. -/
theorem mem_range_artinianPolynomialAmbientLayerSumComponentLinear_iff
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    x ∈ LinearMap.range
        (artinianPolynomialAmbientLayerSumComponentLinear
          I e weight shift degree) ↔
      artinianPolynomialAmbientLayerSumComponentLinear
        I e weight shift degree x = x := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  constructor
  · rintro ⟨y, rfl⟩
    exact artinianPolynomialAmbientLayerSumComponentLinear_idempotent
      (n := n) (r := r) I e weight shift degree y
  · intro hx
    exact ⟨x, hx⟩

/-! ### Induced layer sums -/

/-- Restrict the residue-polynomial action on an induced layer sum along
constant polynomials. -/
def artinianPolynomialInducedLayerSumResidueModule
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    Module (B ⧸ I)
      (artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  exact Module.compHom
    (artinianPolynomialInducedLayerSum (n := n) (r := r) I N e)
    (MvPolynomial.C : (B ⧸ I) →+*
      MvPolynomial (Fin n) (B ⧸ I))

/-- The pointwise induced component is residue-coefficient-linear. -/
theorem artinianPolynomialInducedLayerSumComponent_smul_residue
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ) (c : B ⧸ I)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialInducedLayerSumComponent I N hN e degree (c • x) =
      c • artinianPolynomialInducedLayerSumComponent I N hN e degree x := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  let f := artinianPolynomialInducedLayerSumMap
    (n := n) (r := r) I N e
  have hf_smul (y : artinianPolynomialInducedLayerSum
      (n := n) (r := r) I N e) : f (c • y) = c • f y := by
    change f ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • y) =
      (MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • f y
    exact f.map_smul _ _
  apply artinianPolynomialInducedLayerSumMap_injective
    (n := n) (r := r) I N e
  calc
    f (artinianPolynomialInducedLayerSumComponent I N hN e degree
        (c • x)) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (f (c • x)) := by
      exact artinianPolynomialInducedLayerSumMap_component
        (n := n) (r := r) I N hN e degree (c • x)
    _ = artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (c • f x) := by
      rw [hf_smul]
    _ = c • artinianPolynomialAmbientLayerSumComponent
        I e weight shift degree (f x) := by
      exact artinianPolynomialAmbientLayerSumComponent_smul_residue
        (n := n) (r := r) I e weight shift degree c (f x)
    _ = c • f
        (artinianPolynomialInducedLayerSumComponent
          I N hN e degree x) := by
      rw [artinianPolynomialInducedLayerSumMap_component
        (n := n) (r := r) I N hN e degree x]
    _ = f (c • artinianPolynomialInducedLayerSumComponent
        I N hN e degree x) := by
      rw [hf_smul]

/-- The induced layer-sum component bundled as a residue-coefficient-linear
map. -/
def artinianPolynomialInducedLayerSumComponentLinear
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedLayerSum (n := n) (r := r) I N e →ₗ[B ⧸ I]
      artinianPolynomialInducedLayerSum (n := n) (r := r) I N e := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  exact
    { toFun := artinianPolynomialInducedLayerSumComponent
        I N hN e degree
      map_add' := (artinianPolynomialInducedLayerSumComponent
        I N hN e degree).map_add
      map_smul' := artinianPolynomialInducedLayerSumComponent_smul_residue
        (n := n) (r := r) I N hN e degree }

@[simp]
theorem artinianPolynomialInducedLayerSumComponentLinear_apply
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedLayerSumComponentLinear I N hN e degree x =
      artinianPolynomialInducedLayerSumComponent
        I N hN e degree x := rfl

/-- Pointwise induced projection is idempotent. -/
theorem artinianPolynomialInducedLayerSumComponent_idempotent
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialInducedLayerSumComponent I N hN e degree
        (artinianPolynomialInducedLayerSumComponent
          I N hN e degree x) =
      artinianPolynomialInducedLayerSumComponent
        I N hN e degree x := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let f := artinianPolynomialInducedLayerSumMap
    (n := n) (r := r) I N e
  apply artinianPolynomialInducedLayerSumMap_injective
    (n := n) (r := r) I N e
  calc
    f (artinianPolynomialInducedLayerSumComponent I N hN e degree
        (artinianPolynomialInducedLayerSumComponent
          I N hN e degree x)) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (f (artinianPolynomialInducedLayerSumComponent
          I N hN e degree x)) := by
      exact artinianPolynomialInducedLayerSumMap_component
        (n := n) (r := r) I N hN e degree _
    _ = artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialAmbientLayerSumComponent I e weight shift degree
          (f x)) := by
      rw [artinianPolynomialInducedLayerSumMap_component
        (n := n) (r := r) I N hN e degree x]
    _ = artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (f x) := by
      exact artinianPolynomialAmbientLayerSumComponent_idempotent
        (n := n) (r := r) I e weight shift degree (f x)
    _ = f (artinianPolynomialInducedLayerSumComponent
        I N hN e degree x) := by
      rw [artinianPolynomialInducedLayerSumMap_component
        (n := n) (r := r) I N hN e degree x]

@[simp]
theorem artinianPolynomialInducedLayerSumComponentLinear_idempotent
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedLayerSumComponentLinear I N hN e degree
        (artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree x) =
      artinianPolynomialInducedLayerSumComponentLinear
        I N hN e degree x := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  exact artinianPolynomialInducedLayerSumComponent_idempotent
    (n := n) (r := r) I N hN e degree x

/-- The range of the induced component projection is its fixed-point
subspace. -/
theorem mem_range_artinianPolynomialInducedLayerSumComponentLinear_iff
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    x ∈ LinearMap.range
        (artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree) ↔
      artinianPolynomialInducedLayerSumComponentLinear
        I N hN e degree x = x := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  constructor
  · rintro ⟨y, rfl⟩
    exact artinianPolynomialInducedLayerSumComponentLinear_idempotent
      (n := n) (r := r) I N hN e degree y
  · intro hx
    exact ⟨x, hx⟩

/-! ## Stable preimages and the homogeneous kernel -/

/-- Any subset of the target stable under the pointwise target component has
a preimage stable under the corresponding source component.  This set-level
form applies directly both to kernels and to ranges of induced-layer maps. -/
theorem artinianPolynomialAmbientLayerSumGradedCover_component_mem_preimage
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (S : Set (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e))
    (hS : ∀ y ∈ S,
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree y ∈ S)
    {x : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
      MvPolynomial (Fin n) (B ⧸ I)}
    (hx :
      letI (i : Fin e) :=
        artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x ∈ S) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x) ∈ S := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  rw [← artinianPolynomialAmbientLayerSumGradedCover_component
    (n := n) (r := r) I e weight shift degree x]
  exact hS _ hx

/-- Kernel of the explicit graded finite free cover. -/
def artinianPolynomialAmbientLayerSumGradedCoverKernel
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule (MvPolynomial (Fin n) (B ⧸ I))
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)) := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact LinearMap.ker
    (artinianPolynomialAmbientLayerSumGradedCover
      (n := n) (r := r) I e)

@[simp]
theorem mem_artinianPolynomialAmbientLayerSumGradedCoverKernel_iff
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (x : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
      MvPolynomial (Fin n) (B ⧸ I)) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    x ∈ artinianPolynomialAmbientLayerSumGradedCoverKernel
        (n := n) (r := r) I e ↔
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x = 0 := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact LinearMap.mem_ker

/-- The kernel of the graded cover is an actual weighted homogeneous
polynomial submodule with the inherited generator shifts. -/
theorem artinianPolynomialAmbientLayerSumGradedCoverKernel_homogeneous
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    IsArtinianPolynomialSubmoduleHomogeneous (B := B ⧸ I) weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialAmbientLayerSumGradedCoverKernel
        (n := n) (r := r) I e) := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  intro x hx degree
  rw [mem_artinianPolynomialAmbientLayerSumGradedCoverKernel_iff] at hx ⊢
  have hcomponent := artinianPolynomialAmbientLayerSumGradedCover_component
    (n := n) (r := r) I e weight shift degree x
  rw [hx, map_zero] at hcomponent
  exact hcomponent.symm

/-- In the maximal-ideal case, kernel homogeneity is stated in the field API
expected by the uniform polynomial-module generator theorem. -/
theorem artinianPolynomialAmbientLayerSumGradedCoverKernel_weightedHomogeneous
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal] (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    IsWeightedPolynomialModuleHomogeneous weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialAmbientLayerSumGradedCoverKernel
        (n := n) (r := r) I e) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact
    (isArtinianPolynomialSubmoduleHomogeneous_iff_isWeightedPolynomialModuleHomogeneous
      weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialAmbientLayerSumGradedCoverKernel
        (n := n) (r := r) I e)).mp
      (artinianPolynomialAmbientLayerSumGradedCoverKernel_homogeneous
        (n := n) (r := r) I e weight shift)

/-! ## Pullback of an induced layer sum -/

/-- Pull the range of the induced-layer embedding back through the fixed
graded finite free cover.  This is the free polynomial submodule to which the
field uniform-generator theorem will later be applied. -/
def artinianPolynomialInducedLayerSumGradedPullback
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule (MvPolynomial (Fin n) (B ⧸ I))
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact (LinearMap.range
    (artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e)).comap
      (artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e)

@[simp]
theorem mem_artinianPolynomialInducedLayerSumGradedPullback_iff
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ)
    (x : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
      MvPolynomial (Fin n) (B ⧸ I)) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    x ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e ↔
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x ∈
        LinearMap.range
          (artinianPolynomialInducedLayerSumMap
            (n := n) (r := r) I N e) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  rfl

/-- The pullback of the induced-layer range is homogeneous whenever the
original polynomial submodule is homogeneous. -/
theorem artinianPolynomialInducedLayerSumGradedPullback_homogeneous
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    IsArtinianPolynomialSubmoduleHomogeneous (B := B ⧸ I) weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  intro x hx degree
  rw [mem_artinianPolynomialInducedLayerSumGradedPullback_iff] at hx ⊢
  rw [← artinianPolynomialAmbientLayerSumGradedCover_component
    (n := n) (r := r) I e weight shift degree x]
  exact artinianPolynomialAmbientLayerSumComponent_mem_range
    (n := n) (r := r) I N hN e degree hx

/-- In the maximal-ideal case, pullback homogeneity is stated in the field
polynomial-module API. -/
theorem artinianPolynomialInducedLayerSumGradedPullback_weightedHomogeneous
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    IsWeightedPolynomialModuleHomogeneous weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact
    (isArtinianPolynomialSubmoduleHomogeneous_iff_isWeightedPolynomialModuleHomogeneous
      weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)).mp
      (artinianPolynomialInducedLayerSumGradedPullback_homogeneous
        (n := n) (r := r) I N hN e)

/-- Every relation of the graded cover lies in the pullback of each induced
layer range. -/
theorem artinianPolynomialAmbientLayerSumGradedCoverKernel_le_pullback
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumGradedCoverKernel
        (n := n) (r := r) I e ≤
      artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  intro x hx
  rw [mem_artinianPolynomialAmbientLayerSumGradedCoverKernel_iff] at hx
  rw [mem_artinianPolynomialInducedLayerSumGradedPullback_iff, hx]
  exact Submodule.zero_mem _

end AbelFormalization
