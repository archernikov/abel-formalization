import AbelFormalization.LocalArtinianFiniteDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Degree slices of induced Artinian layers

This file supplies the one grading bridge left explicit in
`LocalArtinianFiniteDescent`.  In one filtration layer, inclusion of the
degree part into the full numerator descends to the quotient.  Projection
back to the chosen weighted degree is its inverse on the range of the
induced component.  Taking the finite product gives the canonical linear
equivalence required by `ArtinianInducedLayerDegreeIdentification`.

No equality of the dimensions of the individual ideal-power layers is used.
-/

noncomputable section

namespace AbelFormalization

section OneLayer

variable {B : Type*} [CommRing B] {n r : ℕ}

/-! ## Inclusion of one degree numerator -/

/-- Include the degree-filtered numerator into the full induced numerator
of the same ideal-power layer. -/
def artinianPolynomialInducedDegreeNumeratorInclusion
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) :
    artinianPolynomialInducedDegreeFiltration
        I N weight shift degree i →+
      ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i) :
        Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r)) where
  toFun x := ⟨
    ((x : artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r),
    ⟨x.property.1, x.property.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem artinianPolynomialInducedDegreeNumeratorInclusion_coe
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ)
    (x : artinianPolynomialInducedDegreeFiltration
      I N weight shift degree i) :
    ((artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i x :
      ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i) :
        Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r))) :
      artinianFreePolynomialModule B n r) =
    ((x : artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) := rfl

/-- Inclusion respects the two quotient relations. -/
theorem artinianPolynomialInducedDegreeNumeratorInclusion_quotientRel
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ)
    {x y : artinianPolynomialInducedDegreeFiltration
      I N weight shift degree i}
    (hxy :
      ((artinianPolynomialInducedDegreeFiltration
          I N weight shift degree (i + 1)).comap
        (artinianPolynomialInducedDegreeFiltration
          I N weight shift degree i).subtype).quotientRel x y) :
    ((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)).comap
      (N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype).quotientRel
      (artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i x)
      (artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i y) := by
  rw [Submodule.quotientRel_def] at hxy ⊢
  change
    (((x - y : artinianPolynomialInducedDegreeFiltration
          I N weight shift degree i) :
        artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) ∈
        N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1) at hxy
  change
    (((artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i x -
        artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i y :
        ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
            (n := n) (r := r) I i) :
          Submodule (MvPolynomial (Fin n) B)
            (artinianFreePolynomialModule B n r)))) :
      artinianFreePolynomialModule B n r) ∈
        N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)
  exact hxy

/-- Inclusion of degree numerators descended to one actual quotient layer,
as an additive map. -/
def artinianPolynomialInducedDegreeLayerToInducedLayerAdd
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) :
    artinianPolynomialInducedDegreeLayer
        I N weight shift degree i →+
      artinianPolynomialInducedLayer (n := n) (r := r) I N i where
  toFun := Quotient.map'
    (artinianPolynomialInducedDegreeNumeratorInclusion
      I N weight shift degree i)
    (fun _ _ hxy =>
      artinianPolynomialInducedDegreeNumeratorInclusion_quotientRel
        I N weight shift degree i hxy)
  map_zero' := by
    change Submodule.Quotient.mk
        (artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i 0) =
      Submodule.Quotient.mk 0
    rw [map_zero]
  map_add' := by
    intro x y
    refine Submodule.Quotient.induction_on _ x ?_
    intro P
    refine Submodule.Quotient.induction_on _ y ?_
    intro Q
    change Submodule.Quotient.mk
        (artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i (P + Q)) =
      Submodule.Quotient.mk
          (artinianPolynomialInducedDegreeNumeratorInclusion
            I N weight shift degree i P) +
        Submodule.Quotient.mk
          (artinianPolynomialInducedDegreeNumeratorInclusion
            I N weight shift degree i Q)
    rw [map_add, Submodule.Quotient.mk_add]

@[simp]
theorem artinianPolynomialInducedDegreeLayerToInducedLayerAdd_mk
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ)
    (x : artinianPolynomialInducedDegreeFiltration
      I N weight shift degree i) :
    artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i x) := rfl

/-! ## Projection of a full numerator into one degree -/

/-- Project a full induced numerator to the selected degree and record it
inside the corresponding degree-filtered numerator. -/
def artinianPolynomialInducedNumeratorDegreeProjection
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ) :
    ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i) :
      Submodule (MvPolynomial (Fin n) B)
        (artinianFreePolynomialModule B n r)) →+
      artinianPolynomialInducedDegreeFiltration
        I N weight shift degree i where
  toFun P := by
    let p : artinianFreePolynomialModule B n r :=
      (P : artinianFreePolynomialModule B n r)
    exact
      ⟨⟨artinianPolynomialModuleComponent
            (B := B) weight shift degree p,
          artinianPolynomialModuleComponent_mem_piece
            (B := B) weight shift degree p⟩,
        ⟨hN p P.property.1 degree,
          artinianPolynomialModuleComponent_mem_idealPower
            (B := B) (n := n) (r := r) I i weight shift degree
              P.property.2⟩⟩
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    exact (artinianPolynomialModuleComponent
      (B := B) weight shift degree).map_zero
  map_add' P Q := by
    apply Subtype.ext
    apply Subtype.ext
    exact (artinianPolynomialModuleComponent
      (B := B) weight shift degree).map_add P Q

@[simp]
theorem artinianPolynomialInducedNumeratorDegreeProjection_coe
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ)
    (P : ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
        (n := n) (r := r) I i) :
      Submodule (MvPolynomial (Fin n) B)
        (artinianFreePolynomialModule B n r))) :
    (((artinianPolynomialInducedNumeratorDegreeProjection
          I N hN degree i P :
        artinianPolynomialInducedDegreeFiltration
          I N weight shift degree i) :
      artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) =
    artinianPolynomialModuleComponent weight shift degree P := rfl

/-- Degree projection respects the successive induced quotient relations. -/
theorem artinianPolynomialInducedNumeratorDegreeProjection_quotientRel
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ)
    {P Q : ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
        (n := n) (r := r) I i) :
      Submodule (MvPolynomial (Fin n) B)
        (artinianFreePolynomialModule B n r))}
    (hPQ :
      ((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)).comap
        (N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype).quotientRel P Q) :
    ((artinianPolynomialInducedDegreeFiltration
          I N weight shift degree (i + 1)).comap
      (artinianPolynomialInducedDegreeFiltration
          I N weight shift degree i).subtype).quotientRel
      (artinianPolynomialInducedNumeratorDegreeProjection
        I N hN degree i P)
      (artinianPolynomialInducedNumeratorDegreeProjection
        I N hN degree i Q) := by
  rw [Submodule.quotientRel_def] at hPQ ⊢
  change ((P : artinianFreePolynomialModule B n r) - Q) ∈
    N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I (i + 1) at hPQ
  refine ⟨?_, ?_⟩
  · change artinianPolynomialModuleComponent weight shift degree P -
      artinianPolynomialModuleComponent weight shift degree Q ∈ N
    rw [← map_sub]
    exact hN _ hPQ.1 degree
  · change artinianPolynomialModuleComponent weight shift degree P -
      artinianPolynomialModuleComponent weight shift degree Q ∈
        artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)
    rw [← map_sub]
    exact artinianPolynomialModuleComponent_mem_idealPower
      (n := n) (r := r) I (i + 1) weight shift degree hPQ.2

/-- Degree projection descended from a full induced quotient layer to its
actual degree-filtered quotient. -/
def artinianPolynomialInducedLayerToDegreeLayerAdd
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ) :
    artinianPolynomialInducedLayer (n := n) (r := r) I N i →+
      artinianPolynomialInducedDegreeLayer
        I N weight shift degree i where
  toFun := Quotient.map'
    (artinianPolynomialInducedNumeratorDegreeProjection
      I N hN degree i)
    (fun _ _ hPQ =>
      artinianPolynomialInducedNumeratorDegreeProjection_quotientRel
        I N hN degree i hPQ)
  map_zero' := by
    change Submodule.Quotient.mk
        (artinianPolynomialInducedNumeratorDegreeProjection
          I N hN degree i 0) =
      Submodule.Quotient.mk 0
    rw [map_zero]
  map_add' := by
    intro x y
    refine Submodule.Quotient.induction_on _ x ?_
    intro P
    refine Submodule.Quotient.induction_on _ y ?_
    intro Q
    change Submodule.Quotient.mk
        (artinianPolynomialInducedNumeratorDegreeProjection
          I N hN degree i (P + Q)) =
      Submodule.Quotient.mk
          (artinianPolynomialInducedNumeratorDegreeProjection
            I N hN degree i P) +
        Submodule.Quotient.mk
          (artinianPolynomialInducedNumeratorDegreeProjection
            I N hN degree i Q)
    rw [map_add, Submodule.Quotient.mk_add]

@[simp]
theorem artinianPolynomialInducedLayerToDegreeLayerAdd_mk
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ)
    (P : ↥((N ⊓ artinianPolynomialIdealPowerSubmodule
        (n := n) (r := r) I i) :
      Submodule (MvPolynomial (Fin n) B)
        (artinianFreePolynomialModule B n r))) :
    artinianPolynomialInducedLayerToDegreeLayerAdd I N hN degree i
        (Submodule.Quotient.mk P) =
      Submodule.Quotient.mk
        (artinianPolynomialInducedNumeratorDegreeProjection
          I N hN degree i P) := rfl

/-! ## The two quotient maps are inverse on the component range -/

/-- Projecting after including an actual degree quotient is the identity. -/
theorem artinianPolynomialInducedLayerToDegreeLayerAdd_comp_inclusion
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ)
    (x : artinianPolynomialInducedDegreeLayer
      I N weight shift degree i) :
    artinianPolynomialInducedLayerToDegreeLayerAdd I N hN degree i
        (artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i x) = x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro P
  change Submodule.Quotient.mk
      (artinianPolynomialInducedNumeratorDegreeProjection
        I N hN degree i
        (artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i P)) =
    Submodule.Quotient.mk P
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  apply Subtype.ext
  exact artinianPolynomialModuleComponent_eq_self
    weight shift degree P.val.property

/-- Including after projecting a full quotient is its induced weighted
component. -/
theorem artinianPolynomialInducedDegreeLayerToInducedLayerAdd_comp_projection
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (i : ℕ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i
        (artinianPolynomialInducedLayerToDegreeLayerAdd
          I N hN degree i x) =
      artinianPolynomialInducedLayerComponent I N hN i degree x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro P
  change Submodule.Quotient.mk
      (artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i
        (artinianPolynomialInducedNumeratorDegreeProjection
          I N hN degree i P)) =
    Submodule.Quotient.mk
      (artinianPolynomialInducedNumeratorComponent
        I N hN i degree P)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rfl

end OneLayer

/-! ## Residue linearity -/

section ResidueLinearity

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- On one induced layer, a residue polynomial represented by an original
polynomial acts as that original polynomial. -/
theorem artinianPolynomialInducedLayer_residue_smul_eq_original
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (i : ℕ) (a : MvPolynomial (Fin n) B)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    letI := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i
    artinianPolynomialResidueMap (n := n) I a • x = a • x := by
  let _ := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i
  exact submoduleLayerPushforward_smul_eq_original
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I)
    (N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i)
    (N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I (i + 1))
    (artinianPolynomialInducedLayer_annihilation
      (n := n) (r := r) I N i) a x

/-- Restrict the residue-polynomial action on one induced layer along the
constant-polynomial map. -/
@[instance_reducible]
def artinianPolynomialInducedLayerResidueModule
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (i : ℕ) :
    letI := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i
    Module (B ⧸ I)
      (artinianPolynomialInducedLayer (n := n) (r := r) I N i) := by
  let _ := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i
  exact Module.compHom
    (artinianPolynomialInducedLayer (n := n) (r := r) I N i)
    (MvPolynomial.C : (B ⧸ I) →+*
      MvPolynomial (Fin n) (B ⧸ I))

/-- Inclusion of a degree numerator commutes with original coefficient
scalars, viewed as constant-polynomial scalars on the full numerator. -/
theorem artinianPolynomialInducedDegreeNumeratorInclusion_smul_original
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) (b : B)
    (x : artinianPolynomialInducedDegreeFiltration
      I N weight shift degree i) :
    artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i (b • x) =
      (MvPolynomial.C b : MvPolynomial (Fin n) B) •
        artinianPolynomialInducedDegreeNumeratorInclusion
          I N weight shift degree i x := by
  apply Subtype.ext
  change
    b • (((x : artinianPolynomialModulePiece
        (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r)) =
      (MvPolynomial.C b : MvPolynomial (Fin n) B) •
        (((x : artinianPolynomialModulePiece
            (B := B) weight shift degree) :
          artinianFreePolynomialModule B n r))
  simpa only [MvPolynomial.C_eq_algebraMap, algebraMap_smul]

/-- The descended inclusion commutes with original coefficient scalars. -/
theorem artinianPolynomialInducedDegreeLayerToInducedLayerAdd_smul_original
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) (b : B)
    (x : artinianPolynomialInducedDegreeLayer
      I N weight shift degree i) :
    artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i (b • x) =
      (MvPolynomial.C b : MvPolynomial (Fin n) B) •
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro P
  change Submodule.Quotient.mk
      (artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i (b • P)) =
    (MvPolynomial.C b : MvPolynomial (Fin n) B) • Submodule.Quotient.mk
      (artinianPolynomialInducedDegreeNumeratorInclusion
        I N weight shift degree i P)
  rw [artinianPolynomialInducedDegreeNumeratorInclusion_smul_original,
    Submodule.Quotient.mk_smul]

/-- The descended degree inclusion is linear over the residue coefficient
ring. -/
theorem artinianPolynomialInducedDegreeLayerToInducedLayerAdd_smul_residue
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) (c : B ⧸ I)
    (x : artinianPolynomialInducedDegreeLayer
      I N weight shift degree i) :
    letI := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i
    letI := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i
    letI := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i
    artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i (c • x) =
      c • artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i x := by
  let _ := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i
  let _ := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i
  let _ := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) c
  let A := artinianPolynomialInducedDegreeFiltration
    I N weight shift degree i
  let A' := artinianPolynomialInducedDegreeFiltration
    I N weight shift degree (i + 1)
  let hAA' : I • A ≤ A' :=
    artinianPolynomialInducedDegreeFiltration_smul_le
      I N weight shift degree i
  have hsource : Module.IsTorsionBySet B
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i) I :=
    submoduleLayer_isTorsionBySet I A A' hAA'
  have hC :
      artinianPolynomialResidueMap (n := n) I (MvPolynomial.C b) =
        MvPolynomial.C (Ideal.Quotient.mk I b) := by
    simp [artinianPolynomialResidueMap]
  change
    artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i
        (Ideal.Quotient.mk I b • x) =
      (MvPolynomial.C (Ideal.Quotient.mk I b) :
        MvPolynomial (Fin n) (B ⧸ I)) •
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i x
  calc
    artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i
        (Ideal.Quotient.mk I b • x) =
      artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i (b • x) := by
          rw [Module.IsTorsionBySet.mk_smul hsource]
    _ = (MvPolynomial.C b : MvPolynomial (Fin n) B) •
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i x :=
      artinianPolynomialInducedDegreeLayerToInducedLayerAdd_smul_original
        I N weight shift degree i b x
    _ = artinianPolynomialResidueMap (n := n) I (MvPolynomial.C b) •
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i x :=
      (artinianPolynomialInducedLayer_residue_smul_eq_original
        (n := n) (r := r) I N i (MvPolynomial.C b)
          (artinianPolynomialInducedDegreeLayerToInducedLayerAdd
            I N weight shift degree i x)).symm
    _ = (MvPolynomial.C (Ideal.Quotient.mk I b) : MvPolynomial (Fin n) (B ⧸ I)) •
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i x := by rw [hC]

/-- The degree inclusion into one induced layer, bundled as a residue-ring
linear map. -/
def artinianPolynomialInducedDegreeLayerToInducedLayerLinear
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) :
    letI := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i
    letI := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i
    letI := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i
    artinianPolynomialInducedDegreeLayer I N weight shift degree i
      →ₗ[B ⧸ I]
        artinianPolynomialInducedLayer (n := n) (r := r) I N i := by
  let _ := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i
  let _ := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i
  let _ := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i
  exact
    { toFun := artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i
      map_add' := (artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i).map_add
      map_smul' :=
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd_smul_residue
          I N weight shift degree i }

@[simp]
theorem artinianPolynomialInducedDegreeLayerToInducedLayerLinear_apply
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ)
    (x : artinianPolynomialInducedDegreeLayer
      I N weight shift degree i) :
    letI := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i
    letI := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i
    letI := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i
    artinianPolynomialInducedDegreeLayerToInducedLayerLinear
        I N weight shift degree i x =
      artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i x := rfl

end ResidueLinearity

/-! ## The finite product and its component range -/

section FiniteProduct

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- Include each actual degree quotient in the corresponding full induced
layer. -/
def artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (e : ℕ) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedDegreeLayerSum
        I N weight shift degree e →ₗ[B ⧸ I]
      artinianPolynomialInducedLayerSum (n := n) (r := r) I N e := by
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  exact
    { toFun := fun x i =>
        artinianPolynomialInducedDegreeLayerToInducedLayerAdd
          I N weight shift degree i.1 (x i)
      map_add' := by
        intro x y
        funext i
        exact map_add
          (artinianPolynomialInducedDegreeLayerToInducedLayerAdd
            I N weight shift degree i.1) (x i) (y i)
      map_smul' := by
        intro c x
        funext i
        exact artinianPolynomialInducedDegreeLayerToInducedLayerAdd_smul_residue
          I N weight shift degree i.1 c (x i) }

@[simp]
theorem artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear_apply
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (e : ℕ)
    (x : artinianPolynomialInducedDegreeLayerSum
      I N weight shift degree e) (i : Fin e) :
    letI (j : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree j.1) := inferInstance
    letI (j : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree j.1
    letI (j : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N j.1
    letI (j : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N j.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
        I N weight shift degree e x i =
      artinianPolynomialInducedDegreeLayerToInducedLayerAdd
        I N weight shift degree i.1 (x i) := rfl

/-- Extract the selected degree from every full induced layer. -/
def artinianPolynomialInducedLayerSumToDegreeLayerSum
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ) :
    artinianPolynomialInducedLayerSum (n := n) (r := r) I N e →
      artinianPolynomialInducedDegreeLayerSum
        I N weight shift degree e :=
  fun x i => artinianPolynomialInducedLayerToDegreeLayerAdd
    I N hN degree i.1 (x i)

@[simp]
theorem artinianPolynomialInducedLayerSumToDegreeLayerSum_apply
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e)
    (i : Fin e) :
    artinianPolynomialInducedLayerSumToDegreeLayerSum
        I N hN degree e x i =
      artinianPolynomialInducedLayerToDegreeLayerAdd
        I N hN degree i.1 (x i) := rfl

/-- Extraction is a left inverse to simultaneous inclusion. -/
theorem artinianPolynomialInducedLayerSumToDegreeLayerSum_comp_inclusion
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ)
    (x : artinianPolynomialInducedDegreeLayerSum
      I N weight shift degree e) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedLayerSumToDegreeLayerSum I N hN degree e
        (artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
          I N weight shift degree e x) = x := by
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  funext i
  exact artinianPolynomialInducedLayerToDegreeLayerAdd_comp_inclusion
    I N hN degree i.1 (x i)

/-- Including the extracted tuple is exactly the pointwise component of the
original tuple. -/
theorem artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear_comp_projection
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
        I N weight shift degree e
        (artinianPolynomialInducedLayerSumToDegreeLayerSum
          I N hN degree e x) =
      artinianPolynomialInducedLayerSumComponent I N hN e degree x := by
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  funext i
  exact artinianPolynomialInducedDegreeLayerToInducedLayerAdd_comp_projection
    I N hN degree i.1 (x i)

section ComponentRange

variable [IsNoetherianRing B]

/-- Simultaneous degree inclusion lands in the range of the pointwise
component projection. -/
theorem artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear_mem_componentRange
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ)
    (x : artinianPolynomialInducedDegreeLayerSum
      I N weight shift degree e) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialAmbientLayerModule
      (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
        I N weight shift degree e x ∈
      LinearMap.range
        (artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree) := by
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialAmbientLayerModule
    (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  refine ⟨
    artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
      I N weight shift degree e x, ?_⟩
  rw [artinianPolynomialInducedLayerSumComponentLinear_apply]
  rw [← artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear_comp_projection
    I N hN degree e]
  rw [artinianPolynomialInducedLayerSumToDegreeLayerSum_comp_inclusion
    I N hN degree e]

/-- The canonical linear map from the product of actual degree quotients to
the component range. -/
def artinianPolynomialInducedDegreeLayerSumToComponentRangeLinear
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialAmbientLayerModule
      (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedDegreeLayerSum
        I N weight shift degree e →ₗ[B ⧸ I]
      LinearMap.range
        (artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree) := by
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialAmbientLayerModule
    (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  exact LinearMap.codRestrict
    (LinearMap.range
      (artinianPolynomialInducedLayerSumComponentLinear
        I N hN e degree))
    (artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
      I N weight shift degree e)
    (artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear_mem_componentRange
      I N hN degree e)

@[simp]
theorem artinianPolynomialInducedDegreeLayerSumToComponentRangeLinear_coe
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ)
    (x : artinianPolynomialInducedDegreeLayerSum
      I N weight shift degree e) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialAmbientLayerModule
      (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    ((artinianPolynomialInducedDegreeLayerSumToComponentRangeLinear
        I N hN degree e x :
      LinearMap.range
        (artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree)) :
      artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) =
    artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
      I N weight shift degree e x := rfl

/-- Canonical per-degree equivalence between the product of the actual
filtration quotients and the range of the induced-layer component. -/
noncomputable def artinianPolynomialInducedDegreeLayerSumEquivComponentRange
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (degree : ℤ) (e : ℕ) :
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialInducedLayerResidueModule
      (n := n) (r := r) I N i.1
    letI (i : Fin e) := artinianPolynomialAmbientLayerModule
      (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    artinianPolynomialInducedDegreeLayerSum I N weight shift degree e
      ≃ₗ[B ⧸ I]
        LinearMap.range
          (artinianPolynomialInducedLayerSumComponentLinear
            I N hN e degree) := by
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialAmbientLayerModule
    (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let f := artinianPolynomialInducedDegreeLayerSumToComponentRangeLinear
    I N hN degree e
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' :
        artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
            I N weight shift degree e x =
          artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
            I N weight shift degree e y :=
      congrArg Subtype.val hxy
    calc
      x = artinianPolynomialInducedLayerSumToDegreeLayerSum I N hN degree e
          (artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
            I N weight shift degree e x) :=
        (artinianPolynomialInducedLayerSumToDegreeLayerSum_comp_inclusion
          I N hN degree e x).symm
      _ = artinianPolynomialInducedLayerSumToDegreeLayerSum I N hN degree e
          (artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
            I N weight shift degree e y) := congrArg
        (artinianPolynomialInducedLayerSumToDegreeLayerSum
          I N hN degree e) hxy'
      _ = y :=
        artinianPolynomialInducedLayerSumToDegreeLayerSum_comp_inclusion
          I N hN degree e y
  · intro y
    refine ⟨artinianPolynomialInducedLayerSumToDegreeLayerSum
      I N hN degree e y.1, ?_⟩
    apply Subtype.ext
    change
      artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
          I N weight shift degree e
          (artinianPolynomialInducedLayerSumToDegreeLayerSum
            I N hN degree e y.1) = y.1
    calc
      artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear
          I N weight shift degree e
          (artinianPolynomialInducedLayerSumToDegreeLayerSum
            I N hN degree e y.1) =
        artinianPolynomialInducedLayerSumComponent I N hN e degree y.1 :=
          artinianPolynomialInducedDegreeLayerSumToInducedLayerSumLinear_comp_projection
            I N hN degree e y.1
      _ = artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree y.1 := rfl
      _ = y.1 :=
        (mem_range_artinianPolynomialInducedLayerSumComponentLinear_iff
          I N hN e degree y.1).mp y.2

end ComponentRange

end FiniteProduct

/-! ## Discharge of the isolated interface -/

section Identification

variable {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]

/-- Every degree slice of the finite induced-layer sum is canonically the
range of the corresponding component projection. -/
theorem artinianPolynomialInducedLayerDegreeIdentification
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) :
    ArtinianInducedLayerDegreeIdentification I N hN e := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) := artinianPolynomialInducedLayerModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialInducedLayerResidueModule
    (n := n) (r := r) I N i.1
  let _ (i : Fin e) := artinianPolynomialAmbientLayerModule
    (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  intro degree
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i.1
  exact ⟨artinianPolynomialInducedDegreeLayerSumEquivComponentRange
    I N hN degree e⟩

end Identification

end AbelFormalization
