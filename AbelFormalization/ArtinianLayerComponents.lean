import AbelFormalization.ArtinianHomogeneousLayerCover

set_option autoImplicit false

/-!
# Weighted components on Artinian polynomial layers

Weighted coefficient projection is linear over the coefficient ring, but it
is not linear over the polynomial ring.  Accordingly, this file descends the
projection through the actual submodule quotients as an additive homomorphism
using `Quotient.map'`.  No coefficient-field section is chosen.
-/

noncomputable section

namespace AbelFormalization

section PolynomialLayerComponents

variable {B : Type*} [CommRing B] {n r : ℕ}

/-! ## Components on one ambient layer -/

/-- Weighted projection restricted to one numerator of the coefficient-ideal
filtration.  It is recorded as an additive homomorphism because that is the
structure needed for the quotient construction. -/
def artinianPolynomialIdealPowerComponent
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i →+
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i where
  toFun P := ⟨artinianPolynomialModuleComponent weight shift degree P,
    artinianPolynomialModuleComponent_mem_idealPower
      (n := n) (r := r) I i weight shift degree P.property⟩
  map_zero' := by
    apply Subtype.ext
    exact (artinianPolynomialModuleComponent
      (B := B) weight shift degree).map_zero
  map_add' P Q := by
    apply Subtype.ext
    exact (artinianPolynomialModuleComponent
      (B := B) weight shift degree).map_add P Q

@[simp]
theorem artinianPolynomialIdealPowerComponent_coe
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (P : artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) :
    ((artinianPolynomialIdealPowerComponent I i weight shift degree P :
        artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) :
      artinianFreePolynomialModule B n r) =
        artinianPolynomialModuleComponent weight shift degree P :=
  rfl

/-- Compatibility of weighted projection with the quotient relation between
two consecutive coefficient-ideal powers. -/
theorem artinianPolynomialIdealPowerComponent_quotientRel
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    {P Q : artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i}
    (hPQ :
      ((artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1)).comap
          (artinianPolynomialIdealPowerSubmodule
            (n := n) (r := r) I i).subtype).quotientRel P Q) :
    ((artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1)).comap
        (artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype).quotientRel
      (artinianPolynomialIdealPowerComponent I i weight shift degree P)
      (artinianPolynomialIdealPowerComponent I i weight shift degree Q) := by
  rw [Submodule.quotientRel_def] at hPQ ⊢
  change ((P : artinianFreePolynomialModule B n r) - Q) ∈
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1) at hPQ
  change
    artinianPolynomialModuleComponent weight shift degree P -
        artinianPolynomialModuleComponent weight shift degree Q ∈
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1)
  rw [← map_sub]
  exact artinianPolynomialModuleComponent_mem_idealPower
    (n := n) (r := r) I (i + 1) weight shift degree hPQ

/-- The weighted component on an actual ambient quotient layer.  This is an
additive map, rather than a residue-polynomial-linear map. -/
def artinianPolynomialAmbientLayerComponent
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianPolynomialAmbientLayer (n := n) (r := r) I i →+
      artinianPolynomialAmbientLayer (n := n) (r := r) I i where
  toFun := Quotient.map'
    (artinianPolynomialIdealPowerComponent I i weight shift degree)
    (fun _ _ hPQ => artinianPolynomialIdealPowerComponent_quotientRel
      I i weight shift degree hPQ)
  map_zero' := by
    change Submodule.Quotient.mk
        (artinianPolynomialIdealPowerComponent I i weight shift degree 0) =
      Submodule.Quotient.mk 0
    rw [map_zero]
  map_add' := by
    intro x y
    refine Submodule.Quotient.induction_on _ x ?_
    intro P
    refine Submodule.Quotient.induction_on _ y ?_
    intro Q
    change Submodule.Quotient.mk
        (artinianPolynomialIdealPowerComponent I i weight shift degree (P + Q)) =
      Submodule.Quotient.mk
          (artinianPolynomialIdealPowerComponent I i weight shift degree P) +
        Submodule.Quotient.mk
          (artinianPolynomialIdealPowerComponent I i weight shift degree Q)
    rw [map_add, Submodule.Quotient.mk_add]

@[simp]
theorem artinianPolynomialAmbientLayerComponent_mk
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (P : artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) :
    artinianPolynomialAmbientLayerComponent I i weight shift degree
        (Submodule.Quotient.mk P) =
      Submodule.Quotient.mk
        (artinianPolynomialIdealPowerComponent I i weight shift degree P) :=
  rfl

@[simp]
theorem artinianPolynomialAmbientLayerComponent_zero
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianPolynomialAmbientLayerComponent I i weight shift degree 0 = 0 :=
  map_zero _

@[simp]
theorem artinianPolynomialAmbientLayerComponent_add
    (I : Ideal B) (i : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x y : artinianPolynomialAmbientLayer (n := n) (r := r) I i) :
    artinianPolynomialAmbientLayerComponent I i weight shift degree (x + y) =
      artinianPolynomialAmbientLayerComponent I i weight shift degree x +
        artinianPolynomialAmbientLayerComponent I i weight shift degree y :=
  map_add _ _ _

/-! ## Homogeneous polynomial submodules and induced layers -/

/-- A polynomial submodule is weighted homogeneous when it is closed under
every actual shifted weighted coefficient projection. -/
def IsArtinianPolynomialSubmoduleHomogeneous
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) : Prop :=
  ∀ P ∈ N, ∀ degree : ℤ,
    artinianPolynomialModuleComponent weight shift degree P ∈ N

/-- Weighted projection restricted to the numerator of an induced layer of
a homogeneous polynomial submodule. -/
def artinianPolynomialInducedNumeratorComponent
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ) :
    ↥(N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) →+
      ↥(N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) where
  toFun P := ⟨artinianPolynomialModuleComponent weight shift degree P,
    ⟨hN P P.property.1 degree,
      artinianPolynomialModuleComponent_mem_idealPower
        (n := n) (r := r) I i weight shift degree P.property.2⟩⟩
  map_zero' := by
    apply Subtype.ext
    exact (artinianPolynomialModuleComponent
      (B := B) weight shift degree).map_zero
  map_add' P Q := by
    apply Subtype.ext
    exact (artinianPolynomialModuleComponent
      (B := B) weight shift degree).map_add P Q

@[simp]
theorem artinianPolynomialInducedNumeratorComponent_coe
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    (P : ↥(N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)) :
    ((artinianPolynomialInducedNumeratorComponent I N hN i degree P :
        ↥(N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)) :
      artinianFreePolynomialModule B n r) =
        artinianPolynomialModuleComponent weight shift degree P :=
  rfl

/-- Compatibility of the numerator component with the quotient relation of
an induced layer. -/
theorem artinianPolynomialInducedNumeratorComponent_quotientRel
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    {P Q : ↥(N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)}
    (hPQ :
      ((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)).comap
        (N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype).quotientRel P Q) :
    ((N ⊓ artinianPolynomialIdealPowerSubmodule
        (n := n) (r := r) I (i + 1)).comap
      (N ⊓ artinianPolynomialIdealPowerSubmodule
        (n := n) (r := r) I i).subtype).quotientRel
      (artinianPolynomialInducedNumeratorComponent I N hN i degree P)
      (artinianPolynomialInducedNumeratorComponent I N hN i degree Q) := by
  rw [Submodule.quotientRel_def] at hPQ ⊢
  change ((P : artinianFreePolynomialModule B n r) - Q) ∈
    N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I (i + 1) at hPQ
  change
    artinianPolynomialModuleComponent weight shift degree P -
        artinianPolynomialModuleComponent weight shift degree Q ∈
      N ⊓ artinianPolynomialIdealPowerSubmodule
        (n := n) (r := r) I (i + 1)
  rw [← map_sub]
  exact ⟨hN _ hPQ.1 degree,
    artinianPolynomialModuleComponent_mem_idealPower
      (n := n) (r := r) I (i + 1) weight shift degree hPQ.2⟩

/-- The additive weighted component on one actual induced layer. -/
def artinianPolynomialInducedLayerComponent
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ) :
    artinianPolynomialInducedLayer (n := n) (r := r) I N i →+
      artinianPolynomialInducedLayer (n := n) (r := r) I N i where
  toFun := Quotient.map'
    (artinianPolynomialInducedNumeratorComponent I N hN i degree)
    (fun _ _ hPQ => artinianPolynomialInducedNumeratorComponent_quotientRel
      I N hN i degree hPQ)
  map_zero' := by
    change Submodule.Quotient.mk
        (artinianPolynomialInducedNumeratorComponent I N hN i degree 0) =
      Submodule.Quotient.mk 0
    rw [map_zero]
  map_add' := by
    intro x y
    refine Submodule.Quotient.induction_on _ x ?_
    intro P
    refine Submodule.Quotient.induction_on _ y ?_
    intro Q
    change Submodule.Quotient.mk
        (artinianPolynomialInducedNumeratorComponent I N hN i degree (P + Q)) =
      Submodule.Quotient.mk
          (artinianPolynomialInducedNumeratorComponent I N hN i degree P) +
        Submodule.Quotient.mk
          (artinianPolynomialInducedNumeratorComponent I N hN i degree Q)
    rw [map_add, Submodule.Quotient.mk_add]

@[simp]
theorem artinianPolynomialInducedLayerComponent_mk
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    (P : ↥(N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)) :
    artinianPolynomialInducedLayerComponent I N hN i degree
        (Submodule.Quotient.mk P) =
      Submodule.Quotient.mk
        (artinianPolynomialInducedNumeratorComponent I N hN i degree P) :=
  rfl

/-- The induced-layer embedding commutes with weighted components. -/
theorem artinianPolynomialInducedLayerMap_component
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    letI := artinianPolynomialInducedLayerModule (n := n) (r := r) I N i
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    artinianPolynomialInducedLayerMap (n := n) (r := r) I N i
        (artinianPolynomialInducedLayerComponent I N hN i degree x) =
      artinianPolynomialAmbientLayerComponent I i weight shift degree
        (artinianPolynomialInducedLayerMap (n := n) (r := r) I N i x) := by
  let _ := artinianPolynomialInducedLayerModule (n := n) (r := r) I N i
  let _ := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
  refine Submodule.Quotient.induction_on _ x ?_
  intro P
  simp only [artinianPolynomialInducedLayerComponent_mk,
    artinianPolynomialInducedLayerMap, inducedSubmoduleLayerPushforwardMap,
    inducedSubmoduleLayerMap, Submodule.mapQ_apply,
    artinianPolynomialAmbientLayerComponent_mk]
  rfl

/-! ## Pointwise components on the fixed finite product -/

/-- Weighted component applied independently in every ambient layer below
the fixed cutoff. -/
def artinianPolynomialAmbientLayerSumComponent
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianPolynomialAmbientLayerSum (n := n) (r := r) I e →+
      artinianPolynomialAmbientLayerSum (n := n) (r := r) I e where
  toFun x i := artinianPolynomialAmbientLayerComponent
    I i.1 weight shift degree (x i)
  map_zero' := by
    funext i
    exact map_zero _
  map_add' x y := by
    funext i
    exact map_add _ _ _

@[simp]
theorem artinianPolynomialAmbientLayerSumComponent_apply
    (I : Ideal B) (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e)
    (i : Fin e) :
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree x i =
      artinianPolynomialAmbientLayerComponent I i.1 weight shift degree (x i) :=
  rfl

/-- Weighted component applied independently in every induced layer below
the fixed cutoff. -/
def artinianPolynomialInducedLayerSumComponent
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ) :
    artinianPolynomialInducedLayerSum (n := n) (r := r) I N e →+
      artinianPolynomialInducedLayerSum (n := n) (r := r) I N e where
  toFun x i := artinianPolynomialInducedLayerComponent
    I N hN i.1 degree (x i)
  map_zero' := by
    funext i
    exact map_zero _
  map_add' x y := by
    funext i
    exact map_add _ _ _

@[simp]
theorem artinianPolynomialInducedLayerSumComponent_apply
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e)
    (i : Fin e) :
    artinianPolynomialInducedLayerSumComponent I N hN e degree x i =
      artinianPolynomialInducedLayerComponent I N hN i.1 degree (x i) :=
  rfl

/-- The simultaneous induced-layer embedding commutes with pointwise
weighted components. -/
theorem artinianPolynomialInducedLayerSumMap_component
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
    artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e
        (artinianPolynomialInducedLayerSumComponent I N hN e degree x) =
      artinianPolynomialAmbientLayerSumComponent I e weight shift degree
        (artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e x) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  funext i
  exact artinianPolynomialInducedLayerMap_component
    (n := n) (r := r) I N hN i.1 degree (x i)

/-- The image of a homogeneous polynomial submodule in the fixed product of
ambient layers is stable under every pointwise weighted component. -/
theorem artinianPolynomialAmbientLayerSumComponent_mem_range
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    {x : artinianPolynomialAmbientLayerSum (n := n) (r := r) I e}
    (hx :
      letI (i : Fin e) :=
        artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
      letI (i : Fin e) :=
        artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
      x ∈ LinearMap.range
        (artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e)) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree x ∈
      LinearMap.range
        (artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  obtain ⟨y, rfl⟩ := hx
  refine ⟨artinianPolynomialInducedLayerSumComponent I N hN e degree y, ?_⟩
  exact artinianPolynomialInducedLayerSumMap_component
    (n := n) (r := r) I N hN e degree y

end PolynomialLayerComponents

end AbelFormalization
