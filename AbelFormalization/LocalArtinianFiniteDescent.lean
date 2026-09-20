import AbelFormalization.ArtinianGradedCoverKernel
import AbelFormalization.FiniteWeightQuotient
import AbelFormalization.PolynomialModuleUniformGenerators
import Mathlib.Data.ENat.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Local Artinian finite descent: degree slices and filtration lifting

This file isolates the two exact linear-algebra steps needed to pass from the
residue-field layer construction back to a polynomial submodule over a local
Artinian coefficient ring.

First, a surjective linear cover commuting with two idempotent degree
projections restricts to a surjection between the corresponding degree
slices.  Rank-nullity then gives the kernel-corrected Hilbert function of the
pullback.  Second, if a fixed finite family spans every successive induced
quotient layer of a finite filtration, then the same family spans the original
submodule.  Neither result assumes that the dimensions of the individual
Artinian layers are constant.
-/

noncomputable section

namespace AbelFormalization

/-! ## Degree slices through a linear cover -/

section ProjectionSlices

variable {K F E : Type*} [Semiring K]
variable [AddCommMonoid F] [Module K F] [AddCommMonoid E] [Module K E]

/-- The part of the inverse image of `W` lying in the image of a source
degree projection. -/
def projectionPullbackSlice (q : F →ₗ[K] E) (W : Submodule K E)
    (sourceComponent : F →ₗ[K] F) : Submodule K F :=
  W.comap q ⊓ LinearMap.range sourceComponent

/-- The part of `W` lying in the image of a target degree projection. -/
def projectionTargetSlice (W : Submodule K E)
    (targetComponent : E →ₗ[K] E) : Submodule K E :=
  W ⊓ LinearMap.range targetComponent

/-- An idempotent linear map fixes every element of its range. -/
theorem LinearMap.eq_self_of_mem_range_of_idempotent
    (p : E →ₗ[K] E) (hp : ∀ x, p (p x) = p x) {x : E}
    (hx : x ∈ LinearMap.range p) : p x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact hp y

/-- A cover commuting with the two degree projections restricts to a map
between the corresponding pullback and target slices. -/
def projectionPullbackSliceMap
    (q : F →ₗ[K] E) (W : Submodule K E)
    (sourceComponent : F →ₗ[K] F) (targetComponent : E →ₗ[K] E)
    (hcomponent : ∀ x, q (sourceComponent x) = targetComponent (q x)) :
    projectionPullbackSlice q W sourceComponent →ₗ[K]
      projectionTargetSlice W targetComponent where
  toFun x := ⟨q x, ⟨x.property.1, by
    obtain ⟨y, hy⟩ := x.property.2
    refine ⟨q y, ?_⟩
    rw [← hcomponent, hy]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact q.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact q.map_smul c x

@[simp]
theorem projectionPullbackSliceMap_coe
    (q : F →ₗ[K] E) (W : Submodule K E)
    (sourceComponent : F →ₗ[K] F) (targetComponent : E →ₗ[K] E)
    (hcomponent : ∀ x, q (sourceComponent x) = targetComponent (q x))
    (x : projectionPullbackSlice q W sourceComponent) :
    ((projectionPullbackSliceMap q W sourceComponent targetComponent hcomponent x :
        projectionTargetSlice W targetComponent) : E) = q x := rfl

/-- Surjectivity of the original cover descends to every target degree
slice.  The proof projects an arbitrary lift in the source. -/
theorem projectionPullbackSliceMap_surjective
    (q : F →ₗ[K] E) (hq : Function.Surjective q) (W : Submodule K E)
    (sourceComponent : F →ₗ[K] F) (targetComponent : E →ₗ[K] E)
    (hcomponent : ∀ x, q (sourceComponent x) = targetComponent (q x))
    (htarget : ∀ x, targetComponent (targetComponent x) = targetComponent x) :
    Function.Surjective
      (projectionPullbackSliceMap q W sourceComponent targetComponent hcomponent) := by
  intro y
  obtain ⟨x, hx⟩ := hq (y : E)
  have hyfixed : targetComponent (y : E) = y :=
    LinearMap.eq_self_of_mem_range_of_idempotent
      targetComponent htarget y.property.2
  let x' : projectionPullbackSlice q W sourceComponent :=
    ⟨sourceComponent x, ⟨by
      change q (sourceComponent x) ∈ W
      rw [hcomponent, hx, hyfixed]
      exact y.property.1, ⟨x, rfl⟩⟩⟩
  refine ⟨x', ?_⟩
  apply Subtype.ext
  change q (sourceComponent x) = (y : E)
  rw [hcomponent, hx, hyfixed]

/-- The kernel of the restricted slice map is canonically the source degree
slice of the kernel of the original cover. -/
def projectionPullbackSliceKernelEquiv
    (q : F →ₗ[K] E) (W : Submodule K E)
    (sourceComponent : F →ₗ[K] F) (targetComponent : E →ₗ[K] E)
    (hcomponent : ∀ x, q (sourceComponent x) = targetComponent (q x)) :
    ((LinearMap.ker q ⊓ LinearMap.range sourceComponent) : Submodule K F) ≃ₗ[K]
      LinearMap.ker
        (projectionPullbackSliceMap q W sourceComponent targetComponent hcomponent) where
  toFun x := ⟨⟨x, ⟨by
    change q (x : F) ∈ W
    rw [LinearMap.mem_ker.mp x.property.1]
    exact W.zero_mem, x.property.2⟩⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact LinearMap.mem_ker.mp x.property.1⟩
  invFun y := ⟨((y : projectionPullbackSlice q W sourceComponent) : F), ⟨by
    apply LinearMap.mem_ker.mpr
    have hy := LinearMap.mem_ker.mp y.property
    exact congrArg Subtype.val hy, y.val.property.2⟩⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

end ProjectionSlices

section ProjectionSliceFinrank

variable {K F E : Type*} [Field K]
variable [AddCommGroup F] [Module K F] [AddCommGroup E] [Module K E]

/-- Rank-nullity for an actual projected degree slice.  The target summand
and the fixed-kernel summand add to the pullback degree dimension. -/
theorem finrank_projectionPullbackSlice_eq_add
    (q : F →ₗ[K] E) (hq : Function.Surjective q) (W : Submodule K E)
    (sourceComponent : F →ₗ[K] F) (targetComponent : E →ₗ[K] E)
    (hcomponent : ∀ x, q (sourceComponent x) = targetComponent (q x))
    (htarget : ∀ x, targetComponent (targetComponent x) = targetComponent x)
    [FiniteDimensional K (projectionPullbackSlice q W sourceComponent)] :
    Module.finrank K (projectionPullbackSlice q W sourceComponent) =
      Module.finrank K
          ((LinearMap.ker q ⊓ LinearMap.range sourceComponent) : Submodule K F) +
        Module.finrank K (projectionTargetSlice W targetComponent) := by
  let f := projectionPullbackSliceMap q W sourceComponent targetComponent hcomponent
  have hf : Function.Surjective f :=
    projectionPullbackSliceMap_surjective q hq W sourceComponent targetComponent
      hcomponent htarget
  have hrank := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top,
    ← (projectionPullbackSliceKernelEquiv
      q W sourceComponent targetComponent hcomponent).finrank_eq] at hrank
  omega

end ProjectionSliceFinrank

/-! ### A component range inside an embedded homogeneous target -/

section ComponentSlices

variable {K : Type*} [Semiring K]

/-- The range of a source component maps to the corresponding degree slice
inside the range of an injective intertwining map. -/
def componentRangeToTargetSlice
    {G H : Type*} [AddCommGroup G] [Module K G]
    [AddCommGroup H] [Module K H]
    (j : G →ₗ[K] H) (sourceComponent : G →ₗ[K] G)
    (targetComponent : H →ₗ[K] H)
    (hcomponent : ∀ x, j (sourceComponent x) = targetComponent (j x)) :
    LinearMap.range sourceComponent →ₗ[K]
      projectionTargetSlice (LinearMap.range j) targetComponent where
  toFun x := ⟨j x, ⟨⟨x, rfl⟩, by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨j y, ?_⟩
    rw [← hcomponent, hy]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact j.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact j.map_smul c x

@[simp]
theorem componentRangeToTargetSlice_coe
    {G H : Type*} [AddCommGroup G] [Module K G]
    [AddCommGroup H] [Module K H]
    (j : G →ₗ[K] H) (sourceComponent : G →ₗ[K] G)
    (targetComponent : H →ₗ[K] H)
    (hcomponent : ∀ x, j (sourceComponent x) = targetComponent (j x))
    (x : LinearMap.range sourceComponent) :
    ((componentRangeToTargetSlice j sourceComponent targetComponent hcomponent x :
        projectionTargetSlice (LinearMap.range j) targetComponent) : H) =
      j x := rfl

/-- If the embedding is injective and the target component is idempotent,
the preceding map is a linear equivalence.  This records that taking a
degree slice commutes with identifying a module with its image. -/
noncomputable def componentRangeEquivTargetSlice
    {G H : Type*} [AddCommGroup G] [Module K G]
    [AddCommGroup H] [Module K H]
    (j : G →ₗ[K] H) (hj : Function.Injective j)
    (sourceComponent : G →ₗ[K] G) (targetComponent : H →ₗ[K] H)
    (hcomponent : ∀ x, j (sourceComponent x) = targetComponent (j x))
    (htarget : ∀ x, targetComponent (targetComponent x) = targetComponent x) :
    LinearMap.range sourceComponent ≃ₗ[K]
      projectionTargetSlice (LinearMap.range j) targetComponent := by
  let f := componentRangeToTargetSlice
    j sourceComponent targetComponent hcomponent
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply hj
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := y.property.1
    have hyfixed : targetComponent (y : H) = y :=
      LinearMap.eq_self_of_mem_range_of_idempotent
        targetComponent htarget y.property.2
    have hxFixed : sourceComponent x = x := by
      apply hj
      calc
        j (sourceComponent x) = targetComponent (j x) := hcomponent x
        _ = targetComponent (y : H) := congrArg targetComponent hx
        _ = (y : H) := hyfixed
        _ = j x := hx.symm
    let x' : LinearMap.range sourceComponent := ⟨x, ⟨x, hxFixed⟩⟩
    refine ⟨x', ?_⟩
    apply Subtype.ext
    exact hx

/-- The target degree slice has the same dimension as the range of the
intertwined source component. -/
theorem finrank_projectionTargetSlice_eq_componentRange
    {G H : Type*} [AddCommGroup G] [Module K G]
    [AddCommGroup H] [Module K H]
    (j : G →ₗ[K] H) (hj : Function.Injective j)
    (sourceComponent : G →ₗ[K] G) (targetComponent : H →ₗ[K] H)
    (hcomponent : ∀ x, j (sourceComponent x) = targetComponent (j x))
    (htarget : ∀ x, targetComponent (targetComponent x) = targetComponent x) :
    Module.finrank K
        (projectionTargetSlice (LinearMap.range j) targetComponent) =
      Module.finrank K (LinearMap.range sourceComponent) := by
  exact (componentRangeEquivTargetSlice j hj sourceComponent targetComponent
    hcomponent htarget).finrank_eq.symm

end ComponentSlices

/-! ## The source polynomial degree projection -/

section PolynomialProjection

variable {K : Type*} [Field K] {n r : ℕ}

/-- The range of the actual weighted polynomial component is exactly the
corresponding shifted homogeneous piece. -/
theorem range_weightedPolynomialModuleComponent_eq_piece
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    LinearMap.range (weightedPolynomialModuleComponent
      (K := K) weight shift degree) =
        weightedPolynomialModulePiece weight shift degree := by
  ext P
  constructor
  · rintro ⟨Q, rfl⟩
    exact weightedPolynomialModuleComponent_mem weight shift degree Q
  · intro hP
    exact ⟨P, weightedPolynomialModuleComponent_eq_self
      weight shift degree hP⟩

/-- The actual weighted polynomial component is idempotent. -/
theorem weightedPolynomialModuleComponent_idempotent
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (P : Fin r → MvPolynomial (Fin n) K) :
    weightedPolynomialModuleComponent weight shift degree
        (weightedPolynomialModuleComponent weight shift degree P) =
      weightedPolynomialModuleComponent weight shift degree P :=
  weightedPolynomialModuleComponent_eq_self weight shift degree
    (weightedPolynomialModuleComponent_mem weight shift degree P)

/-- Positive weights make an actual weighted polynomial-module piece finite
dimensional.  This instance-producing form complements the numerical
`finrank_weightedPolynomialModulePiece` theorem. -/
theorem weightedPolynomialModulePiece_moduleFinite
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (degree : ℤ) :
    Module.Finite K
      (weightedPolynomialModulePiece (K := K) weight shift degree) := by
  let _ : Fintype (shiftedModuleDegreeTerms weight shift degree) :=
    (shiftedModuleDegreeTerms_finite weight hweight shift degree).fintype
  exact Module.Finite.equiv
    (polynomialModuleSupportedEquiv
      (K := K) (shiftedModuleDegreeTerms weight shift degree)).symm

end PolynomialProjection

/-! ## Actual degree layers of the induced Artinian filtration -/

section ArtinianDegreeLayers

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- The `i`th actual quotient in the filtration of the degree-`degree`
piece.  Its numerator and denominator are the induced Artinian filtration
terms, rather than intrinsic powers of the submodule. -/
abbrev artinianPolynomialInducedDegreeLayer
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) :=
  submoduleLayer
    (artinianPolynomialInducedDegreeFiltration
      I N weight shift degree i)
    (artinianPolynomialInducedDegreeFiltration
      I N weight shift degree (i + 1))

/-- Canonical residue-ring action on one actual degree quotient. -/
@[instance_reducible]
def artinianPolynomialInducedDegreeLayerModule
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (i : ℕ) :
    Module (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i) :=
  submoduleLayerQuotientModule I
    (artinianPolynomialInducedDegreeFiltration
      I N weight shift degree i)
    (artinianPolynomialInducedDegreeFiltration
      I N weight shift degree (i + 1))
    (artinianPolynomialInducedDegreeFiltration_smul_le
      I N weight shift degree i)

/-- Product of all actual degree quotients below the fixed nilpotence
cutoff. -/
abbrev artinianPolynomialInducedDegreeLayerSum
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (e : ℕ) :=
  (i : Fin e) →
    artinianPolynomialInducedDegreeLayer
      I N weight shift degree i.1

/-- Each actual degree quotient is finite dimensional over the residue
field.  Finiteness comes from the finite ambient degree piece; it does not
use finiteness of the whole polynomial module over `B`. -/
theorem artinianPolynomialInducedDegreeLayer_moduleFinite
    [IsArtinianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i
    Module.Finite (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ : Module.Finite B
      (artinianPolynomialModulePiece (B := B) weight shift degree) :=
    artinianPolynomialModulePiece_moduleFinite weight hweight shift degree
  let _ : IsNoetherian B
      (artinianPolynomialModulePiece (B := B) weight shift degree) :=
    inferInstance
  let A := artinianPolynomialInducedDegreeFiltration
    I N weight shift degree i
  let A' := artinianPolynomialInducedDegreeFiltration
    I N weight shift degree (i + 1)
  let hAA' : I • A ≤ A' :=
    artinianPolynomialInducedDegreeFiltration_smul_le
      I N weight shift degree i
  let _ := artinianPolynomialInducedDegreeLayerModule
    I N weight shift degree i
  let _ : IsScalarTower B (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i) :=
    (submoduleLayer_isTorsionBySet I A A' hAA').isScalarTower
  let _ : IsNoetherian (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i) :=
    isNoetherian_of_tower B inferInstance
  infer_instance

/-- The dimension of the finite product of actual degree quotients is the
sum of their canonical residue dimensions. -/
theorem finrank_artinianPolynomialInducedDegreeLayerSum
    [IsArtinianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (degree : ℤ) (e : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    Module.finrank (B ⧸ I)
        (artinianPolynomialInducedDegreeLayerSum
          I N weight shift degree e) =
      ∑ i ∈ Finset.range e,
        submoduleLayerResidueFinrank I
          (artinianPolynomialInducedDegreeFiltration
            I N weight shift degree i)
          (artinianPolynomialInducedDegreeFiltration
            I N weight shift degree (i + 1))
          (artinianPolynomialInducedDegreeFiltration_smul_le
            I N weight shift degree i) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  letI degreeLayerModule (i : Fin e) : Module (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) :=
    artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
  letI degreeLayerFree (i : Fin e) : Module.Free (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  let _ (i : Fin e) : Module.Finite (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) :=
    artinianPolynomialInducedDegreeLayer_moduleFinite
      I N weight hweight shift degree i.1
  rw [Module.finrank_pi_fintype]
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- The dimension of the product of actual degree quotients is the natural
number represented by the Artinian length of the original degree piece. -/
theorem finrank_artinianPolynomialInducedDegreeLayerSum_eq_length_toNat
    [IsArtinianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (degree : ℤ) {e : ℕ} (he : I ^ e = ⊥) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    Module.finrank (B ⧸ I)
        (artinianPolynomialInducedDegreeLayerSum
          I N weight shift degree e) =
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          N weight shift degree)).toNat := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  letI degreeLayerModule (i : Fin e) : Module (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) :=
    artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
  have hlength :=
    artinianPolynomialSubmoduleDegree_length_eq_sum_layer_finranks
      I N weight hweight shift degree he
  have hlengthNat := congrArg ENat.toNat hlength
  rw [ENat.toNat_sum (by
    intro i hi
    simp)] at hlengthNat
  simp only [ENat.toNat_natCast] at hlengthNat
  rw [finrank_artinianPolynomialInducedDegreeLayerSum
    I N weight hweight shift degree e]
  exact hlengthNat.symm

/-- The remaining grading identification, isolated as one exact interface:
the product of the actual degree-filtered quotients is the range of the
degree component on the full induced layer sum.  No equality of the
individual layer dimensions is part of this proposition. -/
def ArtinianInducedLayerDegreeIdentification
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) : Prop :=
  letI : Field (B ⧸ I) := Ideal.Quotient.field I
  letI (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  letI (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  letI := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  ∀ degree : ℤ,
    letI (i : Fin e) : AddCommMonoid
        (artinianPolynomialInducedDegreeLayer
          I N weight shift degree i.1) := inferInstance
    letI (i : Fin e) := artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
    Nonempty
      (artinianPolynomialInducedDegreeLayerSum
          I N weight shift degree e ≃ₗ[B ⧸ I]
        LinearMap.range
          (artinianPolynomialInducedLayerSumComponentLinear
            I N hN e degree))

/-- The exact grading identification converts the induced component range
dimension to the length of the original Artinian degree piece. -/
theorem finrank_artinianPolynomialInducedLayerSumComponentRange_eq_length_toNat
    [IsArtinianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ)
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    {e : ℕ} (he : I ^ e = ⊥)
    (hidentify : ArtinianInducedLayerDegreeIdentification I N hN e)
    (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    Module.finrank (B ⧸ I)
        (LinearMap.range
          (artinianPolynomialInducedLayerSumComponentLinear
            I N hN e degree)) =
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          N weight shift degree)).toNat := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  letI degreeLayerAdd (i : Fin e) : AddCommMonoid
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) := inferInstance
  letI degreeLayerModule (i : Fin e) : Module (B ⧸ I)
      (artinianPolynomialInducedDegreeLayer
        I N weight shift degree i.1) :=
    artinianPolynomialInducedDegreeLayerModule
      I N weight shift degree i.1
  obtain ⟨equiv⟩ := hidentify degree
  calc
    Module.finrank (B ⧸ I)
        (LinearMap.range
          (artinianPolynomialInducedLayerSumComponentLinear
            I N hN e degree)) =
      Module.finrank (B ⧸ I)
        (artinianPolynomialInducedDegreeLayerSum
          I N weight shift degree e) := equiv.finrank_eq.symm
    _ = (Module.length B
        (artinianPolynomialSubmoduleDegree
          N weight shift degree)).toNat :=
      finrank_artinianPolynomialInducedDegreeLayerSum_eq_length_toNat
        I N weight hweight shift degree he

end ArtinianDegreeLayers

/-! ## The fixed graded cover as residue-field linear algebra -/

section ArtinianGradedCoverSlices

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- Restrict the fixed graded cover to constants in the residue polynomial
ring.  This explicit bundle avoids any dependence on typeclass search for a
scalar-tower instance generated from `Module.compHom`. -/
def artinianPolynomialAmbientLayerSumGradedCoverResidueLinear
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal] (e : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)) →ₗ[B ⧸ I]
      artinianPolynomialAmbientLayerSum (n := n) (r := r) I e := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  let q := artinianPolynomialAmbientLayerSumGradedCover
    (n := n) (r := r) I e
  exact
    { toFun := q
      map_add' := q.map_add
      map_smul' := by
        intro c x
        calc
          q (c • x) = q
              ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • x) :=
            congrArg q (mvPolynomialPi_C_smul_eq c x).symm
          _ = (MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • q x :=
            q.map_smul _ _
          _ = c • q x := rfl }

@[simp]
theorem artinianPolynomialAmbientLayerSumGradedCoverResidueLinear_apply
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal] (e : ℕ)
    (x : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
      MvPolynomial (Fin n) (B ⧸ I)) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSumGradedCoverResidueLinear I e x =
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x := rfl

/-- Restrict the simultaneous induced-layer embedding to residue
coefficients. -/
def artinianPolynomialInducedLayerSumMapResidueLinear
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialInducedLayerSum (n := n) (r := r) I N e →ₗ[B ⧸ I]
      artinianPolynomialAmbientLayerSum (n := n) (r := r) I e := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
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
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro c x
        change f
            ((MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • x) =
          (MvPolynomial.C c : MvPolynomial (Fin n) (B ⧸ I)) • f x
        exact f.map_smul _ _ }

@[simp]
theorem artinianPolynomialInducedLayerSumMapResidueLinear_apply
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialInducedLayerSumMapResidueLinear I N e x =
      artinianPolynomialInducedLayerSumMap
        (n := n) (r := r) I N e x := rfl

/-- The residue-linear graded cover is surjective. -/
theorem artinianPolynomialAmbientLayerSumGradedCoverResidueLinear_surjective
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal] (e : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    Function.Surjective
      (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear
        (n := n) (r := r) I e) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  exact artinianPolynomialAmbientLayerSumGradedCover_surjective
    (n := n) (r := r) I e

/-- The residue-linear induced-layer embedding is injective. -/
theorem artinianPolynomialInducedLayerSumMapResidueLinear_injective
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    Function.Injective
      (artinianPolynomialInducedLayerSumMapResidueLinear
        (n := n) (r := r) I N e) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  exact artinianPolynomialInducedLayerSumMap_injective
    (n := n) (r := r) I N e

/-- The residue-linear cover intertwines the field source component and the
ambient layer-sum component. -/
theorem artinianPolynomialAmbientLayerSumGradedCoverResidueLinear_component
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal] (e : ℕ)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (x : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
      MvPolynomial (Fin n) (B ⧸ I)) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSumGradedCoverResidueLinear I e
        (weightedPolynomialModuleComponent weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x) =
      artinianPolynomialAmbientLayerSumComponentLinear
        I e weight shift degree
        (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear I e x) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  change artinianPolynomialAmbientLayerSumGradedCover
      (n := n) (r := r) I e
      (weightedPolynomialModuleComponent weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree x) =
    artinianPolynomialAmbientLayerSumComponent I e weight shift degree
      (artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x)
  rw [← artinianPolynomialModuleComponent_eq_weightedPolynomialModuleComponent]
  exact (artinianPolynomialAmbientLayerSumGradedCover_component
    (n := n) (r := r) I e weight shift degree x).symm

/-- The residue-linear induced-layer embedding intertwines the induced and
ambient components. -/
theorem artinianPolynomialInducedLayerSumMapResidueLinear_component
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialInducedLayerSumMapResidueLinear I N e
        (artinianPolynomialInducedLayerSumComponentLinear
          I N hN e degree x) =
      artinianPolynomialAmbientLayerSumComponentLinear
        I e weight shift degree
        (artinianPolynomialInducedLayerSumMapResidueLinear I N e x) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  exact artinianPolynomialInducedLayerSumMap_component
    (n := n) (r := r) I N hN e degree x

end ArtinianGradedCoverSlices

section ArtinianPullbackSlices

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- Actual field degree slice of the polynomial pullback of the induced
Artinian layer sum.  This is the subspace whose dimension is passed to the
field uniform-generator theorem. -/
def artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (e : ℕ) (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule (B ⧸ I)
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact
    (artinianPolynomialInducedLayerSumGradedPullback
      (n := n) (r := r) I N e).restrictScalars (B ⧸ I) ⊓
      weightedPolynomialModulePiece weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree

/-- Actual field degree slice of the fixed kernel of the graded cover. -/
def artinianPolynomialAmbientLayerSumGradedCoverKernelDegreeSlice
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (e : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule (B ⧸ I)
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact
    (artinianPolynomialAmbientLayerSumGradedCoverKernel
      (n := n) (r := r) I e).restrictScalars (B ⧸ I) ⊓
      weightedPolynomialModulePiece weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree

/-- The concrete pullback degree slice is the abstract projected pullback
slice for the two residue-linear maps. -/
theorem artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice_eq_projection
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (e : ℕ) (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice
        I N weight shift e degree =
      projectionPullbackSlice
        (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear
          (n := n) (r := r) I e)
        (artinianPolynomialInducedLayerSumMapResidueLinear
          (n := n) (r := r) I N e).range
        (weightedPolynomialModuleComponent weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  ext x
  change
    (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e x ∈
        LinearMap.range
          (artinianPolynomialInducedLayerSumMap
            (n := n) (r := r) I N e) ∧
      x ∈ weightedPolynomialModulePiece weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree) ↔
    (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear I e x ∈
        LinearMap.range
          (artinianPolynomialInducedLayerSumMapResidueLinear I N e) ∧
      x ∈ LinearMap.range
        (weightedPolynomialModuleComponent weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree))
  rw [range_weightedPolynomialModuleComponent_eq_piece]
  rfl

/-- The concrete fixed-kernel degree slice is the kernel component slice of
the residue-linear cover. -/
theorem artinianPolynomialAmbientLayerSumGradedCoverKernelDegreeSlice_eq_projection
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (e : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    artinianPolynomialAmbientLayerSumGradedCoverKernelDegreeSlice
        I e weight shift degree =
      LinearMap.ker
          (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear
            (n := n) (r := r) I e) ⊓
        LinearMap.range
          (weightedPolynomialModuleComponent weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  ext x
  change
    (artinianPolynomialAmbientLayerSumGradedCover
          (n := n) (r := r) I e x = 0 ∧
      x ∈ weightedPolynomialModulePiece weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree) ↔
    (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear I e x = 0 ∧
      x ∈ LinearMap.range
        (weightedPolynomialModuleComponent weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree))
  rw [range_weightedPolynomialModuleComponent_eq_piece]
  rfl

end ArtinianPullbackSlices

/-! ## Fixed kernel-corrected Hilbert functions -/

section KernelCorrectedHilbert

variable {K : Type*} [Field K] {n r : ℕ}

/-- The Hilbert function supplied to the field uniform-generator theorem is
the fixed kernel contribution plus the desired quotient contribution. -/
def kernelCorrectedHilbertFunction
    (kernelHilbert quotientHilbert : ℤ → ℕ) : ℤ → ℕ :=
  fun degree => kernelHilbert degree + quotientHilbert degree

/-- Uniform field-case generators with a Hilbert function presented in
kernel-plus-quotient form.  This is the exact quantifier order needed for a
fixed graded cover: the bound is selected before the pullback submodule. -/
theorem exists_uniform_finite_homogeneous_generators_of_kernelCorrectedHilbert
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ)
    (hweight : ∀ i, 0 < weight i) (shift : Fin r → ℤ)
    (kernelHilbert quotientHilbert : ℤ → ℕ) :
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) K)
          (Fin r → MvPolynomial (Fin n) K),
        IsWeightedPolynomialModuleHomogeneous weight shift N →
        (∀ degree : ℤ, Module.finrank K
          ((N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) :
            Submodule K (Fin r → MvPolynomial (Fin n) K)) =
              kernelCorrectedHilbertFunction kernelHilbert quotientHilbert degree) →
        ∃ G : Finset (Fin r → MvPolynomial (Fin n) K),
          (∀ P ∈ G, P ∈ N ∧ ∃ degree : ℤ,
            degree ≤ (D : ℤ) ∧
              P ∈ weightedPolynomialModulePiece weight shift degree) ∧
          Submodule.span (MvPolynomial (Fin n) K) (G : Set _) = N := by
  exact exists_uniform_finite_homogeneous_polynomialModule_generators
    m weight hweight shift
      (kernelCorrectedHilbertFunction kernelHilbert quotientHilbert)

/-! ### The kernel-corrected Artinian pullback formula -/

variable {B : Type*} [CommRing B]

/-- Rank-nullity for the fixed graded cover: the pullback degree consists of
the fixed cover-kernel degree plus the degree component in the induced layer
sum. -/
theorem finrank_artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice_eq_add
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ)
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    Module.finrank (B ⧸ I)
        (artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice
          I N weight shift e degree) =
      Module.finrank (B ⧸ I)
          (artinianPolynomialAmbientLayerSumGradedCoverKernelDegreeSlice
            I e weight shift degree) +
        Module.finrank (B ⧸ I)
          (LinearMap.range
            (artinianPolynomialInducedLayerSumComponentLinear
              I N hN e degree)) := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  let q := artinianPolynomialAmbientLayerSumGradedCoverResidueLinear
    (n := n) (r := r) I e
  let j := artinianPolynomialInducedLayerSumMapResidueLinear
    (n := n) (r := r) I N e
  let sourceComponent := weightedPolynomialModuleComponent
    (K := B ⧸ I) weight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      degree
  let targetComponent := artinianPolynomialAmbientLayerSumComponentLinear
    I e weight shift degree
  let inducedComponent := artinianPolynomialInducedLayerSumComponentLinear
    I N hN e degree
  let _ : Module.Finite (B ⧸ I)
      (weightedPolynomialModulePiece (K := B ⧸ I) weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree) :=
    weightedPolynomialModulePiece_moduleFinite weight hweight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      degree
  let _ : Module.Finite (B ⧸ I) (LinearMap.range sourceComponent) := by
    rw [show LinearMap.range sourceComponent =
        weightedPolynomialModulePiece (K := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree from
      range_weightedPolynomialModuleComponent_eq_piece weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree]
    infer_instance
  let _ : Module.Finite (B ⧸ I)
      (projectionPullbackSlice q (LinearMap.range j) sourceComponent) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hrank := by
    with_reducible_and_instances
      exact finrank_projectionPullbackSlice_eq_add
        (K := B ⧸ I)
        (F := Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
          MvPolynomial (Fin n) (B ⧸ I))
        (E := artinianPolynomialAmbientLayerSum (n := n) (r := r) I e)
        q
        (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear_surjective
          (n := n) (r := r) I e)
        (LinearMap.range j) sourceComponent targetComponent
        (artinianPolynomialAmbientLayerSumGradedCoverResidueLinear_component
          (n := n) (r := r) I e weight shift degree)
        (artinianPolynomialAmbientLayerSumComponentLinear_idempotent
          (n := n) (r := r) I e weight shift degree)
  have htarget := finrank_projectionTargetSlice_eq_componentRange
    (K := B ⧸ I)
    (G := artinianPolynomialInducedLayerSum (n := n) (r := r) I N e)
    (H := artinianPolynomialAmbientLayerSum (n := n) (r := r) I e)
    j
    (artinianPolynomialInducedLayerSumMapResidueLinear_injective
      (n := n) (r := r) I N e)
    inducedComponent targetComponent
    (artinianPolynomialInducedLayerSumMapResidueLinear_component
      (n := n) (r := r) I N hN e degree)
    (artinianPolynomialAmbientLayerSumComponentLinear_idempotent
      (n := n) (r := r) I e weight shift degree)
  rw [← artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice_eq_projection
      I N weight shift e degree,
    ← artinianPolynomialAmbientLayerSumGradedCoverKernelDegreeSlice_eq_projection
      I e weight shift degree,
    htarget] at hrank
  exact hrank

/-- The fixed degreewise contribution of the kernel of the graded ambient
cover.  It depends on the ambient Artinian filtration and its chosen graded
cover, but never on the varying submodule `N`. -/
def artinianPolynomialAmbientLayerSumGradedCoverKernelHilbert
    [IsNoetherianRing B]
    (I : Ideal B) [I.IsMaximal]
    (e : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ) : ℤ → ℕ :=
  fun degree =>
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Module.finrank (B ⧸ I)
      (artinianPolynomialAmbientLayerSumGradedCoverKernelDegreeSlice
        I e weight shift degree)

/-- Once the exact degree-layer identification is supplied, the pullback has
the fixed kernel-corrected Hilbert function determined by the Artinian
lengths of the original degree pieces. -/
theorem finrank_artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice_eq_kernelCorrected
    [IsArtinianRing B]
    (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ)
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    {e : ℕ} (he : I ^ e = ⊥)
    (hidentify : ArtinianInducedLayerDegreeIdentification I N hN e)
    (hilbertLength : ℤ → ℕ)
    (hlength : ∀ degree,
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          N weight shift degree)).toNat = hilbertLength degree)
    (degree : ℤ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialInducedLayerSumResidueModule
      (n := n) (r := r) I N e
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    Module.finrank (B ⧸ I)
        (artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice
          I N weight shift e degree) =
      kernelCorrectedHilbertFunction
        (artinianPolynomialAmbientLayerSumGradedCoverKernelHilbert
          I e weight shift)
        hilbertLength degree := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  rw [finrank_artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice_eq_add
      I N weight hweight shift hN e degree,
    finrank_artinianPolynomialInducedLayerSumComponentRange_eq_length_toNat
      I N weight hweight shift hN he hidentify degree,
    hlength degree]
  rfl

/-- A uniform field-case degree bound for all graded pullbacks with one
fixed Artinian length function.  The bound is selected before `N`; the only
remaining input is the exact grading identification between the actual
degree filtration quotients and the component range in the induced layer
sum. -/
theorem exists_uniform_finite_homogeneous_artinianLayerPullback_generators
    [IsArtinianRing B]
    (m : MonomialOrder (Fin n))
    (I : Ideal B) [I.IsMaximal]
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) {e : ℕ} (he : I ^ e = ⊥)
    (hilbertLength : ℤ → ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r),
        letI (i : Fin e) :=
          artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
        letI := artinianPolynomialInducedLayerSumResidueModule
          (n := n) (r := r) I N e
        ∀ hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N,
        ArtinianInducedLayerDegreeIdentification I N hN e →
        (∀ degree,
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              N weight shift degree)).toNat = hilbertLength degree) →
        ∃ G : Finset
            (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
              MvPolynomial (Fin n) (B ⧸ I)),
          (∀ P ∈ G,
            P ∈ artinianPolynomialInducedLayerSumGradedPullback
                (n := n) (r := r) I N e ∧
              ∃ degree : ℤ, degree ≤ (D : ℤ) ∧
                P ∈ weightedPolynomialModulePiece weight
                  (artinianPolynomialAmbientLayerSumGradedGeneratorShift
                    I e shift)
                  degree) ∧
          Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
            artinianPolynomialInducedLayerSumGradedPullback
              (n := n) (r := r) I N e := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  obtain ⟨D, hD⟩ :=
    exists_uniform_finite_homogeneous_generators_of_kernelCorrectedHilbert
      (K := B ⧸ I) m weight hweight
      (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
      (artinianPolynomialAmbientLayerSumGradedCoverKernelHilbert
        I e weight shift)
      hilbertLength
  refine ⟨D, ?_⟩
  intro N
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  intro hN hidentify hlength
  apply hD
    (artinianPolynomialInducedLayerSumGradedPullback
      (n := n) (r := r) I N e)
  · exact
      artinianPolynomialInducedLayerSumGradedPullback_weightedHomogeneous
        (n := n) (r := r) I N hN e
  · intro degree
    change Module.finrank (B ⧸ I)
        (artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice
          I N weight shift e degree) =
      kernelCorrectedHilbertFunction
        (artinianPolynomialAmbientLayerSumGradedCoverKernelHilbert
          I e weight shift)
        hilbertLength degree
    exact
      finrank_artinianPolynomialInducedLayerSumGradedPullbackDegreeSlice_eq_kernelCorrected
        I N weight hweight shift hN he hidentify hilbertLength hlength degree

end KernelCorrectedHilbert

/-! ## Lifting generators through a finite induced filtration -/

section FiltrationLifting

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- The term of the ambient filtration induced on `N`. -/
def inducedFiltrationTerm (N : Submodule R V) (F : ℕ → Submodule R V)
    (i : ℕ) : Submodule R V :=
  N ⊓ F i

/-- If a candidate submodule surjects onto every successive induced quotient
of a finite filtration, then it contains the filtered submodule. -/
theorem le_of_surjects_on_induced_filtration
    (N L : Submodule R V) (F : ℕ → Submodule R V) (e : ℕ)
    (hFzero : F 0 = ⊤) (hFend : F e = ⊥)
    (hsurj : ∀ i, i < e →
      let A := inducedFiltrationTerm N F i
      let A' := inducedFiltrationTerm N F (i + 1)
      (L.comap A.subtype).map ((A'.comap A.subtype).mkQ) = ⊤) :
    N ≤ L := by
  let A : ℕ → Submodule R V := inducedFiltrationTerm N F
  have hAend : A e = ⊥ := by
    simp [A, inducedFiltrationTerm, hFend]
  have hstep : ∀ i, i < e → A (i + 1) ≤ L → A i ≤ L := by
    intro i hi hnext x hx
    let xi : A i := ⟨x, hx⟩
    have htop :
        ((A (i + 1)).comap (A i).subtype).mkQ xi ∈
          (⊤ : Submodule R ((A i) ⧸ (A (i + 1)).comap (A i).subtype)) :=
      Submodule.mem_top
    have hsurj' := hsurj i hi
    dsimp only at hsurj'
    change (L.comap (A i).subtype).map
      (((A (i + 1)).comap (A i).subtype).mkQ) = ⊤ at hsurj'
    rw [← hsurj'] at htop
    obtain ⟨y, hyL, hyq⟩ := htop
    have hdiff : xi - y ∈ (A (i + 1)).comap (A i).subtype :=
      (Submodule.Quotient.eq _).mp hyq.symm
    have hdiffL : ((xi - y : A i) : V) ∈ L :=
      hnext hdiff
    have hyLV : (y : V) ∈ L := hyL
    have hsum : ((xi - y : A i) : V) + (y : V) = x := by
      change (x - (y : V)) + (y : V) = x
      exact sub_add_cancel x y
    rw [← hsum]
    exact L.add_mem hdiffL hyLV
  have hback : ∀ i, i ≤ e → A i ≤ L := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self =>
      rw [hAend]
      exact bot_le
    | of_succ i hi ih =>
      exact hstep i hi ih
  intro x hx
  have hxA : x ∈ A 0 := by
    simpa [A, inducedFiltrationTerm, hFzero] using hx
  exact hback 0 (Nat.zero_le e) hxA

/-- Equality follows when the candidate is already contained in `N`. -/
theorem eq_of_surjects_on_induced_filtration
    (N L : Submodule R V) (F : ℕ → Submodule R V) (e : ℕ)
    (hL : L ≤ N) (hFzero : F 0 = ⊤) (hFend : F e = ⊥)
    (hsurj : ∀ i, i < e →
      let A := inducedFiltrationTerm N F i
      let A' := inducedFiltrationTerm N F (i + 1)
      (L.comap A.subtype).map ((A'.comap A.subtype).mkQ) = ⊤) :
    L = N := by
  apply le_antisymm hL
  exact le_of_surjects_on_induced_filtration N L F e hFzero hFend hsurj

/-- A finite set whose span surjects onto every induced quotient layer is a
finite generating set upstairs. -/
theorem span_eq_of_surjects_on_induced_filtration
    (N : Submodule R V) (F : ℕ → Submodule R V) (e : ℕ)
    (G : Finset V) (hG : ∀ x ∈ G, x ∈ N)
    (hFzero : F 0 = ⊤) (hFend : F e = ⊥)
    (hsurj : ∀ i, i < e →
      let A := inducedFiltrationTerm N F i
      let A' := inducedFiltrationTerm N F (i + 1)
      ((Submodule.span R (G : Set V)).comap A.subtype).map
        ((A'.comap A.subtype).mkQ) = ⊤) :
    Submodule.span R (G : Set V) = N := by
  apply eq_of_surjects_on_induced_filtration N
    (Submodule.span R (G : Set V)) F e
  · exact Submodule.span_le.mpr fun x hx => hG x hx
  · exact hFzero
  · exact hFend
  · exact hsurj

/-! ### The polynomial ideal-power filtration -/

/-- Specialization of the filtration lift to the coefficient-ideal power
filtration of a finite free polynomial module.  Thus representatives that
span every induced quotient layer generate the original polynomial
submodule. -/
theorem span_eq_of_surjects_on_artinianPolynomialIdealPowerFiltration
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {e : ℕ} (he : I ^ e = ⊥)
    (G : Finset (artinianFreePolynomialModule B n r))
    (hG : ∀ x ∈ G, x ∈ N)
    (hsurj : ∀ i, i < e →
      let A := N ⊓
        artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i
      let A' := N ⊓
        artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1)
      ((Submodule.span (MvPolynomial (Fin n) B) (G : Set _)).comap
          A.subtype).map
        ((A'.comap A.subtype).mkQ) = ⊤) :
    Submodule.span (MvPolynomial (Fin n) B) (G : Set _) = N := by
  apply span_eq_of_surjects_on_induced_filtration N
    (fun i => artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i) e G hG
  · change artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I 0 = ⊤
    exact idealPowerSubmodule_zero
      (artinianPolynomialCoefficientIdeal (n := n) I)
  · exact artinianPolynomialIdealPowerSubmodule_eq_bot
      (n := n) (r := r) I he
  · exact hsurj

end FiltrationLifting

end AbelFormalization
