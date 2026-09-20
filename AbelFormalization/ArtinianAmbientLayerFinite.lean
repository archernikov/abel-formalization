import AbelFormalization.IdealPowerLayers
import Mathlib.RingTheory.Finiteness.Cardinality

set_option autoImplicit false

/-!
# Finite free covers of the Artinian ambient layers

This file isolates the finiteness argument needed after `IdealPowerLayers`.
It deliberately does not choose a coefficient-field section.  The ambient
layer is first finite over the Noetherian polynomial ring `B[z]`; its existing
module structure is then pushed through the surjection
`B[z] → (B/I)[z]`.  A finite free cover is finally chosen from
`Module.Finite.exists_fin'`.

The argument only needs `B` Noetherian.  The Artinian-local specialization is
an immediate instance-driven corollary.
-/

noncomputable section

namespace AbelFormalization

open Function

/-- The identity on an annihilated layer, regarded as a semilinear map from
the original scalar ring to the pushed-forward scalar ring. -/
def submoduleLayerPushforwardSemilinearMap
    {A C W : Type*} [CommRing A] [CommRing C] [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q) (F G : Submodule A W)
    (hker : RingHom.ker q • F ≤ G) :
    letI := submoduleLayerPushforwardModule q hq F G hker
    submoduleLayer F G →ₛₗ[q] submoduleLayer F G := by
  let _ : Module (A ⧸ RingHom.ker q) (submoduleLayer F G) :=
    submoduleLayerQuotientModule (RingHom.ker q) F G hker
  let _ := submoduleLayerPushforwardModule q hq F G hker
  exact
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change a • x =
          (RingHom.quotientKerEquivOfSurjective (f := q) hq).symm (q a) • x
        rw [RingHom.quotientKerEquivOfSurjective_symm_apply (f := q)]
        change a • x = a • x
        rfl }

/-- Finite generation descends through the pushed-forward scalar action.
This is the module-theoretic reason that no section of `q` is needed. -/
theorem submoduleLayerPushforward_moduleFinite
    {A C W : Type*} [CommRing A] [CommRing C] [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q) (F G : Submodule A W)
    (hker : RingHom.ker q • F ≤ G)
    [Module.Finite A (submoduleLayer F G)] :
    letI := submoduleLayerPushforwardModule q hq F G hker
    Module.Finite C (submoduleLayer F G) := by
  let _ := submoduleLayerPushforwardModule q hq F G hker
  exact Module.Finite.of_surjective
    (submoduleLayerPushforwardSemilinearMap q hq F G hker)
    (fun x => ⟨x, rfl⟩)

section PolynomialAmbientLayers

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- Every fixed ambient ideal-power layer is a finite module over the residue
polynomial ring.  The proof first uses Noetherianity over `B[z]` and then
pushes the finite generating family through coefficientwise reduction. -/
theorem artinianPolynomialAmbientLayer_moduleFinite_of_isNoetherianRing
    [IsNoetherianRing B] (I : Ideal B) (i : ℕ) :
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    Module.Finite (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayer (n := n) (r := r) I i) := by
  let _ := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
  let _ : Module.Finite (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r) := inferInstance
  let _ : IsNoetherian (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r) := inferInstance
  let _ : Module.Finite (MvPolynomial (Fin n) B)
      (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) :=
    inferInstance
  let _ : Module.Finite (MvPolynomial (Fin n) B)
      (artinianPolynomialAmbientLayer (n := n) (r := r) I i) :=
    inferInstance
  exact submoduleLayerPushforward_moduleFinite
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))
    (artinianPolynomialAmbientLayer_annihilation (n := n) (r := r) I i)

/-- Artinian rings are Noetherian, so the preceding result applies in the
intended local-Artinian setting. -/
theorem artinianPolynomialAmbientLayer_moduleFinite
    [IsArtinianRing B] (I : Ideal B) (i : ℕ) :
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    Module.Finite (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayer (n := n) (r := r) I i) :=
  artinianPolynomialAmbientLayer_moduleFinite_of_isNoetherianRing
    (n := n) (r := r) I i

/-- A finite product of the fixed ambient layers is finite over `(B/I)[z]`. -/
theorem artinianPolynomialAmbientLayerSum_moduleFinite
    [IsArtinianRing B] (I : Ideal B) (e : ℕ) :
    letI (j : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
    Module.Finite (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) := by
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  let _ (j : Fin e) :
      Module.Finite (MvPolynomial (Fin n) (B ⧸ I))
        (artinianPolynomialAmbientLayer (n := n) (r := r) I j.1) :=
    artinianPolynomialAmbientLayer_moduleFinite (n := n) (r := r) I j.1
  infer_instance

/-- Concrete data of a finite free module mapping onto a module. -/
structure FiniteFreeCover (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] where
  rank : ℕ
  map : (Fin rank → R) →ₗ[R] M
  surjective : Function.Surjective map

/-- Choose a finite free cover of any finite module. -/
def FiniteFreeCover.ofModuleFinite (R M : Type*) [Semiring R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    FiniteFreeCover R M :=
  let h := Module.Finite.exists_fin' R M
  { rank := h.choose
    map := h.choose_spec.choose
    surjective := h.choose_spec.choose_spec }

/-- A single chosen finite free residue-polynomial module covers the product
of all ambient layers below the cutoff.  Its rank depends only on
`B`, `I`, `n`, `r`, and `e`, never on the varying submodule `N`. -/
def artinianPolynomialAmbientLayerSumFiniteFreeCover
    [IsArtinianRing B] (I : Ideal B) (e : ℕ) :
    letI (j : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
    FiniteFreeCover (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) := by
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  let _ : Module.Finite (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :=
    artinianPolynomialAmbientLayerSum_moduleFinite (n := n) (r := r) I e
  exact FiniteFreeCover.ofModuleFinite _ _

theorem artinianPolynomialAmbientLayerSumFiniteFreeCover_surjective
    [IsArtinianRing B] (I : Ideal B) (e : ℕ) :
    letI (j : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
    Function.Surjective
      (artinianPolynomialAmbientLayerSumFiniteFreeCover
        (n := n) (r := r) I e).map := by
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  exact (artinianPolynomialAmbientLayerSumFiniteFreeCover
    (n := n) (r := r) I e).surjective

end PolynomialAmbientLayers

end AbelFormalization
