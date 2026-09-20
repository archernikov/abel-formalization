import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false

/-!
# Actual quotient layers of ideal-power filtrations

Layers of an ambient ideal-power filtration are
actual submodule quotients. Ideal annihilation supplies their canonical
quotient-ring scalar structure. Finite-filtration length additivity is
proved from short exact sequences and then specialized to induced layers
`N ∩ I^i V`. No coefficient-field section is used or postulated.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The actual quotient F/(F∩G), viewed as a quotient of the submodule F. -/
abbrev submoduleLayer (F G : Submodule R V) := F ⧸ G.comap F.subtype

/-- I kills the quotient layer whenever I⋅F is contained in G. -/
theorem submoduleLayer_isTorsionBySet (I : Ideal R) (F G : Submodule R V)
    (hIF : I • F ≤ G) : Module.IsTorsionBySet R (submoduleLayer F G) I := by
  apply (Module.isTorsionBySet_quotient_iff (G.comap F.subtype) I).mpr
  intro x a ha
  exact hIF (Submodule.smul_mem_smul ha x.property)

/-- The quotient-ring module structure comes from actual annihilation. -/
@[instance_reducible]
def submoduleLayerQuotientModule (I : Ideal R) (F G : Submodule R V)
    (hIF : I • F ≤ G) : Module (R ⧸ I) (submoduleLayer F G) :=
  (submoduleLayer_isTorsionBySet I F G hIF).module

/-- A numerical residue-field dimension using the canonical scalar action. -/
def submoduleLayerResidueFinrank (I : Ideal R) [I.IsMaximal]
    (F G : Submodule R V) (hIF : I • F ≤ G) : ℕ :=
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  letI := submoduleLayerQuotientModule I F G hIF
  Module.finrank (R ⧸ I) (submoduleLayer F G)

/-- For a Noetherian ambient module, an annihilated layer is finite over
the actual residue field, and its residue dimension equals its R-length. -/
theorem submoduleLayer_length_eq_residue_finrank [IsNoetherian R V]
    (I : Ideal R) [I.IsMaximal] (F G : Submodule R V) (hIF : I • F ≤ G) :
    Module.length R (submoduleLayer F G) =
      (submoduleLayerResidueFinrank I F G hIF : ℕ∞) := by
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  let _ := submoduleLayerQuotientModule I F G hIF
  let _ : IsScalarTower R (R ⧸ I) (submoduleLayer F G) :=
    (submoduleLayer_isTorsionBySet I F G hIF).isScalarTower
  let _ : IsNoetherian (R ⧸ I) (submoduleLayer F G) :=
    isNoetherian_of_tower R inferInstance
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
      (M := submoduleLayer F G) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]
  rfl

/-- The same length comparison only needs the numerator of the layer to be
Noetherian.  This form is needed for a finite homogeneous piece inside an
ambient polynomial module, which is usually not finite over its coefficient
ring. -/
theorem submoduleLayer_length_eq_residue_finrank_of_noetherian
    (I : Ideal R) [I.IsMaximal] (F G : Submodule R V) [IsNoetherian R F]
    (hIF : I • F ≤ G) :
    Module.length R (submoduleLayer F G) =
      (submoduleLayerResidueFinrank I F G hIF : ℕ∞) := by
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  let _ := submoduleLayerQuotientModule I F G hIF
  let _ : IsScalarTower R (R ⧸ I) (submoduleLayer F G) :=
    (submoduleLayer_isTorsionBySet I F G hIF).isScalarTower
  let _ : IsNoetherian (R ⧸ I) (submoduleLayer F G) :=
    isNoetherian_of_tower R inferInstance
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
      (M := submoduleLayer F G) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]
  rfl

/-- An induced quotient layer maps to the fixed ambient quotient layer. -/
def inducedSubmoduleLayerMap (N F G : Submodule R V) :
    submoduleLayer (N ⊓ F) (N ⊓ G) →ₗ[R] submoduleLayer F G :=
  ((N ⊓ G).comap (N ⊓ F).subtype).mapQ (G.comap F.subtype)
    (Submodule.inclusion inf_le_right) (show
      (N ⊓ G).comap (N ⊓ F).subtype ≤
        (G.comap F.subtype).comap (Submodule.inclusion inf_le_right) from by
          intro x hx
          exact hx.2)

/-- The induced layer is a genuine submodule of the ambient layer; its
kernel is precisely the next induced filtration term. -/
theorem inducedSubmoduleLayerMap_injective (N F G : Submodule R V) :
    Function.Injective (inducedSubmoduleLayerMap N F G) := by
  have hden : (G.comap F.subtype).comap (Submodule.inclusion
      (show N ⊓ F ≤ F from inf_le_right)) = (N ⊓ G).comap (N ⊓ F).subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨x.property.1, hx⟩
    · exact fun hx => hx.2
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker
      (((N ⊓ G).comap (N ⊓ F).subtype).mapQ (G.comap F.subtype)
        (Submodule.inclusion inf_le_right) _) = ⊥
  rw [Submodule.ker_mapQ, hden, Submodule.mkQ_map_self]

/-- A quotient layer is part of an actual short exact sequence. -/
theorem submodule_length_eq_add_layer (F G : Submodule R V) (hGF : G ≤ F) :
    Module.length R F = Module.length R G + Module.length R (submoduleLayer F G) := by
  have h := Module.length_eq_add_of_exact (G.comap F.subtype).subtype
    (G.comap F.subtype).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(Submodule.comapSubtypeEquivOfLe hGF).length_eq] at h
  exact h

/-- Length telescopes along an actual finite descending filtration.
The identity remains valid for infinite extended-natural lengths. -/
theorem submodule_length_eq_sum_layers_add (F : ℕ → Submodule R V)
    (hF : ∀ i, F (i + 1) ≤ F i) (e : ℕ) :
    Module.length R (F 0) =
      (∑ i ∈ Finset.range e, Module.length R (submoduleLayer (F i) (F (i + 1)))) +
        Module.length R (F e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    calc
      Module.length R (F 0) =
          (∑ i ∈ Finset.range e, Module.length R (submoduleLayer (F i) (F (i + 1)))) +
            Module.length R (F e) := ih
      _ = (∑ i ∈ Finset.range e, Module.length R (submoduleLayer (F i) (F (i + 1)))) +
            (Module.length R (F (e + 1)) +
              Module.length R (submoduleLayer (F e) (F (e + 1)))) := by
        rw [submodule_length_eq_add_layer (F e) (F (e + 1)) (hF e)]
      _ = _ := by ac_rfl

/-- A finite descending filtration killed one step at a time by a maximal
ideal has total length equal to the sum of the canonical residue-field
dimensions of its layers.  No assertion is made about the individual layer
dimensions in a family. -/
theorem submodule_length_eq_sum_residue_finrank_of_filtration [IsNoetherian R V]
    (I : Ideal R) [I.IsMaximal] (F : ℕ → Submodule R V)
    (hF : ∀ i, F (i + 1) ≤ F i) (hIF : ∀ i, I • F i ≤ F (i + 1))
    {e : ℕ} (he : F e = ⊥) :
    Module.length R (F 0) =
      ∑ i ∈ Finset.range e,
        (submoduleLayerResidueFinrank I (F i) (F (i + 1)) (hIF i) : ℕ∞) := by
  rw [submodule_length_eq_sum_layers_add F hF e, he, Module.length_bot, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  exact submoduleLayer_length_eq_residue_finrank_of_noetherian
    I (F i) (F (i + 1)) (hIF i)

/-- The actual ambient ideal-power filtration. -/
def idealPowerSubmodule (I : Ideal R) (i : ℕ) : Submodule R V :=
  I ^ i • (⊤ : Submodule R V)

@[simp]
theorem idealPowerSubmodule_zero (I : Ideal R) : idealPowerSubmodule (V := V) I 0 = ⊤ := by
  simp [idealPowerSubmodule]

theorem idealPowerSubmodule_succ (I : Ideal R) (i : ℕ) :
    idealPowerSubmodule (V := V) I (i + 1) = I • idealPowerSubmodule I i := by
  rw [idealPowerSubmodule, pow_succ', Submodule.mul_smul]
  rfl

theorem idealPowerSubmodule_succ_le (I : Ideal R) (i : ℕ) :
    idealPowerSubmodule (V := V) I (i + 1) ≤ idealPowerSubmodule I i := by
  rw [idealPowerSubmodule_succ]
  exact Submodule.smul_le_right

theorem idealPowerSubmodule_eq_bot (I : Ideal R) {e : ℕ} (he : I ^ e = ⊥) :
    idealPowerSubmodule (V := V) I e = ⊥ := by
  simp [idealPowerSubmodule, he]

/-- Multiplication by I advances the induced ambient filtration, even
though it need not generate the whole next induced term. -/
theorem idealPower_induced_smul_le (I : Ideal R) (N : Submodule R V) (i : ℕ) :
    I • (N ⊓ idealPowerSubmodule I i) ≤ N ⊓ idealPowerSubmodule I (i + 1) := by
  apply Submodule.smul_le.mpr
  intro a ha x hx
  refine ⟨N.smul_mem a hx.1, ?_⟩
  rw [idealPowerSubmodule_succ]
  exact Submodule.smul_mem_smul ha hx.2

/-- Actual induced layers, rather than the generally different intrinsic
filtration I^iN, recover the full length of N. -/
theorem idealPower_induced_length_eq_sum_layers (I : Ideal R) (N : Submodule R V)
    {e : ℕ} (he : I ^ e = ⊥) :
    Module.length R N =
      ∑ i ∈ Finset.range e, Module.length R
        (submoduleLayer (N ⊓ idealPowerSubmodule I i)
          (N ⊓ idealPowerSubmodule I (i + 1))) := by
  have h := submodule_length_eq_sum_layers_add (fun i => N ⊓ idealPowerSubmodule I i)
    (fun i => inf_le_inf_left N (idealPowerSubmodule_succ_le I i)) e
  rw [idealPowerSubmodule_zero, inf_top_eq, idealPowerSubmodule_eq_bot I he,
    inf_bot_eq, Module.length_bot, add_zero] at h
  exact h

/-- The sum of all induced-layer residue dimensions equals length.
Individual layer dimensions are not asserted to be invariant in a family. -/
theorem idealPower_induced_length_eq_sum_residue_finrank [IsNoetherian R V]
    (I : Ideal R) [I.IsMaximal] (N : Submodule R V) {e : ℕ} (he : I ^ e = ⊥) :
    Module.length R N =
      ∑ i ∈ Finset.range e,
        (submoduleLayerResidueFinrank I (N ⊓ idealPowerSubmodule I i)
          (N ⊓ idealPowerSubmodule I (i + 1)) (idealPower_induced_smul_le I N i) : ℕ∞) := by
  rw [idealPower_induced_length_eq_sum_layers I N he]
  apply Finset.sum_congr rfl
  intro i hi
  exact submoduleLayer_length_eq_residue_finrank I _ _ (idealPower_induced_smul_le I N i)

/-- The finite filtration length is derived for an actual Artinian local
coefficient ring, not imposed as a nilpotence assumption. -/
theorem exists_maximalIdeal_pow_eq_bot_for_layers [IsLocalRing R] [IsArtinianRing R] :
    ∃ e : ℕ, IsLocalRing.maximalIdeal R ^ e = ⊥ := by
  obtain ⟨e, he⟩ :=
    IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (⊥ : Ideal R)
  exact ⟨e, le_bot_iff.mp he⟩

/-- Every finite module over an actual Artinian local ring has the
claimed induced-layer length identity, with a common ambient cutoff. -/
theorem exists_artinian_induced_layer_length [IsLocalRing R] [IsArtinianRing R]
    [Module.Finite R V] :
    ∃ e : ℕ, IsLocalRing.maximalIdeal R ^ e = ⊥ ∧
      ∀ N : Submodule R V, Module.length R N =
        ∑ i ∈ Finset.range e,
          (submoduleLayerResidueFinrank (IsLocalRing.maximalIdeal R)
            (N ⊓ idealPowerSubmodule (IsLocalRing.maximalIdeal R) i)
            (N ⊓ idealPowerSubmodule (IsLocalRing.maximalIdeal R) (i + 1))
            (idealPower_induced_smul_le (IsLocalRing.maximalIdeal R) N i) : ℕ∞) := by
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_bot_for_layers (R := R)
  exact ⟨e, he, fun N => idealPower_induced_length_eq_sum_residue_finrank
    (IsLocalRing.maximalIdeal R) N he⟩

section PolynomialGradingBridge

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- The finite free polynomial module used for the Artinian grading bridge. -/
abbrev artinianFreePolynomialModule (B : Type*) [CommRing B] (n r : ℕ) :=
  Fin r → MvPolynomial (Fin n) B

/-- Actual coefficient coordinates for a finite free polynomial module over
an arbitrary commutative coefficient ring. -/
def artinianPolynomialModuleCoeffEquiv :
    artinianFreePolynomialModule B n r ≃ₗ[B]
      (Fin r × (Fin n →₀ ℕ)) →₀ B :=
  ((LinearEquiv.piCongrRight (fun _ : Fin r =>
      (AddMonoidAlgebra.coeffLinearEquiv B :
        MvPolynomial (Fin n) B ≃ₗ[B] (Fin n →₀ ℕ) →₀ B))).trans
    (Finsupp.linearEquivFunOnFinite B ((Fin n →₀ ℕ) →₀ B) (Fin r)).symm).trans
    (Finsupp.curryLinearEquiv B).symm

@[simp]
theorem artinianPolynomialModuleCoeffEquiv_apply
    (P : artinianFreePolynomialModule B n r) (k : Fin r) (d : Fin n →₀ ℕ) :
    artinianPolynomialModuleCoeffEquiv P (k, d) = (P k).coeff d := by
  rfl

/-- The coefficient submodule supported on a set of component monomials. -/
def artinianPolynomialModuleSupported (T : Set (Fin r × (Fin n →₀ ℕ))) :
    Submodule B (artinianFreePolynomialModule B n r) :=
  (Finsupp.supported B B T).comap artinianPolynomialModuleCoeffEquiv.toLinearMap

theorem mem_artinianPolynomialModuleSupported
    (T : Set (Fin r × (Fin n →₀ ℕ)))
    (P : artinianFreePolynomialModule B n r) :
    P ∈ artinianPolynomialModuleSupported T ↔
      ∀ k d, (P k).coeff d ≠ 0 → (k, d) ∈ T := by
  rw [artinianPolynomialModuleSupported, Submodule.mem_comap, Finsupp.mem_supported]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    Prod.forall, LinearEquiv.coe_coe, artinianPolynomialModuleCoeffEquiv_apply]

/-- Restriction of the actual coefficient equivalence to a supported piece. -/
def artinianPolynomialModuleSupportedEquiv
    (T : Set (Fin r × (Fin n →₀ ℕ))) :
    artinianPolynomialModuleSupported (B := B) T ≃ₗ[B] T →₀ B :=
  (artinianPolynomialModuleCoeffEquiv.ofSubmodule' (Finsupp.supported B B T)).trans
    (Finsupp.supportedEquivFinsupp (R := B) T)

/-- Shifted positive-weight degree of a component monomial. -/
def artinianPolynomialTermDegree (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (t : Fin r × (Fin n →₀ ℕ)) : ℤ :=
  (Finsupp.weight weight t.2 : ℤ) + shift t.1

/-- The component monomials in one shifted ordinary degree. -/
def artinianPolynomialDegreeTerms (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) : Set (Fin r × (Fin n →₀ ℕ)) :=
  {t | artinianPolynomialTermDegree weight shift t = degree}

theorem artinianPolynomialDegreeTerms_finite (weight : Fin n → ℕ)
    (hweight : ∀ i, 0 < weight i) (shift : Fin r → ℤ) (degree : ℤ) :
    (artinianPolynomialDegreeTerms weight shift degree).Finite := by
  have hcomponent (k : Fin r) :
      {d : Fin n →₀ ℕ | (Finsupp.weight weight d : ℤ) + shift k = degree}.Finite := by
    apply (Finsupp.finite_of_nat_weight_le weight (fun i => (hweight i).ne')
      (degree - shift k).toNat).subset
    intro d hd
    have he : (Finsupp.weight weight d : ℤ) = degree - shift k := eq_sub_of_add_eq hd
    exact Int.ofNat_le.mp (he.trans_le (Int.self_le_toNat _))
  have hfinite := Set.finite_iUnion (fun k : Fin r => (hcomponent k).image (Prod.mk k))
  apply hfinite.subset
  intro t ht
  exact Set.mem_iUnion.mpr ⟨t.1, ⟨t.2, ht, rfl⟩⟩

/-- One actual shifted homogeneous piece over the Artinian coefficient ring. -/
def artinianPolynomialModulePiece (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) : Submodule B (artinianFreePolynomialModule B n r) :=
  artinianPolynomialModuleSupported (artinianPolynomialDegreeTerms weight shift degree)

/-- Positivity makes each homogeneous piece a finite module over the
coefficient ring, even though the whole polynomial module is not. -/
theorem artinianPolynomialModulePiece_moduleFinite (weight : Fin n → ℕ)
    (hweight : ∀ i, 0 < weight i) (shift : Fin r → ℤ) (degree : ℤ) :
    Module.Finite B (artinianPolynomialModulePiece (B := B) weight shift degree) := by
  let _ : Fintype (artinianPolynomialDegreeTerms weight shift degree) :=
    (artinianPolynomialDegreeTerms_finite weight hweight shift degree).fintype
  exact Module.Finite.equiv
    (artinianPolynomialModuleSupportedEquiv
      (B := B) (artinianPolynomialDegreeTerms weight shift degree)).symm

/-- Push an annihilated quotient layer along an actual surjective ring map.
The action is obtained from the first-isomorphism equivalence, so it does not
choose a section of the surjection. -/
@[instance_reducible]
def submoduleLayerPushforwardModule
    {A C W : Type*} [CommRing A] [CommRing C] [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q) (F G : Submodule A W)
    (hker : RingHom.ker q • F ≤ G) : Module C (submoduleLayer F G) :=
  letI : Module (A ⧸ RingHom.ker q) (submoduleLayer F G) :=
    submoduleLayerQuotientModule (RingHom.ker q) F G hker
  Module.compHom (submoduleLayer F G)
    (RingHom.quotientKerEquivOfSurjective (f := q) hq).symm.toRingHom

/-- The natural injection of an induced layer into an ambient layer is linear
after both canonical quotient actions are pushed along the same surjection. -/
def inducedSubmoduleLayerPushforwardMap
    {A C W : Type*} [CommRing A] [CommRing C] [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q) (N F G : Submodule A W)
    (hsource : RingHom.ker q • (N ⊓ F) ≤ N ⊓ G)
    (htarget : RingHom.ker q • F ≤ G) :
    letI := submoduleLayerPushforwardModule q hq (N ⊓ F) (N ⊓ G) hsource
    letI := submoduleLayerPushforwardModule q hq F G htarget
    submoduleLayer (N ⊓ F) (N ⊓ G) →ₗ[C] submoduleLayer F G := by
  let _ : Module (A ⧸ RingHom.ker q) (submoduleLayer (N ⊓ F) (N ⊓ G)) :=
    submoduleLayerQuotientModule (RingHom.ker q) (N ⊓ F) (N ⊓ G) hsource
  let _ : Module (A ⧸ RingHom.ker q) (submoduleLayer F G) :=
    submoduleLayerQuotientModule (RingHom.ker q) F G htarget
  let _ := submoduleLayerPushforwardModule q hq (N ⊓ F) (N ⊓ G) hsource
  let _ := submoduleLayerPushforwardModule q hq F G htarget
  let f := inducedSubmoduleLayerMap N F G
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := hq c
        change f ((RingHom.quotientKerEquivOfSurjective (f := q) hq).symm (q a) • x) =
          (RingHom.quotientKerEquivOfSurjective (f := q) hq).symm (q a) • f x
        rw [RingHom.quotientKerEquivOfSurjective_symm_apply (f := q)]
        change f (a • x) = a • f x
        exact f.map_smul a x }

theorem inducedSubmoduleLayerPushforwardMap_injective
    {A C W : Type*} [CommRing A] [CommRing C] [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q) (N F G : Submodule A W)
    (hsource : RingHom.ker q • (N ⊓ F) ≤ N ⊓ G)
    (htarget : RingHom.ker q • F ≤ G) :
    letI := submoduleLayerPushforwardModule q hq (N ⊓ F) (N ⊓ G) hsource
    letI := submoduleLayerPushforwardModule q hq F G htarget
    Function.Injective
      (inducedSubmoduleLayerPushforwardMap q hq N F G hsource htarget) := by
  let _ : Module (A ⧸ RingHom.ker q) (submoduleLayer (N ⊓ F) (N ⊓ G)) :=
    submoduleLayerQuotientModule (RingHom.ker q) (N ⊓ F) (N ⊓ G) hsource
  let _ : Module (A ⧸ RingHom.ker q) (submoduleLayer F G) :=
    submoduleLayerQuotientModule (RingHom.ker q) F G htarget
  let _ := submoduleLayerPushforwardModule q hq (N ⊓ F) (N ⊓ G) hsource
  let _ := submoduleLayerPushforwardModule q hq F G htarget
  change Function.Injective (inducedSubmoduleLayerMap N F G)
  exact inducedSubmoduleLayerMap_injective N F G

/-- Extension of a coefficient ideal to the polynomial ring. -/
def artinianPolynomialCoefficientIdeal (I : Ideal B) :
    Ideal (MvPolynomial (Fin n) B) :=
  Ideal.map MvPolynomial.C I

/-- Coefficientwise reduction to the actual residue polynomial ring. -/
def artinianPolynomialResidueMap (I : Ideal B) :
    MvPolynomial (Fin n) B →+* MvPolynomial (Fin n) (B ⧸ I) :=
  MvPolynomial.map (Ideal.Quotient.mk I)

theorem artinianPolynomialResidueMap_surjective (I : Ideal B) :
    Function.Surjective (artinianPolynomialResidueMap (n := n) I) := by
  simpa [artinianPolynomialResidueMap] using
    (MvPolynomial.map_surjective (σ := Fin n) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective)

theorem artinianPolynomialResidueMap_ker (I : Ideal B) :
    RingHom.ker (artinianPolynomialResidueMap (n := n) I) =
      artinianPolynomialCoefficientIdeal (n := n) I := by
  simpa [artinianPolynomialResidueMap, artinianPolynomialCoefficientIdeal] using
    (MvPolynomial.ker_map (σ := Fin n) (Ideal.Quotient.mk I))

/-- The ambient filtration by powers of the extended coefficient ideal. -/
def artinianPolynomialIdealPowerSubmodule (I : Ideal B) (i : ℕ) :
    Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r) :=
  idealPowerSubmodule (V := artinianFreePolynomialModule B n r)
    (artinianPolynomialCoefficientIdeal (n := n) I) i

theorem artinianPolynomialIdealPowerSubmodule_succ (I : Ideal B) (i : ℕ) :
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1) =
      artinianPolynomialCoefficientIdeal (n := n) I •
        artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i :=
  idealPowerSubmodule_succ _ _

theorem artinianPolynomialIdealPowerSubmodule_succ_le (I : Ideal B) (i : ℕ) :
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1) ≤
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i :=
  idealPowerSubmodule_succ_le _ _

theorem artinianPolynomialIdealPowerSubmodule_eq_bot (I : Ideal B) {e : ℕ}
    (he : I ^ e = ⊥) :
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I e = ⊥ := by
  apply idealPowerSubmodule_eq_bot
  calc
    artinianPolynomialCoefficientIdeal (n := n) I ^ e =
        Ideal.map (MvPolynomial.C : B →+* MvPolynomial (Fin n) B) (I ^ e) :=
      (Ideal.map_pow (f := (MvPolynomial.C : B →+* MvPolynomial (Fin n) B))
        (I := I) e).symm
    _ = ⊥ := by rw [he, Ideal.map_bot]

/-- The full induced polynomial layer of a polynomial submodule. -/
abbrev artinianPolynomialInducedLayer (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (i : ℕ) :=
  submoduleLayer (N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))

/-- The corresponding fixed ambient polynomial layer. -/
abbrev artinianPolynomialAmbientLayer (I : Ideal B) (i : ℕ) :=
  submoduleLayer (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))

theorem artinianPolynomialInducedLayer_annihilation (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (i : ℕ) :
    RingHom.ker (artinianPolynomialResidueMap (n := n) I) •
        (N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i) ≤
      N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1) := by
  rw [artinianPolynomialResidueMap_ker]
  exact idealPower_induced_smul_le
    (artinianPolynomialCoefficientIdeal (n := n) I) N i

theorem artinianPolynomialAmbientLayer_annihilation (I : Ideal B) (i : ℕ) :
    RingHom.ker (artinianPolynomialResidueMap (n := n) I) •
        artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i ≤
      artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1) := by
  rw [artinianPolynomialResidueMap_ker,
    artinianPolynomialIdealPowerSubmodule_succ]

/-- Canonical module structure over `(B/I)[z]` on an induced layer.  It is
obtained from the quotient map `B[z] → (B/I)[z]`, not from a map back. -/
@[instance_reducible]
def artinianPolynomialInducedLayerModule (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (i : ℕ) :
    Module (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialInducedLayer (n := n) (r := r) I N i) :=
  submoduleLayerPushforwardModule
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I)
    (N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (N ⊓ artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))
    (artinianPolynomialInducedLayer_annihilation (n := n) (r := r) I N i)

/-- Canonical `(B/I)[z]`-module structure on the fixed ambient layer. -/
@[instance_reducible]
def artinianPolynomialAmbientLayerModule (I : Ideal B) (i : ℕ) :
    Module (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayer (n := n) (r := r) I i) :=
  submoduleLayerPushforwardModule
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))
    (artinianPolynomialAmbientLayer_annihilation (n := n) (r := r) I i)

/-- Each induced polynomial layer embeds linearly into its fixed ambient
layer over the actual residue polynomial ring. -/
def artinianPolynomialInducedLayerMap (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (i : ℕ) :
    letI := artinianPolynomialInducedLayerModule (n := n) (r := r) I N i
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    artinianPolynomialInducedLayer (n := n) (r := r) I N i
      →ₗ[MvPolynomial (Fin n) (B ⧸ I)]
        artinianPolynomialAmbientLayer (n := n) (r := r) I i :=
  inducedSubmoduleLayerPushforwardMap
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I) N
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))
    (artinianPolynomialInducedLayer_annihilation (n := n) (r := r) I N i)
    (artinianPolynomialAmbientLayer_annihilation (n := n) (r := r) I i)

theorem artinianPolynomialInducedLayerMap_injective (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (i : ℕ) :
    letI := artinianPolynomialInducedLayerModule (n := n) (r := r) I N i
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    Function.Injective (artinianPolynomialInducedLayerMap (n := n) (r := r) I N i) :=
  inducedSubmoduleLayerPushforwardMap_injective
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I) N
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))
    (artinianPolynomialInducedLayer_annihilation (n := n) (r := r) I N i)
    (artinianPolynomialAmbientLayer_annihilation (n := n) (r := r) I i)

/-- Finite direct sum of all induced layers, represented by a dependent
finite product. -/
abbrev artinianPolynomialInducedLayerSum (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (e : ℕ) :=
  (i : Fin e) → artinianPolynomialInducedLayer (n := n) (r := r) I N i.1

/-- The fixed finite direct sum of the ambient layers. -/
abbrev artinianPolynomialAmbientLayerSum (I : Ideal B) (e : ℕ) :=
  (i : Fin e) → artinianPolynomialAmbientLayer (n := n) (r := r) I i.1

/-- Simultaneous residue-polynomial-module embedding of all induced layers
into one fixed ambient module.  The target depends on `B`, `I`, `n`, `r`, and
the cutoff, but not on `N`. -/
def artinianPolynomialInducedLayerSumMap (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialInducedLayerSum (n := n) (r := r) I N e
      →ₗ[MvPolynomial (Fin n) (B ⧸ I)]
        artinianPolynomialAmbientLayerSum (n := n) (r := r) I e := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact LinearMap.piMap (fun i : Fin e =>
    artinianPolynomialInducedLayerMap (n := n) (r := r) I N i.1)

theorem artinianPolynomialInducedLayerSumMap_injective (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Function.Injective
      (artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  intro x y hxy
  funext i
  apply artinianPolynomialInducedLayerMap_injective (n := n) (r := r) I N i.1
  simpa [artinianPolynomialInducedLayerSumMap] using congrFun hxy i

/-- The ordinary-degree piece of a polynomial submodule, regarded as a
submodule of the corresponding fixed finite homogeneous ambient piece. -/
def artinianPolynomialSubmoduleDegree
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    Submodule B (artinianPolynomialModulePiece (B := B) weight shift degree) :=
  (N.restrictScalars B).comap
    (artinianPolynomialModulePiece (B := B) weight shift degree).subtype

/-- Restriction of the ambient coefficient-ideal filtration to one ordinary
homogeneous degree. -/
def artinianPolynomialIdealPowerDegreeSubmodule (I : Ideal B)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    Submodule B (artinianPolynomialModulePiece (B := B) weight shift degree) :=
  ((artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i).restrictScalars B).comap
    (artinianPolynomialModulePiece (B := B) weight shift degree).subtype

/-- The filtration on one original homogeneous degree is induced from the
fixed ambient polynomial filtration. -/
def artinianPolynomialInducedDegreeFiltration (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    Submodule B (artinianPolynomialModulePiece (B := B) weight shift degree) :=
  artinianPolynomialSubmoduleDegree N weight shift degree ⊓
    artinianPolynomialIdealPowerDegreeSubmodule I weight shift degree i

/-- This is literally the degree restriction of `N ∩ (mB[z])^i F`; it is
not the generally different intrinsic filtration `m^i N`. -/
theorem artinianPolynomialInducedDegreeFiltration_eq_comap (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    artinianPolynomialInducedDegreeFiltration I N weight shift degree i =
      ((N ⊓ artinianPolynomialIdealPowerSubmodule I i).restrictScalars B).comap
        (artinianPolynomialModulePiece (B := B) weight shift degree).subtype := by
  ext x
  rfl

theorem artinianPolynomialIdealPowerDegreeSubmodule_succ_le (I : Ideal B)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    artinianPolynomialIdealPowerDegreeSubmodule I weight shift degree (i + 1) ≤
      artinianPolynomialIdealPowerDegreeSubmodule I weight shift degree i := by
  intro x hx
  change ((x : artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) ∈
    artinianPolynomialIdealPowerSubmodule I (i + 1) at hx
  change ((x : artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) ∈
    artinianPolynomialIdealPowerSubmodule I i
  exact artinianPolynomialIdealPowerSubmodule_succ_le I i hx

@[simp]
theorem artinianPolynomialIdealPowerDegreeSubmodule_zero (I : Ideal B)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianPolynomialIdealPowerDegreeSubmodule I weight shift degree 0 = ⊤ := by
  rw [artinianPolynomialIdealPowerDegreeSubmodule,
    artinianPolynomialIdealPowerSubmodule,
    idealPowerSubmodule_zero, Submodule.restrictScalars_top]
  simp only [Submodule.comap_top]

theorem artinianPolynomialIdealPowerDegreeSubmodule_eq_bot (I : Ideal B)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) {e : ℕ}
    (he : I ^ e = ⊥) :
    artinianPolynomialIdealPowerDegreeSubmodule I weight shift degree e = ⊥ := by
  rw [artinianPolynomialIdealPowerDegreeSubmodule,
    artinianPolynomialIdealPowerSubmodule_eq_bot I he]
  simp

@[simp]
theorem artinianPolynomialInducedDegreeFiltration_zero (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) :
    artinianPolynomialInducedDegreeFiltration I N weight shift degree 0 =
      artinianPolynomialSubmoduleDegree N weight shift degree := by
  simp [artinianPolynomialInducedDegreeFiltration]

theorem artinianPolynomialInducedDegreeFiltration_eq_bot (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) {e : ℕ}
    (he : I ^ e = ⊥) :
    artinianPolynomialInducedDegreeFiltration I N weight shift degree e = ⊥ := by
  rw [artinianPolynomialInducedDegreeFiltration,
    artinianPolynomialIdealPowerDegreeSubmodule_eq_bot I weight shift degree he]
  exact inf_bot_eq _

theorem artinianPolynomialInducedDegreeFiltration_succ_le (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    artinianPolynomialInducedDegreeFiltration I N weight shift degree (i + 1) ≤
      artinianPolynomialInducedDegreeFiltration I N weight shift degree i :=
  inf_le_inf_left _
    (artinianPolynomialIdealPowerDegreeSubmodule_succ_le I weight shift degree i)

/-- Multiplication by the coefficient ideal advances the inherited
polynomial filtration on each fixed ordinary degree. -/
theorem artinianPolynomialInducedDegreeFiltration_smul_le (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ) (i : ℕ) :
    I • artinianPolynomialInducedDegreeFiltration I N weight shift degree i ≤
      artinianPolynomialInducedDegreeFiltration I N weight shift degree (i + 1) := by
  apply Submodule.smul_le.mpr
  intro a ha x hx
  refine ⟨(artinianPolynomialSubmoduleDegree N weight shift degree).smul_mem a hx.1, ?_⟩
  have haC : MvPolynomial.C a ∈ artinianPolynomialCoefficientIdeal (n := n) I :=
    Ideal.mem_map_of_mem MvPolynomial.C ha
  have hs : MvPolynomial.C (σ := Fin n) a •
      ((x : artinianPolynomialModulePiece (B := B) weight shift degree) :
        artinianFreePolynomialModule B n r) ∈
      artinianPolynomialIdealPowerSubmodule I (i + 1) := by
    rw [artinianPolynomialIdealPowerSubmodule_succ]
    exact Submodule.smul_mem_smul haC hx.2
  change ((a • x : artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) ∈
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1)
  change a • ((x : artinianPolynomialModulePiece (B := B) weight shift degree) :
      artinianFreePolynomialModule B n r) ∈
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1)
  simpa only [MvPolynomial.C_eq_algebraMap, algebraMap_smul] using hs

/-- For every original homogeneous degree, the sum of the dimensions of all
induced layers over the actual residue field equals the length of that degree
piece.  Only the sum is controlled; individual summands may vary with `N`. -/
theorem artinianPolynomialSubmoduleDegree_length_eq_sum_layer_finranks
    [IsArtinianRing B] (I : Ideal B) [I.IsMaximal]
    (N : Submodule (MvPolynomial (Fin n) B) (artinianFreePolynomialModule B n r))
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (degree : ℤ) {e : ℕ} (he : I ^ e = ⊥) :
    Module.length B (artinianPolynomialSubmoduleDegree N weight shift degree) =
      ∑ i ∈ Finset.range e,
        (submoduleLayerResidueFinrank I
          (artinianPolynomialInducedDegreeFiltration I N weight shift degree i)
          (artinianPolynomialInducedDegreeFiltration I N weight shift degree (i + 1))
          (artinianPolynomialInducedDegreeFiltration_smul_le
            I N weight shift degree i) : ℕ∞) := by
  let _ : Module.Finite B (artinianPolynomialModulePiece (B := B) weight shift degree) :=
    artinianPolynomialModulePiece_moduleFinite weight hweight shift degree
  let _ : IsNoetherian B (artinianPolynomialModulePiece (B := B) weight shift degree) :=
    inferInstance
  have h := submodule_length_eq_sum_residue_finrank_of_filtration I
    (fun i => artinianPolynomialInducedDegreeFiltration I N weight shift degree i)
    (fun i => artinianPolynomialInducedDegreeFiltration_succ_le
      I N weight shift degree i)
    (fun i => artinianPolynomialInducedDegreeFiltration_smul_le
      I N weight shift degree i)
    (artinianPolynomialInducedDegreeFiltration_eq_bot
      I N weight shift degree he)
  rw [artinianPolynomialInducedDegreeFiltration_zero] at h
  exact h

/-- A single nilpotence exponent works for all polynomial submodules and all
ordinary degrees over an Artinian local coefficient ring. -/
theorem exists_artinianPolynomialSubmoduleDegree_length_eq_sum_layer_finranks
    [IsLocalRing B] [IsArtinianRing B]
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i) (shift : Fin r → ℤ) :
    ∃ e : ℕ, IsLocalRing.maximalIdeal B ^ e = ⊥ ∧
      ∀ (N : Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r)) (degree : ℤ),
        Module.length B (artinianPolynomialSubmoduleDegree N weight shift degree) =
          ∑ i ∈ Finset.range e,
            (submoduleLayerResidueFinrank (IsLocalRing.maximalIdeal B)
              (artinianPolynomialInducedDegreeFiltration
                (IsLocalRing.maximalIdeal B) N weight shift degree i)
              (artinianPolynomialInducedDegreeFiltration
                (IsLocalRing.maximalIdeal B) N weight shift degree (i + 1))
              (artinianPolynomialInducedDegreeFiltration_smul_le
                (IsLocalRing.maximalIdeal B) N weight shift degree i) : ℕ∞) := by
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_bot_for_layers (R := B)
  refine ⟨e, he, ?_⟩
  intro N degree
  exact artinianPolynomialSubmoduleDegree_length_eq_sum_layer_finranks
    (IsLocalRing.maximalIdeal B) N weight hweight shift degree he

/-!
The remaining integration step is grading compatibility.  For a homogeneous
`N`, one must identify the degree-`d` part of each full polynomial layer with
the quotient of the two degree filtrations above.  Combining those
identifications over `i < e` turns `artinianPolynomialInducedLayerSumMap` into
the degreewise embedding whose source dimension is computed by
`artinianPolynomialSubmoduleDegree_length_eq_sum_layer_finranks`.

For the field-case monomial argument one also needs a fixed finite free cover
of `artinianPolynomialAmbientLayerSum`; equivalently, identify its `i`th term
with a finite free module over `(B/I)[z]` after choosing a basis of the finite
residue-vector-space layer `I^i / I^(i+1)`.  This requires only a vector-space
basis in the quotient layer.  It does not require a ring section `B/I → B`.

To reuse the finite-descent recurrence, a filtration-preserving `B[z]`-linear
operator must next be descended to these layers, and weighted initial
formation must be shown compatible with their induced grading.  A generator
degree bound on the layer sum then lifts through the finite filtration by
choosing representatives of finitely many quotient classes and inducting on
the filtration index; this also needs no multiplicative choice of coefficient
representatives.
-/

end PolynomialGradingBridge

end AbelFormalization
