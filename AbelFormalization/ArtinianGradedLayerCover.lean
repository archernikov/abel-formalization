import AbelFormalization.ArtinianHomogeneousLayerSpan
import AbelFormalization.ArtinianLayerComponents

set_option autoImplicit false

/-!
# A graded finite free cover of the Artinian ambient layer sum

The coefficient generators chosen for each ideal power give constant
generators in every ambient quotient layer.  This file assembles those
families over a fixed finite cutoff, reindexes the resulting dependent finite
type by `Fin`, and forms the corresponding `Fintype.linearCombination` map
over the residue polynomial ring.

The only comparison of the original and pushed-forward scalar actions comes
from `submoduleLayerPushforwardSemilinearMap`.  In particular, no section of
the coefficient quotient map is chosen.
-/

noncomputable section

namespace AbelFormalization

open Function

/-! ## Scalar compatibility for the pushed-forward quotient action -/

/-- On a pushed-forward quotient layer, a scalar in the image of the
surjective ring map acts exactly as its chosen source scalar did before the
pushforward.  This is the `map_smul` identity of the identity semilinear map,
not a choice of a section of `q`. -/
theorem submoduleLayerPushforward_smul_eq_original
    {A C W : Type*} [CommRing A] [CommRing C] [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q) (F G : Submodule A W)
    (hker : RingHom.ker q • F ≤ G) (a : A) (x : submoduleLayer F G) :
    letI := submoduleLayerPushforwardModule q hq F G hker
    q a • x = a • x := by
  let _ := submoduleLayerPushforwardModule q hq F G hker
  exact
    ((submoduleLayerPushforwardSemilinearMap q hq F G hker).map_smulₛₗ a x).symm

section PolynomialLayers

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- The scalar compatibility identity specialized to an ambient polynomial
ideal-power layer. -/
theorem artinianPolynomialAmbientLayer_residue_smul_eq_original
    (I : Ideal B) (i : ℕ) (a : MvPolynomial (Fin n) B)
    (x : artinianPolynomialAmbientLayer (n := n) (r := r) I i) :
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    artinianPolynomialResidueMap (n := n) I a • x = a • x := by
  let _ := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
  exact submoduleLayerPushforward_smul_eq_original
    (artinianPolynomialResidueMap (n := n) I)
    (artinianPolynomialResidueMap_surjective (n := n) I)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i)
    (artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I (i + 1))
    (artinianPolynomialAmbientLayer_annihilation
      (n := n) (r := r) I i) a x

/-! ## One ambient layer -/

/-- The constant quotient generators span one ambient layer over the actual
residue polynomial ring. -/
theorem artinianPolynomialAmbientLayerConstantGenerator_span_eq_top
    [IsNoetherianRing B] (I : Ideal B) (i : ℕ) :
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
      (Set.range (fun ks :
          Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
        artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i ks.1 ks.2)) = ⊤ := by
  classical
  let _ := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
  apply top_unique
  intro x hx
  refine Submodule.Quotient.induction_on _ x ?_
  intro P
  have hP :
      (P : artinianFreePolynomialModule B n r) ∈
        Submodule.span (MvPolynomial (Fin n) B)
          (Set.range (fun ks :
              Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
            artinianPolynomialIdealPowerConstantGenerator
              (n := n) (r := r) I i ks.1 ks.2)) := by
    rw [← artinianPolynomialIdealPowerSubmodule_eq_span_constants
      (n := n) (r := r) I i]
    exact P.property
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R := MvPolynomial (Fin n) B)).mp hP
  have hcsub :
      (∑ ks,
        c ks •
          (⟨artinianPolynomialIdealPowerConstantGenerator
              (n := n) (r := r) I i ks.1 ks.2,
            artinianPolynomialIdealPowerConstantGenerator_mem
              (n := n) (r := r) I i ks.1 ks.2⟩ :
            artinianPolynomialIdealPowerSubmodule
              (n := n) (r := r) I i)) = P := by
    apply Subtype.ext
    simpa using hc
  have hquot :
      (∑ ks,
        c ks • artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i ks.1 ks.2) =
        Submodule.Quotient.mk P := by
    have hm := congrArg
      ((artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)).comap
        (artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype).mkQ hcsub
    simpa only [map_sum, map_smul, Submodule.mkQ_apply,
      artinianPolynomialAmbientLayerConstantGenerator] using hm
  have hresidue :
      (∑ ks,
        artinianPolynomialResidueMap (n := n) I (c ks) •
          artinianPolynomialAmbientLayerConstantGenerator
            (n := n) (r := r) I i ks.1 ks.2) =
        ∑ ks,
          c ks • artinianPolynomialAmbientLayerConstantGenerator
            (n := n) (r := r) I i ks.1 ks.2 := by
    apply Finset.sum_congr rfl
    intro ks hks
    exact artinianPolynomialAmbientLayer_residue_smul_eq_original
      (n := n) (r := r) I i (c ks)
        (artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i ks.1 ks.2)
  rw [← hquot, ← hresidue]
  apply Submodule.sum_mem
  intro ks hks
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self ks))

/-- The finite linear-combination map supplied by the constant generators in
one ambient layer. -/
def artinianPolynomialAmbientLayerConstantCover
    [IsNoetherianRing B] (I : Ideal B) (i : ℕ) :
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    (Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank →
        MvPolynomial (Fin n) (B ⧸ I)) →ₗ[MvPolynomial (Fin n) (B ⧸ I)]
      artinianPolynomialAmbientLayer (n := n) (r := r) I i := by
  let _ := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
  exact Fintype.linearCombination (MvPolynomial (Fin n) (B ⧸ I))
    (fun ks : Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
      artinianPolynomialAmbientLayerConstantGenerator
        (n := n) (r := r) I i ks.1 ks.2)

/-- The constant linear-combination map onto one ambient layer is
surjective. -/
theorem artinianPolynomialAmbientLayerConstantCover_surjective
    [IsNoetherianRing B] (I : Ideal B) (i : ℕ) :
    letI := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
    Function.Surjective
      (artinianPolynomialAmbientLayerConstantCover
        (n := n) (r := r) I i) := by
  let _ := artinianPolynomialAmbientLayerModule (n := n) (r := r) I i
  change Function.Surjective
    (Fintype.linearCombination (MvPolynomial (Fin n) (B ⧸ I))
      (fun ks : Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
        artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i ks.1 ks.2))
  exact
    (span_range_eq_top_iff_surjective_fintypeLinearCombination
      (R := MvPolynomial (Fin n) (B ⧸ I))
      (v := fun ks :
          Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
        artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i ks.1 ks.2)).mp
      (artinianPolynomialAmbientLayerConstantGenerator_span_eq_top
        (n := n) (r := r) I i)

/-! ## The dependent finite generator type -/

/-- Before reindexing, a generator records its layer, its original free
coordinate, and its chosen coefficient-ideal generator. -/
abbrev artinianPolynomialAmbientLayerRawGeneratorIndex
    [IsNoetherianRing B] (I : Ideal B) (e r : ℕ) :=
  Σ i : Fin e,
    Fin r × Fin (artinianIdealPowerFiniteFreeCover I i.1).rank

/-- The number of constant generators in all ambient layers below the fixed
cutoff. -/
def artinianPolynomialAmbientLayerGradedCoverRank
    [IsNoetherianRing B] (I : Ideal B) (e r : ℕ) : ℕ :=
  Fintype.card (artinianPolynomialAmbientLayerRawGeneratorIndex I e r)

/-- A fixed reindexing of the dependent generator type by `Fin`. -/
def artinianPolynomialAmbientLayerRawGeneratorEquivFin
    [IsNoetherianRing B] (I : Ideal B) (e r : ℕ) :
    artinianPolynomialAmbientLayerRawGeneratorIndex I e r ≃
      Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) :=
  Fintype.equivFin _

/-- Insert one layer's constant generator into the corresponding coordinate
of the finite ambient layer sum. -/
def artinianPolynomialAmbientLayerSumRawGenerator
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ)
    (g : artinianPolynomialAmbientLayerRawGeneratorIndex I e r) :
    artinianPolynomialAmbientLayerSum (n := n) (r := r) I e :=
  Pi.single g.1
    (artinianPolynomialAmbientLayerConstantGenerator
      (n := n) (r := r) I g.1.1 g.2.1 g.2.2)

/-- The original free-coordinate shift inherited by a raw constant
generator.  The layer and coefficient-generator indices contribute no
additional shift. -/
def artinianPolynomialAmbientLayerSumRawGeneratorShift
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ)
    (shift : Fin r → ℤ)
    (g : artinianPolynomialAmbientLayerRawGeneratorIndex I e r) : ℤ :=
  shift g.2.1

/-- The constant generator family after reindexing by `Fin`. -/
def artinianPolynomialAmbientLayerSumGradedGenerator
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ)
    (j : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r)) :
    artinianPolynomialAmbientLayerSum (n := n) (r := r) I e :=
  artinianPolynomialAmbientLayerSumRawGenerator (n := n) I e
    ((artinianPolynomialAmbientLayerRawGeneratorEquivFin I e r).symm j)

/-- The inherited shift of a `Fin`-reindexed generator. -/
def artinianPolynomialAmbientLayerSumGradedGeneratorShift
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ)
    (shift : Fin r → ℤ)
    (j : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r)) : ℤ :=
  artinianPolynomialAmbientLayerSumRawGeneratorShift I e shift
    ((artinianPolynomialAmbientLayerRawGeneratorEquivFin I e r).symm j)

/-! ## Homogeneity of the distinguished generators -/

/-- Weighted projection to the inherited shift fixes a constant generator in
one ambient quotient layer. -/
theorem artinianPolynomialAmbientLayerComponent_constantGenerator
    [IsNoetherianRing B]
    (I : Ideal B) (i : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (k : Fin r) (s : Fin (artinianIdealPowerFiniteFreeCover I i).rank) :
    artinianPolynomialAmbientLayerComponent I i weight shift (shift k)
        (artinianPolynomialAmbientLayerConstantGenerator
          (n := n) (r := r) I i k s) =
      artinianPolynomialAmbientLayerConstantGenerator
        (n := n) (r := r) I i k s := by
  rw [artinianPolynomialAmbientLayerConstantGenerator,
    artinianPolynomialAmbientLayerComponent_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact artinianPolynomialModuleComponent_constantGenerator
    (n := n) (r := r) I i weight shift k s

/-- Pointwise weighted projection to a raw generator's inherited shift fixes
that generator in the ambient layer sum. -/
theorem artinianPolynomialAmbientLayerSumComponent_rawGenerator
    [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (g : artinianPolynomialAmbientLayerRawGeneratorIndex I e r) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift
        (artinianPolynomialAmbientLayerSumRawGeneratorShift I e shift g)
        (artinianPolynomialAmbientLayerSumRawGenerator (n := n) I e g) =
      artinianPolynomialAmbientLayerSumRawGenerator (n := n) I e g := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  rcases g with ⟨i, k, s⟩
  funext j
  by_cases hji : j = i
  · subst j
    simp only [artinianPolynomialAmbientLayerSumComponent_apply,
      artinianPolynomialAmbientLayerSumRawGeneratorShift,
      artinianPolynomialAmbientLayerSumRawGenerator, Pi.single_eq_same]
    exact artinianPolynomialAmbientLayerComponent_constantGenerator
      (n := n) (r := r) I i.1 weight shift k s
  · simp [artinianPolynomialAmbientLayerSumRawGeneratorShift,
      artinianPolynomialAmbientLayerSumRawGenerator, Pi.single_apply, hji]

/-- The same homogeneity statement for the `Fin`-reindexed generator
family. -/
theorem artinianPolynomialAmbientLayerSumComponent_gradedGenerator
    [IsNoetherianRing B]
    (I : Ideal B) (e : ℕ) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (j : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r)) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialAmbientLayerSumComponent I e weight shift
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift j)
        (artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) I e j) =
      artinianPolynomialAmbientLayerSumGradedGenerator (n := n) I e j := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  simpa [artinianPolynomialAmbientLayerSumGradedGeneratorShift,
    artinianPolynomialAmbientLayerSumGradedGenerator] using
    (artinianPolynomialAmbientLayerSumComponent_rawGenerator
      (n := n) (r := r) I e weight shift
      ((artinianPolynomialAmbientLayerRawGeneratorEquivFin I e r).symm j))

/-! ## Spanning the finite ambient layer sum -/

/-- The dependent raw family spans the whole finite product of ambient
layers. -/
theorem artinianPolynomialAmbientLayerSumRawGenerator_span_eq_top
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
      (Set.range
        (artinianPolynomialAmbientLayerSumRawGenerator
          (n := n) (r := r) I e)) = ⊤ := by
  classical
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let S : Submodule (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) :=
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
      (Set.range
        (artinianPolynomialAmbientLayerSumRawGenerator
          (n := n) (r := r) I e))
  apply top_unique
  intro x hx
  change x ∈ S
  refine Pi.single_induction (p := fun y => y ∈ S) x S.zero_mem
    (fun y z hy hz => S.add_mem hy hz) ?_
  intro i y
  have hy :
      y ∈ Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
        (Set.range (fun ks :
            Fin r × Fin (artinianIdealPowerFiniteFreeCover I i.1).rank =>
          artinianPolynomialAmbientLayerConstantGenerator
            (n := n) (r := r) I i.1 ks.1 ks.2)) := by
    rw [artinianPolynomialAmbientLayerConstantGenerator_span_eq_top
      (n := n) (r := r) I i.1]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun z _ => Pi.single i z ∈ S) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨ks, rfl⟩
    change artinianPolynomialAmbientLayerSumRawGenerator
      (n := n) (r := r) I e
        (⟨i, ks⟩ : artinianPolynomialAmbientLayerRawGeneratorIndex I e r) ∈ S
    exact Submodule.subset_span
      (R := MvPolynomial (Fin n) (B ⧸ I))
      (Set.mem_range_self
        (⟨i, ks⟩ :
          artinianPolynomialAmbientLayerRawGeneratorIndex I e r))
  · simpa using S.zero_mem
  · intro y z hy hz hy' hz'
    have hsingle :
        (Pi.single i (y + z) :
            artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) =
          Pi.single i y + Pi.single i z := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Pi.single_apply, hji]
    rw [hsingle]
    exact S.add_mem hy' hz'
  · intro a y hy hy'
    have hsingle :
        (Pi.single i (a • y) :
            artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) =
          a • Pi.single i y := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Pi.single_apply, hji]
    rw [hsingle]
    exact S.smul_mem a hy'

/-- Reindexing by `Fin` does not change the range of the generator family. -/
theorem artinianPolynomialAmbientLayerSumGradedGenerator_range
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ) :
    Set.range
        (artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) (r := r) I e) =
      Set.range
        (artinianPolynomialAmbientLayerSumRawGenerator
          (n := n) (r := r) I e) := by
  apply Set.Subset.antisymm
  · rintro x ⟨j, rfl⟩
    exact ⟨(artinianPolynomialAmbientLayerRawGeneratorEquivFin I e r).symm j,
      rfl⟩
  · rintro x ⟨g, rfl⟩
    refine ⟨artinianPolynomialAmbientLayerRawGeneratorEquivFin I e r g, ?_⟩
    simp [artinianPolynomialAmbientLayerSumGradedGenerator]

/-- The `Fin`-reindexed distinguished family spans the entire fixed ambient
layer sum. -/
theorem artinianPolynomialAmbientLayerSumGradedGenerator_span_eq_top
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
      (Set.range
        (artinianPolynomialAmbientLayerSumGradedGenerator
          (n := n) (r := r) I e)) = ⊤ := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  rw [artinianPolynomialAmbientLayerSumGradedGenerator_range
    (n := n) (r := r) I e]
  exact artinianPolynomialAmbientLayerSumRawGenerator_span_eq_top
    (n := n) (r := r) I e

/-! ## The graded residue-polynomial-linear cover -/

/-- Linear combination of the `Fin`-reindexed constant homogeneous
generators over the residue polynomial ring. -/
def artinianPolynomialAmbientLayerSumGradedCover
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)) →ₗ[MvPolynomial (Fin n) (B ⧸ I)]
      artinianPolynomialAmbientLayerSum (n := n) (r := r) I e := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact Fintype.linearCombination (MvPolynomial (Fin n) (B ⧸ I))
    (artinianPolynomialAmbientLayerSumGradedGenerator
      (n := n) (r := r) I e)

/-- The explicit constant homogeneous cover is onto. -/
theorem artinianPolynomialAmbientLayerSumGradedCover_surjective
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Function.Surjective
      (artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e) := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  change Function.Surjective
    (Fintype.linearCombination (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayerSumGradedGenerator
        (n := n) (r := r) I e))
  exact
    (span_range_eq_top_iff_surjective_fintypeLinearCombination
      (R := MvPolynomial (Fin n) (B ⧸ I))
      (v := artinianPolynomialAmbientLayerSumGradedGenerator
        (n := n) (r := r) I e)).mp
      (artinianPolynomialAmbientLayerSumGradedGenerator_span_eq_top
        (n := n) (r := r) I e)

/-- The graded linear-combination map, packaged as a finite free cover. -/
def artinianPolynomialAmbientLayerSumGradedFiniteFreeCover
    [IsNoetherianRing B] (I : Ideal B) (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    FiniteFreeCover (MvPolynomial (Fin n) (B ⧸ I))
      (artinianPolynomialAmbientLayerSum (n := n) (r := r) I e) := by
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  exact
    { rank := artinianPolynomialAmbientLayerGradedCoverRank I e r
      map := artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
      surjective := artinianPolynomialAmbientLayerSumGradedCover_surjective
        (n := n) (r := r) I e }

end PolynomialLayers

end AbelFormalization
