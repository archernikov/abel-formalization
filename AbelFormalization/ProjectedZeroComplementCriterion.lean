import AbelFormalization.ProjectedZeroMatrixSections
import AbelFormalization.ProjectedZeroPolynomialSigns
import AbelFormalization.ProjectedZeroDefinabilityBridge
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection

/-!
# Projected-zero inputs to the theorem of the complement

This file assembles the parts of the Karpinski--Macintyre/Wilkie route that
follow from mathlib and the project's existing projected-zero results.

It proves the missing passage from matrix sections to arbitrary affine
subspaces (the literal W5 condition), packages W1--W6 and the all-orders DC
condition, and gives a first-order endpoint for the ambient o-minimal closure
produced by a theorem of the complement.

The ambient closure is intentionally not identified with the original class
of projected zero sets.  The cited complement theorem proves closure under
complement only in that ambient Charbonnel closure; obtaining
`HasProjectedZeroComplements G` requires the additional reflection property
made explicit at the end of this file.
-/

noncomputable section

open Set Function
open FirstOrder FirstOrder.Language
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

def flatSquareMatrixOfLinearMap {n : ℕ}
    (L : RealEuclidean n →ₗ[ℝ] RealEuclidean n) : FlatSquareMatrix n :=
  fun k ↦
    let ij := finProdFinEquiv.symm k
    L (Pi.single ij.2 1) ij.1

@[simp]
theorem flatSquareMatrixEntry_ofLinearMap {n : ℕ}
    (L : RealEuclidean n →ₗ[ℝ] RealEuclidean n) (i j : Fin n) :
    flatSquareMatrixEntry (flatSquareMatrixOfLinearMap L) i j =
      L (Pi.single j 1) i := by
  simp [flatSquareMatrixEntry, flatSquareMatrixOfLinearMap]

theorem flatSquareMatrixMulVec_ofLinearMap {n : ℕ}
    (L : RealEuclidean n →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean n) :
    flatSquareMatrixMulVec (flatSquareMatrixOfLinearMap L) x = L x := by
  funext i
  rw [← Finset.univ_sum_single x]
  simp only [map_sum, Finset.sum_apply, flatSquareMatrixMulVec,
    flatSquareMatrixEntry_ofLinearMap]
  apply Finset.sum_congr rfl
  intro j _
  have hsingle : Pi.single j (x j) = x j • Pi.single j (1 : ℝ) := by
    ext k
    by_cases hkj : k = j
    · simp [hkj]
    · simp [hkj]
  rw [hsingle]
  simp [mul_comm]

/-- Every affine subspace of a positive-dimensional coordinate space is the
solution set of one square matrix equation.  Allowing dependent and zero rows
lets a square matrix encode affine subspaces of every codimension. -/
theorem exists_flatSquareMatrix_eq_affineSubspace {n : ℕ} (hn : 0 < n)
    (V : AffineSubspace ℝ (RealEuclidean n)) :
    ∃ (M : FlatSquareMatrix n) (b : RealEuclidean n),
      {x | flatSquareMatrixMulVec M x = b} = (V : Set (RealEuclidean n)) := by
  rcases V.eq_bot_or_nonempty with hV | ⟨p, hp⟩
  · subst V
    let i : Fin n := ⟨0, hn⟩
    refine ⟨0, Pi.single i 1, ?_⟩
    ext x
    change flatSquareMatrixMulVec 0 x = Pi.single i 1 ↔ False
    constructor
    · intro h
      have hi := congrFun h i
      simp [flatSquareMatrixMulVec, flatSquareMatrixEntry, i] at hi
    · exact False.elim
  · let S : Submodule ℝ (RealEuclidean n) := V.direction
    obtain ⟨T, hST⟩ := S.exists_isCompl
    let L : RealEuclidean n →ₗ[ℝ] RealEuclidean n :=
      T.projection S hST.symm
    refine ⟨flatSquareMatrixOfLinearMap L, L p, ?_⟩
    ext x
    rw [Set.mem_ofPred_eq, flatSquareMatrixMulVec_ofLinearMap]
    have hker : LinearMap.ker L = S := by
      exact Submodule.ker_projection hST.symm
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hker]
    exact AffineSubspace.vsub_right_mem_direction_iff_mem hp x

/-- The matrix-section form already proved from UFF implies the literal W5
bound over every affine subspace. -/
theorem IsProjectedZeroSet.exists_affineSubspace_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : IsProjectedZeroSet G A) :
    ∃ N : ℕ, ∀ V : AffineSubspace ℝ (RealEuclidean n),
      ENat.card (ConnectedComponents
        ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))) ≤ N := by
  obtain ⟨N, hN⟩ := hA.exists_matrixSection_component_bound hG hUFF
  refine ⟨N, fun V ↦ ?_⟩
  obtain ⟨M, b, hV⟩ := exists_flatSquareMatrix_eq_affineSubspace hn V
  rw [← hV]
  exact hN M b

/-! ## W1--W6 and DC certificates -/

/-- The literal affine-section form of condition W5 for projected zero sets.
The positivity restriction matches the manuscript, whose set families start
in dimension one. -/
def HasProjectedZeroAffineSectionBounds
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ A : Set (RealEuclidean n),
    IsProjectedZeroSet G A →
      ∃ N : ℕ, ∀ V : AffineSubspace ℝ (RealEuclidean n),
        ENat.card (ConnectedComponents
          ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))) ≤ N

/-- The DC^N-for-all-N certificate used by the complement theorem.  This is
slightly stronger than the source definition: one fixed globally smooth
family member represents the set at every differentiability order. -/
def HasProjectedZeroDCAllOrders
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ (n : ℕ) (A : Set (RealEuclidean n)), IsProjectedZeroSet G A →
    ∃ (q : ℕ) (f : RealEuclideanFunction (n + q)),
      f ∈ G (n + q) ∧
      (∀ N : ℕ, ContDiff ℝ N f) ∧
      IsProjectedZeroSet G (realEuclideanGraph f) ∧
      A = {x | ∃ z : RealEuclidean q,
        f (realEuclideanAppend x z) = 0}

/-- All mathlib-level hypotheses of the Karpinski--Macintyre/Wilkie route for
the projected-zero family.  `w2_polynomialSign` is the explicit polynomial
sign normal form available in this development; it is the exact syntax used
by the manuscript's elementary semialgebraic argument.  W4 is strengthened
from coordinate permutations to arbitrary linear equivalences. -/
structure ProjectedZeroWeakStructureCertificate
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop where
  w1_inter : ∀ {n : ℕ} {A B : Set (RealEuclidean n)},
    IsProjectedZeroSet G A → IsProjectedZeroSet G B →
      IsProjectedZeroSet G (A ∩ B)
  w2_polynomialSign : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
    PolynomialSignConstructible n A → IsProjectedZeroSet G A
  w3_prod : ∀ {n m : ℕ} {A : Set (RealEuclidean n)}
    {B : Set (RealEuclidean m)},
    IsProjectedZeroSet G A → IsProjectedZeroSet G B →
      IsProjectedZeroSet G (realEuclideanSetProduct A B)
  w4_linearEquiv : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
    IsProjectedZeroSet G A →
      ∀ e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n,
        IsProjectedZeroSet G (e '' A)
  w5_affineSections : HasProjectedZeroAffineSectionBounds G
  w6_closedLift : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
    IsProjectedZeroSet G A → HasClosedProjectedZeroLift G A
  dc_allOrders : HasProjectedZeroDCAllOrders G

/-- A smooth geometric family with UFF satisfies every formalized W1--W6/DC
obligation for its projected-zero family.  The complement theorem itself is
the remaining external theorem. -/
theorem projectedZeroWeakStructureCertificate
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    ProjectedZeroWeakStructureCertificate G := by
  constructor
  · intro n A B hA hB
    exact hA.inter hG hB
  · intro n A hA
    exact hA.isProjectedZeroSet hG
  · intro n m A B hA hB
    exact hA.prod hG hB
  · intro n A hA e
    exact hA.linearEquiv_image hG e
  · intro n hn A hA
    exact hA.exists_affineSubspace_component_bound hG hUFF hn
  · intro n A hA
    exact hA.hasClosedLift hsmooth
  · intro n A hA
    obtain ⟨q, f, hf, hAf⟩ := hA
    refine ⟨q, f, hf, ?_, hG.isProjectedZeroSet_graph hf, hAf⟩
    intro N
    exact (hsmooth (n + q) f hf).of_le (by simp)

/-- Abel-family specialization: after UFF, every W1--W6/DC input to the
complement theorem is available without any further geometric assumption. -/
theorem IsAbel.projectedZeroWeakStructureCertificate
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    ProjectedZeroWeakStructureCertificate (abelGeometricFamily A) :=
  AbelFormalization.projectedZeroWeakStructureCertificate
    (isGeometricFunctionFamily_abelGeometricFamily A)
    hA.isEverywhereSmooth_abelGeometricFamily hUFF

/-! ## The actual output needed from the theorem of the complement -/

/-- A Boolean, projection-closed ambient family containing all projected zero
sets, together with the unary finiteness conclusion of the complement theorem.

The Karpinski--Macintyre/Wilkie theorem produces such an ambient closure.  It
does not assert that complements return to the original projected-zero class,
so this is deliberately distinct from `HasProjectedZeroComplements`. -/
structure ProjectedZeroComplementEnvelope
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) where
  sets : (n : ℕ) → Set (Set (RealEuclidean n))
  projectedZero_mem : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
    IsProjectedZeroSet G A → A ∈ sets n
  empty_mem : ∀ n : ℕ, (∅ : Set (RealEuclidean n)) ∈ sets n
  union_mem : ∀ {n : ℕ} {A B : Set (RealEuclidean n)},
    A ∈ sets n → B ∈ sets n → A ∪ B ∈ sets n
  compl_mem : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
    A ∈ sets n → Aᶜ ∈ sets n
  linearEquiv_image_mem : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
    A ∈ sets n → ∀ e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n,
      e '' A ∈ sets n
  existentialProjection_mem : ∀ {n m : ℕ}
    {A : Set (RealEuclidean (n + m))},
    A ∈ sets (n + m) → realEuclideanExistentialProjection A ∈ sets n
  unary_component_bound : ∀ {A : Set (RealEuclidean 1)}, A ∈ sets 1 →
    ∃ N : ℕ, ENat.card (ConnectedComponents A) ≤ N

/-- The exact external implication needed from the theorem of the complement:
the formalized weak-structure/DC certificate produces a Boolean,
projection-closed ambient family with finite unary component counts.  This is
a proposition recording the remaining input, not a claimed mathlib theorem. -/
def ProjectedZeroComplementPrinciple : Prop :=
  ∀ G : (n : ℕ) → Set (RealEuclideanFunction n),
    ProjectedZeroWeakStructureCertificate G →
      Nonempty (ProjectedZeroComplementEnvelope G)

/-- The stronger principle that would be needed to prove complement closure
of the *original* projected-zero family.  The reflection clause is additional
to the ambient conclusion of Karpinski--Macintyre. -/
def ProjectedZeroReflectingComplementPrinciple : Prop :=
  ∀ G : (n : ℕ) → Set (RealEuclideanFunction n),
    ProjectedZeroWeakStructureCertificate G →
      ∃ E : ProjectedZeroComplementEnvelope G,
        ∀ {n : ℕ} {A : Set (RealEuclidean n)},
          A ∈ E.sets n → IsProjectedZeroSet G A

/-- An ambient Boolean family is closed under universal coordinate
projection by the usual complement--existential--complement identity. -/
theorem ProjectedZeroComplementEnvelope.universalProjection_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (E : ProjectedZeroComplementEnvelope G)
    {n m : ℕ} {A : Set (RealEuclidean (n + m))}
    (hA : A ∈ E.sets (n + m)) :
    realEuclideanUniversalProjection A ∈ E.sets n := by
  have hcompl : Aᶜ ∈ E.sets (n + m) := E.compl_mem hA
  have hproj : realEuclideanExistentialProjection Aᶜ ∈ E.sets n :=
    E.existentialProjection_mem hcompl
  have hresult : (realEuclideanExistentialProjection Aᶜ)ᶜ ∈ E.sets n :=
    E.compl_mem hproj
  convert hresult using 1
  ext x
  simp [realEuclideanUniversalProjection,
    realEuclideanExistentialProjection]

/-- Universal projection in mathlib's snoc-bounded-formula bracketing is also
available in every complement envelope. -/
theorem ProjectedZeroComplementEnvelope.universalBoundProjection_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (E : ProjectedZeroComplementEnvelope G)
    {n l : ℕ} {A : Set (RealEuclidean (n + (l + 1)))}
    (hA : A ∈ E.sets (n + (l + 1))) :
    realEuclideanUniversalBoundProjection A ∈ E.sets (n + l) := by
  let e := realEuclideanAssociateLeftLinearEquiv n l 1
  have himage : e '' A ∈ E.sets ((n + l) + 1) :=
    E.linearEquiv_image_mem hA e
  have hproj := E.universalProjection_mem himage
  convert hproj using 1
  ext v
  simp only [realEuclideanUniversalBoundProjection,
    realEuclideanUniversalProjection, Set.mem_ofPred_eq]
  constructor
  · intro h z
    refine ⟨realEuclideanSnocBound v (z 0), h (z 0), ?_⟩
    change realEuclideanAssociateLeftLinearMap n l 1
        (realEuclideanSnocBound v (z 0)) = realEuclideanAppend v z
    rw [show realEuclideanSnocBound v (z 0) =
        realEuclideanAppend (realEuclideanTakeLeft v)
          (realEuclideanAppend (realEuclideanTakeRight v) z) by
      apply congrArg (realEuclideanAppend (realEuclideanTakeLeft v))
      apply congrArg (realEuclideanAppend (realEuclideanTakeRight v))
      funext i
      exact Fin.eq_zero i ▸ rfl]
    rw [realEuclideanAssociateLeftLinearMap_append,
      realEuclideanAppend_takeLeft_takeRight]
  · intro h a
    obtain ⟨w, hw, hew⟩ := h (fun _ : Fin 1 ↦ a)
    have hwEq : w = realEuclideanSnocBound v a := by
      apply e.injective
      rw [hew]
      change realEuclideanAppend v (fun _ : Fin 1 ↦ a) =
        realEuclideanAssociateLeftLinearMap n l 1
          (realEuclideanSnocBound v a)
      rw [show realEuclideanSnocBound v a =
          realEuclideanAppend (realEuclideanTakeLeft v)
            (realEuclideanAppend (realEuclideanTakeRight v)
              (fun _ : Fin 1 ↦ a)) by rfl,
        realEuclideanAssociateLeftLinearMap_append,
        realEuclideanAppend_takeLeft_takeRight]
    rwa [← hwEq]

/-- Abel bounded-formula semantics belongs to any complement envelope of the
Abel projected-zero family.  Atomic formulas use the existing term-graph
compiler; implication and quantification use the ambient closure operations. -/
theorem ProjectedZeroComplementEnvelope.abelBoundedFormula_mem
    {A : ℝ → ℝ}
    (E : ProjectedZeroComplementEnvelope (abelGeometricFamily A))
    {n l : ℕ}
    (φ : abelLanguage[[(Set.univ : Set ℝ)]].BoundedFormula (Fin n) l) :
    abelBoundedFormulaRealizationSet A φ ∈ E.sets (n + l) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  let hatomic := hasProjectedZeroAbelAtomicSemantics A
  induction φ with
  | @falsum l =>
      simpa [abelBoundedFormulaRealizationSet,
        FirstOrder.Language.BoundedFormula.Realize] using
        E.empty_mem (n + l)
  | @equal l t₁ t₂ =>
      exact E.projectedZero_mem (hatomic.equal t₁ t₂)
  | @rel l k R ts =>
      exact E.projectedZero_mem (hatomic.rel R ts)
  | @imp l φ ψ ihφ ihψ =>
      have hnot := E.compl_mem ihφ
      have hor := E.union_mem hnot ihψ
      convert hor using 1
      ext v
      simp only [abelBoundedFormulaRealizationSet, Set.mem_union,
        Set.mem_compl_iff, Set.mem_ofPred_eq,
        FirstOrder.Language.BoundedFormula.realize_imp]
      constructor
      · intro h
        by_cases hp : φ.Realize (realEuclideanTakeLeft v)
            (realEuclideanTakeRight v)
        · exact Or.inr (h hp)
        · exact Or.inl hp
      · rintro (hp | hq) hφ
        · exact (hp hφ).elim
        · exact hq
  | @all l φ ih =>
      have hproj := E.universalBoundProjection_mem ih
      convert hproj using 1
      ext v
      simp only [abelBoundedFormulaRealizationSet,
        realEuclideanUniversalBoundProjection, Set.mem_ofPred_eq,
        FirstOrder.Language.BoundedFormula.realize_all]
      constructor
      · intro h a
        simpa using h a
      · intro h a
        simpa using h a

/-- The manuscript's complement-theorem output is already enough for the
project's exact o-minimality conclusion; complement closure of the original
projected-zero class is unnecessary. -/
theorem ProjectedZeroComplementEnvelope.oMinimal
    {A : ℝ → ℝ}
    (E : ProjectedZeroComplementEnvelope (abelGeometricFamily A)) :
    OMinimal A := by
  intro s hs
  let _ : abelLanguage.Structure ℝ := abelStructure A
  change (Set.univ : Set ℝ).Definable abelLanguage
      {v : Fin 1 → ℝ | v 0 ∈ s} at hs
  rcases hs with ⟨φ, hφ⟩
  have hmem := E.abelBoundedFormula_mem φ
  have hset : abelBoundedFormulaRealizationSet A φ =
      {v : RealEuclidean 1 | v 0 ∈ s} := by
    rw [hφ]
    ext v
    simp only [Set.mem_ofPred_eq, abelBoundedFormulaRealizationSet]
    have hleft : realEuclideanTakeLeft (n := 1) (m := 0) v = v := by
      funext i
      simp [realEuclideanTakeLeft]
    rw [hleft]
    simp only [FirstOrder.Language.Formula.Realize]
    rw [show (@default (Fin 0 → ℝ) Unique.instInhabited) =
        realEuclideanTakeRight (n := 1) (m := 0) v from
      Subsingleton.elim _ _]
  rw [hset] at hmem
  obtain ⟨N, hN⟩ := E.unary_component_bound hmem
  have hcoordCard :
      ENat.card (ConnectedComponents
        (realEuclideanOneCoordinateImage
          {v : RealEuclidean 1 | v 0 ∈ s})) ≤ N :=
    (enatCard_connectedComponents_le_of_continuous_surjective
      (continuous_realEuclideanOneToCoordinateImage
        {v : RealEuclidean 1 | v 0 ∈ s})
      (surjective_realEuclideanOneToCoordinateImage
        {v : RealEuclidean 1 | v 0 ∈ s})).trans hN
  have hpieces := unaryPieceDecomposable_of_enatCard_connectedComponents_le
    (realEuclideanOneCoordinateImage
      {v : RealEuclidean 1 | v 0 ∈ s}) N hcoordCard
  have himage : realEuclideanOneCoordinateImage
      {v : RealEuclidean 1 | v 0 ∈ s} = s := by
    ext x
    simp only [realEuclideanOneCoordinateImage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨fun _ ↦ x, hx, rfl⟩
  rwa [himage] at hpieces

/-- With the actual ambient conclusion of the complement theorem supplied,
the formalized W1--W6/DC certificate proves o-minimality of the Abel
expansion.  This follows the manuscript's reduct route and does not require
complement closure of the original projected-zero family. -/
theorem IsAbel.oMinimal_of_projectedZeroComplementPrinciple
    (hcomplement : ProjectedZeroComplementPrinciple)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨E⟩ := hcomplement (abelGeometricFamily A)
    (hA.projectedZeroWeakStructureCertificate hUFF)
  exact E.oMinimal

/-- An ambient complement envelope yields complement closure of projected zero
sets exactly when membership in the envelope reflects back to projected-zero
membership.  This extra reflection is not a conclusion of the cited theorem
of the complement. -/
theorem ProjectedZeroComplementEnvelope.hasProjectedZeroComplements
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (E : ProjectedZeroComplementEnvelope G)
    (hreflect : ∀ {n : ℕ} {A : Set (RealEuclidean n)},
      A ∈ E.sets n → IsProjectedZeroSet G A) :
    HasProjectedZeroComplements G := by
  intro n A hA
  exact hreflect (E.compl_mem (E.projectedZero_mem hA))

/-- The literal projected-zero complement target follows from the explicitly
stronger reflecting principle.  Keeping this separate records precisely the
extra statement that is absent from the manuscript's ambient-closure route. -/
theorem IsAbel.hasProjectedZeroComplements_of_reflectingComplementPrinciple
    (hcomplement : ProjectedZeroReflectingComplementPrinciple)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    HasProjectedZeroComplements (abelGeometricFamily A) := by
  obtain ⟨E, hreflect⟩ := hcomplement (abelGeometricFamily A)
    (hA.projectedZeroWeakStructureCertificate hUFF)
  exact E.hasProjectedZeroComplements hreflect

end AbelFormalization
