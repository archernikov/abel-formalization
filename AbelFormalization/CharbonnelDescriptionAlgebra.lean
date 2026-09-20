import AbelFormalization.CharbonnelWeakStructure
import Mathlib.Topology.Constructions

/-!
# Algebra of Charbonnel descriptions

This file formalizes the elementary description algebra used before the
approximation and boundary arguments in the theorem of the complement.  Its
main results are the product construction of Berarducci--Servi, with rank at
most the sum of the input ranks, and the resulting intersection construction,
with rank at most two plus that sum.

The product lemma in the source is a lemma for a *closed* W-structure: every
set in the base family is assumed to be topologically closed.  That hypothesis
is recorded explicitly below.  It is not a consequence of WS1--WS4 (or of the
semi-closed lift clause WS6), so none of the results in this file silently
deduces it from those interfaces.

Only coordinate reindexings are propagated through descriptions.  Although
the base WS4 interface is stated for arbitrary real-linear equivalences, an
arbitrary such equivalence need not preserve integer-affine sets.  Finite
coordinate bijections do preserve them and are precisely what the product
construction needs for block reassociation and block exchange.

No complement closure is asserted here.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## Closed base families and coordinate reindexing -/

/-- The additional hypothesis called "closed" for a W-structure in the
source: every positive-arity generator is a topologically closed set. -/
def IsClosedPositiveAritySetFamily (S : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {A : Set (RealEuclidean n)}, A ∈ S n → IsClosed A

/-- Reindex a finite real coordinate vector along a bijection of its coordinate
types.  The direction is chosen so that output coordinate `i` reads input
coordinate `e i`. -/
def realEuclideanCoordinateReindex {n m : ℕ} (e : Fin m ≃ Fin n) :
    RealEuclidean n ≃ₗ[ℝ] RealEuclidean m where
  toFun x i := x (e i)
  invFun y j := y (e.symm j)
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext i
    simp
  map_add' x y := by
    rfl
  map_smul' c x := by
    rfl

@[simp]
theorem realEuclideanCoordinateReindex_apply {n m : ℕ}
    (e : Fin m ≃ Fin n) (x : RealEuclidean n) (i : Fin m) :
    realEuclideanCoordinateReindex e x i = x (e i) :=
  rfl

/-- The part of a base-family structure needed to propagate finite coordinate
bijections through Charbonnel descriptions.  This deliberately mentions only
coordinate reindexing: arbitrary real-linear equivalences do not in general
preserve the integer-affine cuts occurring later in a description. -/
structure PositiveArityDescriptionReindexBase
    (S : EuclideanSetFamily) : Prop where
  coordinateReindex : ∀ {n m : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, A ∈ S n →
      ∀ e : Fin m ≃ Fin n,
        realEuclideanCoordinateReindex e '' A ∈ S m

/-- The exact base-family input used by the description product lemma: base
sets are closed, their flat products are again base sets, and finite
coordinate reindexings preserve the base family.  No semialgebraic or
complement clause is part of this interface. -/
structure ClosedPositiveArityDescriptionBase
    (S : EuclideanSetFamily) : Prop
    extends PositiveArityDescriptionReindexBase S where
  base_isClosed : IsClosedPositiveAritySetFamily S
  base_prod : ∀ {n m : ℕ}, 0 < n → 0 < m →
    ∀ {A : Set (RealEuclidean n)} {B : Set (RealEuclidean m)},
      A ∈ S n → B ∈ S m → realEuclideanSetProduct A B ∈ S (n + m)

/-- WS4 implies the smaller coordinate-reindexing interface. -/
theorem PositiveArityWeakSetStructure.toDescriptionReindexBase
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S) :
    PositiveArityDescriptionReindexBase S := by
  refine { coordinateReindex := ?_ }
  intro n m hn A hA e
  have hmn : m = n := by
    simpa using Fintype.card_congr e
  subst m
  exact hS.ws4_linearEquiv hn hA (realEuclideanCoordinateReindex e)

/-- A closed weak structure supplies the smaller input actually consumed by
the description product argument. -/
theorem PositiveArityWeakSetStructure.toClosedDescriptionBase
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S) :
    ClosedPositiveArityDescriptionBase S :=
  { toPositiveArityDescriptionReindexBase := hS.toDescriptionReindexBase
    base_isClosed := hclosed
    base_prod := by
      intro n m hn hm A B hA hB
      exact hS.ws3_prod (n := n) (m := m) hn hm
        (A := A) (B := B) hA hB }

/-- Extend a coordinate bijection by the identity on a final coordinate
block. -/
def finAddCoordinateEquiv {n m : ℕ} (e : Fin m ≃ Fin n) (k : ℕ) :
    Fin (m + k) ≃ Fin (n + k) :=
  finSumFinEquiv.symm |>.trans
    ((Equiv.sumCongr e (Equiv.refl (Fin k))).trans finSumFinEquiv)

@[simp]
theorem realEuclideanCoordinateReindex_append {n m k : ℕ}
    (e : Fin m ≃ Fin n) (x : RealEuclidean n) (z : RealEuclidean k) :
    realEuclideanCoordinateReindex (finAddCoordinateEquiv e k)
        (realEuclideanAppend x z) =
      realEuclideanAppend (realEuclideanCoordinateReindex e x) z := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [realEuclideanCoordinateReindex, finAddCoordinateEquiv,
      realEuclideanAppend]

/-- Coordinate reindexing commutes with projection when the hidden final
block is left fixed. -/
theorem realEuclideanExistentialProjection_coordinateReindex_image
    {n m k : ℕ} (e : Fin m ≃ Fin n)
    (A : Set (RealEuclidean (n + k))) :
    realEuclideanExistentialProjection
        (realEuclideanCoordinateReindex (finAddCoordinateEquiv e k) '' A) =
      realEuclideanCoordinateReindex e ''
        realEuclideanExistentialProjection A := by
  ext y
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, u, hu, heq⟩
    let x : RealEuclidean n := realEuclideanTakeLeft u
    let w : RealEuclidean k := realEuclideanTakeRight u
    have hdecomp : u = realEuclideanAppend x w := by
      exact (realEuclideanAppend_takeLeft_takeRight u).symm
    have hmap :
        realEuclideanCoordinateReindex (finAddCoordinateEquiv e k) u =
          realEuclideanAppend (realEuclideanCoordinateReindex e x) w := by
      rw [hdecomp, realEuclideanCoordinateReindex_append]
    have hvisible : realEuclideanCoordinateReindex e x = y := by
      have h := congrArg (realEuclideanTakeLeft (n := m) (m := k))
        (hmap.symm.trans heq)
      simpa using h
    refine ⟨x, ⟨w, ?_⟩, hvisible⟩
    simpa only [hdecomp] using hu
  · rintro ⟨x, ⟨z, hxz⟩, hxy⟩
    refine ⟨z, realEuclideanAppend x z, hxz, ?_⟩
    rw [realEuclideanCoordinateReindex_append, hxy]

/-! ## Integer-affine helper facts -/

/-- Integer-affine sets are preserved by finite coordinate reindexing. -/
theorem IsIntegerAffineSet.coordinateReindex_image
    {n m : ℕ} {L : Set (RealEuclidean n)}
    (hL : IsIntegerAffineSet L) (e : Fin m ≃ Fin n) :
    IsIntegerAffineSet (realEuclideanCoordinateReindex e '' L) := by
  obtain ⟨r, coeff, constant, rfl⟩ := hL
  refine ⟨r, (fun i j ↦ coeff i (e j)), constant, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro i
    change (∑ j : Fin m, (coeff i (e j) : ℝ) * x (e j)) +
        (constant i : ℝ) = 0
    have hsum :
        (∑ j : Fin m, (coeff i (e j) : ℝ) * x (e j)) =
          ∑ j : Fin n, (coeff i j : ℝ) * x j :=
      Equiv.sum_comp e
        (fun j : Fin n ↦ (coeff i j : ℝ) * x j)
    exact (congrArg (fun t : ℝ ↦ t + (constant i : ℝ)) hsum).trans
      (hx i)
  · intro hy
    let x : RealEuclidean n := realEuclideanCoordinateReindex e.symm y
    refine ⟨x, ?_, ?_⟩
    · intro i
      change (∑ j : Fin n, (coeff i j : ℝ) * y (e.symm j)) +
          (constant i : ℝ) = 0
      rw [show
        (∑ j : Fin n, (coeff i j : ℝ) * y (e.symm j)) =
            ∑ j : Fin m, (coeff i (e j) : ℝ) * y j by
          simpa using Equiv.sum_comp e.symm
            (fun j : Fin m ↦ (coeff i (e j) : ℝ) * y j)]
      exact hy i
    · funext j
      simp [x, realEuclideanCoordinateReindex]

/-- The whole coordinate space is integer-affine (the empty system of
equations). -/
theorem isIntegerAffineSet_univ (n : ℕ) :
    IsIntegerAffineSet (Set.univ : Set (RealEuclidean n)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
  ext x
  simp

/-- Intersecting two finite systems of integer-affine equations concatenates
their equation lists. -/
theorem IsIntegerAffineSet.inter {n : ℕ}
    {L K : Set (RealEuclidean n)}
    (hL : IsIntegerAffineSet L) (hK : IsIntegerAffineSet K) :
    IsIntegerAffineSet (L ∩ K) := by
  obtain ⟨r, coeffL, constantL, rfl⟩ := hL
  obtain ⟨s, coeffK, constantK, rfl⟩ := hK
  refine ⟨r + s,
    (fun i ↦ Fin.addCases coeffL coeffK i),
    Fin.addCases constantL constantK, ?_⟩
  ext x
  simp [Fin.forall_fin_add]

/-- A cylinder over an integer-affine set, with free coordinates appended on
the right, is integer-affine. -/
theorem IsIntegerAffineSet.prod_univ_right {n : ℕ}
    {L : Set (RealEuclidean n)} (hL : IsIntegerAffineSet L) (m : ℕ) :
    IsIntegerAffineSet
      (realEuclideanSetProduct L (Set.univ : Set (RealEuclidean m))) := by
  obtain ⟨r, coeff, constant, rfl⟩ := hL
  refine ⟨r,
    (fun i ↦ Fin.addCases (coeff i) (fun _ ↦ 0)), constant, ?_⟩
  ext v
  simp [realEuclideanSetProduct, realEuclideanTakeLeft,
    Fin.sum_univ_add]

/-- A cylinder over an integer-affine set, with free coordinates prepended on
the left, is integer-affine. -/
theorem IsIntegerAffineSet.univ_prod_left {n : ℕ}
    {L : Set (RealEuclidean n)} (hL : IsIntegerAffineSet L) (m : ℕ) :
    IsIntegerAffineSet
      (realEuclideanSetProduct (Set.univ : Set (RealEuclidean m)) L) := by
  obtain ⟨r, coeff, constant, rfl⟩ := hL
  refine ⟨r,
    (fun i ↦ Fin.addCases (fun _ ↦ 0) (coeff i)), constant, ?_⟩
  ext v
  simp [realEuclideanSetProduct, realEuclideanTakeRight,
    Fin.sum_univ_add]

/-- The diagonal in the flat product `ℝⁿ × ℝⁿ`. -/
def realEuclideanDiagonal (n : ℕ) : Set (RealEuclidean (n + n)) :=
  {v | realEuclideanTakeLeft v = realEuclideanTakeRight v}

/-- The integer coefficient row `eᵢ - eₙ₊ᵢ` cutting out the `i`th diagonal
equation. -/
def realEuclideanDiagonalIntegerCoeff (n : ℕ) (i : Fin n) :
    Fin (n + n) → ℤ :=
  Fin.addCases
    (fun j ↦ if i = j then 1 else 0)
    (fun j ↦ if i = j then -1 else 0)

/-- Evaluation of a diagonal coefficient row is the difference of the two
corresponding block coordinates. -/
theorem sum_realEuclideanDiagonalIntegerCoeff
    {n : ℕ} (v : RealEuclidean (n + n)) (i : Fin n) :
    (∑ j, (realEuclideanDiagonalIntegerCoeff n i j : ℝ) * v j) =
      realEuclideanTakeLeft v i - realEuclideanTakeRight v i := by
  classical
  simp only [Fin.sum_univ_add, realEuclideanDiagonalIntegerCoeff,
    Fin.addCases_left, Fin.addCases_right, Int.cast_ite, Int.cast_one,
    Int.cast_zero, Int.cast_neg, ite_mul, one_mul, zero_mul, neg_mul,
    Fintype.sum_ite_eq, realEuclideanTakeLeft, realEuclideanTakeRight,
    sub_eq_add_neg]

/-- The diagonal is cut out by the integer-linear equations `xᵢ - yᵢ = 0`. -/
theorem isIntegerAffineSet_realEuclideanDiagonal (n : ℕ) :
    IsIntegerAffineSet (realEuclideanDiagonal n) := by
  refine ⟨n, realEuclideanDiagonalIntegerCoeff n, (fun _ ↦ 0), ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, realEuclideanDiagonal]
  constructor
  · intro h
    intro i
    have hi := congrFun h i
    simpa only [sum_realEuclideanDiagonalIntegerCoeff, Int.cast_zero,
      add_zero, sub_eq_zero] using hi
  · intro h
    funext i
    simpa only [sum_realEuclideanDiagonalIntegerCoeff, Int.cast_zero,
      add_zero, sub_eq_zero] using h i

/-- Every integer-affine set is topologically closed. -/
theorem IsIntegerAffineSet.isClosed {n : ℕ}
    {L : Set (RealEuclidean n)} (hL : IsIntegerAffineSet L) :
    IsClosed L := by
  obtain ⟨r, coeff, constant, rfl⟩ := hL
  rw [show
    {x : RealEuclidean n |
      ∀ i, (∑ j, (coeff i j : ℝ) * x j) + (constant i : ℝ) = 0} =
      ⋂ i, {x : RealEuclidean n |
        (∑ j, (coeff i j : ℝ) * x j) + (constant i : ℝ) = 0} by
      ext x
      simp]
  apply isClosed_iInter
  intro i
  exact isClosed_eq (by fun_prop) continuous_const

/-! ## Coordinate reindexing of descriptions -/

/-- Coordinate bijections act on descriptions without changing rank.  This is
the description-level form of the source's W(perm) observation and uses only
the coordinate-reindexing part of the base structure. -/
theorem PositiveArityDescriptionReindexBase.exists_coordinateReindex_description
    {S : EuclideanSetFamily} (hS : PositiveArityDescriptionReindexBase S)
    {n m : ℕ} (description : CharbonnelDescription S n)
    (e : Fin m ≃ Fin n) :
    ∃ reindexed : CharbonnelDescription S m,
      reindexed.carrier = realEuclideanCoordinateReindex e '' description.carrier ∧
        reindexed.rank = description.rank := by
  induction description generalizing m with
  | @base n hn A hA =>
      have hmem : realEuclideanCoordinateReindex e '' A ∈ S m :=
        hS.coordinateReindex hn hA e
      have hm : 0 < m := by
        have hmn : m = n := by
          simpa using Fintype.card_congr e
        omega
      exact ⟨.base hm _ hmem, rfl, rfl⟩
  | @union n left right ihleft ihright =>
      obtain ⟨left', hleftCarrier, hleftRank⟩ := ihleft e
      obtain ⟨right', hrightCarrier, hrightRank⟩ := ihright e
      refine ⟨.union left' right', ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_union, hleftCarrier,
          hrightCarrier, Set.image_union]
      · simp only [CharbonnelDescription.rank_union, hleftRank, hrightRank]
  | @integerAffineInter n inner L hL ih =>
      obtain ⟨inner', hinnerCarrier, hinnerRank⟩ := ih e
      let E := realEuclideanCoordinateReindex e
      have hEL : IsIntegerAffineSet (E '' L) :=
        hL.coordinateReindex_image e
      refine ⟨.integerAffineInter inner' (E '' L) hEL, ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_integerAffineInter,
          hinnerCarrier, E]
        exact (Set.image_inter E.injective).symm
      · simp only [CharbonnelDescription.rank_integerAffineInter, hinnerRank]
  | @projection n k hn inner ih =>
      let e' : Fin (m + k) ≃ Fin (n + k) := finAddCoordinateEquiv e k
      obtain ⟨inner', hinnerCarrier, hinnerRank⟩ := ih e'
      have hm : 0 < m := by
        have hmn : m = n := by
          simpa using Fintype.card_congr e
        omega
      refine ⟨.projection hm inner', ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_projection, hinnerCarrier, e']
        exact realEuclideanExistentialProjection_coordinateReindex_image e
          inner.carrier
      · simp only [CharbonnelDescription.rank_projection, hinnerRank]
  | @topologicalClosure n inner ih =>
      obtain ⟨inner', hinnerCarrier, hinnerRank⟩ := ih e
      let E := realEuclideanCoordinateReindex e
      refine ⟨.topologicalClosure inner', ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_topologicalClosure,
          hinnerCarrier, E]
        exact
          (E.toContinuousLinearEquiv.image_closure inner.carrier).symm
      · simp only [CharbonnelDescription.rank_topologicalClosure, hinnerRank]

/-- Backward-compatible WS4 specialization of coordinate reindexing. -/
theorem PositiveArityWeakSetStructure.exists_coordinateReindex_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n m : ℕ} (description : CharbonnelDescription S n)
    (e : Fin m ≃ Fin n) :
    ∃ reindexed : CharbonnelDescription S m,
      reindexed.carrier = realEuclideanCoordinateReindex e '' description.carrier ∧
        reindexed.rank = description.rank :=
  hS.toDescriptionReindexBase.exists_coordinateReindex_description description e

/-! ## Flat-coordinate product identities -/

/-- Concatenation identifies a product of finite real coordinate spaces with
the corresponding flat coordinate space. -/
def realEuclideanAppendLinearEquiv (n m : ℕ) :
    (RealEuclidean n × RealEuclidean m) ≃ₗ[ℝ] RealEuclidean (n + m) where
  toFun p := realEuclideanAppend p.1 p.2
  invFun v := (realEuclideanTakeLeft v, realEuclideanTakeRight v)
  left_inv p := by
    ext <;> simp
  right_inv v := realEuclideanAppend_takeLeft_takeRight v
  map_add' p q := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend]
  map_smul' c p := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend]

/-- The flat-coordinate set product is the image of the ordinary product set
under concatenation. -/
theorem realEuclideanSetProduct_eq_append_image {n m : ℕ}
    (A : Set (RealEuclidean n)) (B : Set (RealEuclidean m)) :
    realEuclideanSetProduct A B =
      realEuclideanAppendLinearEquiv n m '' (A ×ˢ B) := by
  ext v
  constructor
  · intro hv
    refine ⟨(realEuclideanTakeLeft v, realEuclideanTakeRight v), hv, ?_⟩
    exact realEuclideanAppend_takeLeft_takeRight v
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    change realEuclideanTakeLeft (realEuclideanAppend x y) ∈ A ∧
      realEuclideanTakeRight (realEuclideanAppend x y) ∈ B
    simpa only [realEuclideanTakeLeft_append,
      realEuclideanTakeRight_append] using And.intro hx hy

/-- Closure commutes with the flat-coordinate product. -/
theorem closure_realEuclideanSetProduct {n m : ℕ}
    (A : Set (RealEuclidean n)) (B : Set (RealEuclidean m)) :
    closure (realEuclideanSetProduct A B) =
      realEuclideanSetProduct (closure A) (closure B) := by
  let E := realEuclideanAppendLinearEquiv n m
  calc
    closure (realEuclideanSetProduct A B) =
        closure (E '' (A ×ˢ B)) := by
          rw [realEuclideanSetProduct_eq_append_image]
    _ = E '' closure (A ×ˢ B) :=
      (E.toContinuousLinearEquiv.image_closure (A ×ˢ B)).symm
    _ = E '' (closure A ×ˢ closure B) := by
      rw [closure_prod_eq]
    _ = realEuclideanSetProduct (closure A) (closure B) := by
      rw [realEuclideanSetProduct_eq_append_image]

/-- If the right factor is closed, closing a product only closes its left
factor. -/
theorem closure_realEuclideanSetProduct_of_right_isClosed {n m : ℕ}
    (A : Set (RealEuclidean n)) {B : Set (RealEuclidean m)}
    (hB : IsClosed B) :
    closure (realEuclideanSetProduct A B) =
      realEuclideanSetProduct (closure A) B := by
  rw [closure_realEuclideanSetProduct, hB.closure_eq]

/-- If the left factor is closed, closing a product only closes its right
factor. -/
theorem closure_realEuclideanSetProduct_of_left_isClosed {n m : ℕ}
    {A : Set (RealEuclidean n)} (B : Set (RealEuclidean m))
    (hA : IsClosed A) :
    closure (realEuclideanSetProduct A B) =
      realEuclideanSetProduct A (closure B) := by
  rw [closure_realEuclideanSetProduct, hA.closure_eq]

theorem realEuclideanSetProduct_union_right {n m : ℕ}
    (A : Set (RealEuclidean n)) (B C : Set (RealEuclidean m)) :
    realEuclideanSetProduct A (B ∪ C) =
      realEuclideanSetProduct A B ∪ realEuclideanSetProduct A C := by
  ext v
  simp [realEuclideanSetProduct, and_or_left]

theorem realEuclideanSetProduct_union_left {n m : ℕ}
    (A B : Set (RealEuclidean n)) (C : Set (RealEuclidean m)) :
    realEuclideanSetProduct (A ∪ B) C =
      realEuclideanSetProduct A C ∪ realEuclideanSetProduct B C := by
  ext v
  simp [realEuclideanSetProduct, or_and_right]

theorem realEuclideanSetProduct_inter_right {n m : ℕ}
    (A : Set (RealEuclidean n)) (B C : Set (RealEuclidean m)) :
    realEuclideanSetProduct A (B ∩ C) =
      realEuclideanSetProduct A B ∩
        realEuclideanSetProduct (Set.univ : Set (RealEuclidean n)) C := by
  ext v
  simp [realEuclideanSetProduct, and_assoc]

theorem realEuclideanSetProduct_inter_left {n m : ℕ}
    (A B : Set (RealEuclidean n)) (C : Set (RealEuclidean m)) :
    realEuclideanSetProduct (A ∩ B) C =
      realEuclideanSetProduct A C ∩
        realEuclideanSetProduct B (Set.univ : Set (RealEuclidean m)) := by
  ext v
  simp [realEuclideanSetProduct, and_assoc, and_left_comm, and_comm]

/-! ## The two block reindexings used by products -/

/-- The coordinate equivalence from the flat bracketing `((n+m)+k)` to
`(n+(m+k))`. -/
def finAddAssocCoordinateEquiv (n m k : ℕ) :
    Fin ((n + m) + k) ≃ Fin (n + (m + k)) :=
  ((finSumFinEquiv : Fin (n + m) ⊕ Fin k ≃ Fin ((n + m) + k)).symm).trans
    ((Equiv.sumCongr
      (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm
      (Equiv.refl (Fin k))).trans
    ((Equiv.sumAssoc (Fin n) (Fin m) (Fin k)).trans
    ((Equiv.sumCongr (Equiv.refl (Fin n))
      (finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m + k))).trans
      (finSumFinEquiv : Fin n ⊕ Fin (m + k) ≃ Fin (n + (m + k))))))

@[simp]
theorem realEuclideanCoordinateReindex_finAddAssoc_append
    {n m k : ℕ} (x : RealEuclidean n) (y : RealEuclidean m)
    (z : RealEuclidean k) :
    realEuclideanCoordinateReindex (finAddAssocCoordinateEquiv n m k)
        (realEuclideanAppend x (realEuclideanAppend y z)) =
      realEuclideanAppend (realEuclideanAppend x y) z := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro ij
    refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) ij <;>
      simp [realEuclideanCoordinateReindex, finAddAssocCoordinateEquiv,
        realEuclideanAppend]
  · intro c
    simp [realEuclideanCoordinateReindex, finAddAssocCoordinateEquiv,
      realEuclideanAppend]

/-- Reassociated products project to the product of the first factor with the
projection of the second. -/
theorem realEuclideanExistentialProjection_assoc_image_product
    {n m k : ℕ} (A : Set (RealEuclidean n))
    (B : Set (RealEuclidean (m + k))) :
    realEuclideanExistentialProjection
        (realEuclideanCoordinateReindex (finAddAssocCoordinateEquiv n m k) ''
          realEuclideanSetProduct A B) =
      realEuclideanSetProduct A
        (realEuclideanExistentialProjection B) := by
  ext v
  let x : RealEuclidean n := realEuclideanTakeLeft v
  let y : RealEuclidean m := realEuclideanTakeRight v
  have hv : v = realEuclideanAppend x y :=
    (realEuclideanAppend_takeLeft_takeRight v).symm
  rw [hv]
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    realEuclideanSetProduct, realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · rintro ⟨z, w, hw, heq⟩
    have hcanonical :
        realEuclideanCoordinateReindex (finAddAssocCoordinateEquiv n m k)
            (realEuclideanAppend x (realEuclideanAppend y z)) =
          realEuclideanAppend (realEuclideanAppend x y) z :=
      realEuclideanCoordinateReindex_finAddAssoc_append x y z
    have hwEq : w = realEuclideanAppend x (realEuclideanAppend y z) :=
      (realEuclideanCoordinateReindex
        (finAddAssocCoordinateEquiv n m k)).injective
          (heq.trans hcanonical.symm)
    rw [hwEq] at hw
    refine ⟨?_, z, ?_⟩
    · simpa only [realEuclideanTakeLeft_append] using hw.1
    · simpa only [realEuclideanTakeRight_append] using hw.2
  · rintro ⟨hx, z, hyz⟩
    refine ⟨z, realEuclideanAppend x (realEuclideanAppend y z), ?_, ?_⟩
    · change
        realEuclideanTakeLeft
            (realEuclideanAppend x (realEuclideanAppend y z)) ∈ A ∧
          realEuclideanTakeRight
            (realEuclideanAppend x (realEuclideanAppend y z)) ∈ B
      simpa only [realEuclideanTakeLeft_append,
        realEuclideanTakeRight_append] using And.intro hx hyz
    exact realEuclideanCoordinateReindex_finAddAssoc_append x y z

@[simp]
theorem realEuclideanCoordinateReindex_finAddFlip_append
    {n m : ℕ} (x : RealEuclidean n) (y : RealEuclidean m) :
    realEuclideanCoordinateReindex (@finAddFlip n m)
        (realEuclideanAppend y x) =
      realEuclideanAppend x y := by
  funext i
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i <;>
    simp [realEuclideanCoordinateReindex, realEuclideanAppend]

/-- Exchanging the two flat coordinate blocks takes `B × A` to `A × B`. -/
theorem coordinateReindex_finAddFlip_image_product {n m : ℕ}
    (A : Set (RealEuclidean n)) (B : Set (RealEuclidean m)) :
    realEuclideanCoordinateReindex (@finAddFlip n m) ''
        realEuclideanSetProduct B A =
      realEuclideanSetProduct A B := by
  ext v
  let x : RealEuclidean n := realEuclideanTakeLeft v
  let y : RealEuclidean m := realEuclideanTakeRight v
  have hv : v = realEuclideanAppend x y :=
    (realEuclideanAppend_takeLeft_takeRight v).symm
  rw [hv]
  constructor
  · rintro ⟨w, hw, heq⟩
    have hcanonical :
        realEuclideanCoordinateReindex (@finAddFlip n m)
            (realEuclideanAppend y x) = realEuclideanAppend x y :=
      realEuclideanCoordinateReindex_finAddFlip_append x y
    have hwEq : w = realEuclideanAppend y x :=
      (realEuclideanCoordinateReindex (@finAddFlip n m)).injective
        (heq.trans hcanonical.symm)
    rw [hwEq] at hw
    change
      realEuclideanTakeLeft (realEuclideanAppend y x) ∈ B ∧
        realEuclideanTakeRight (realEuclideanAppend y x) ∈ A at hw
    have hw' : y ∈ B ∧ x ∈ A := by
      simpa only [realEuclideanTakeLeft_append,
        realEuclideanTakeRight_append] using hw
    refine ⟨?_, ?_⟩
    · simpa only [realEuclideanTakeLeft_append] using hw'.2
    · simpa only [realEuclideanTakeRight_append] using hw'.1
  · rintro ⟨hx, hy⟩
    refine ⟨realEuclideanAppend y x, ?_, ?_⟩
    · change realEuclideanTakeLeft (realEuclideanAppend y x) ∈ B ∧
        realEuclideanTakeRight (realEuclideanAppend y x) ∈ A
      simpa only [realEuclideanTakeLeft_append,
        realEuclideanTakeRight_append] using And.intro hy hx
    exact realEuclideanCoordinateReindex_finAddFlip_append x y

/-! ## The diagonal projection identity -/

/-- Intersect a product with the diagonal and project: this is ordinary set
intersection. -/
theorem projection_product_inter_diagonal {n : ℕ}
    (A B : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection
        (realEuclideanSetProduct A B ∩ realEuclideanDiagonal n) =
      A ∩ B := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    Set.mem_inter_iff, realEuclideanSetProduct, realEuclideanDiagonal,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
  constructor
  · rintro ⟨y, ⟨hx, hy⟩, hxy⟩
    subst y
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hxB⟩
    exact ⟨x, ⟨hx, hxB⟩, rfl⟩

/-! ## Products of descriptions -/

/-- Product construction for descriptions over the exact closed-base
interface above.  This is the description-level form of Berarducci--Servi,
Lemma 3.3.7 (Lemma 4.7 in the paper): the carrier is the exact flat Cartesian
product and its rank is bounded by the sum of the two input ranks. -/
theorem ClosedPositiveArityDescriptionBase.exists_product_description
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    {n m : ℕ} (left : CharbonnelDescription S n)
    (right : CharbonnelDescription S m) :
    ∃ product : CharbonnelDescription S (n + m),
      product.carrier =
          realEuclideanSetProduct left.carrier right.carrier ∧
        product.rank ≤ left.rank + right.rank := by
  induction right generalizing n with
  | @base m hm B hB =>
      induction left with
      | @base n hn A hA =>
          have hprod : realEuclideanSetProduct A B ∈ S (n + m) :=
            hS.base_prod hn hm hA hB
          exact ⟨.base (by omega) _ hprod, rfl, by simp⟩
      | @union n A C ihA ihC =>
          obtain ⟨pA, hpACarrier, hpARank⟩ := ihA
          obtain ⟨pC, hpCCarrier, hpCRank⟩ := ihC
          refine ⟨.union pA pC, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_union, hpACarrier,
              hpCCarrier]
            exact (realEuclideanSetProduct_union_left _ _ _).symm
          · have hpA0 : pA.rank ≤ A.rank := by
              simpa only [CharbonnelDescription.rank_base, Nat.add_zero]
                using hpARank
            have hpC0 : pC.rank ≤ C.rank := by
              simpa only [CharbonnelDescription.rank_base, Nat.add_zero]
                using hpCRank
            have hmax : max pA.rank pC.rank ≤ max A.rank C.rank :=
              max_le (hpA0.trans (Nat.le_max_left _ _))
                (hpC0.trans (Nat.le_max_right _ _))
            simpa only [CharbonnelDescription.rank_union,
              CharbonnelDescription.rank_base, Nat.add_zero] using
                Nat.add_le_add_left hmax 1
      | @integerAffineInter n A L hL ih =>
          obtain ⟨p, hpCarrier, hpRank⟩ := ih
          have hCylinder := hL.prod_univ_right m
          refine ⟨.integerAffineInter p
            (realEuclideanSetProduct L
              (Set.univ : Set (RealEuclidean m))) hCylinder, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_integerAffineInter,
              hpCarrier]
            exact (realEuclideanSetProduct_inter_left _ _ _).symm
          · simp only [CharbonnelDescription.rank_integerAffineInter]
            omega
      | @projection n k hn A ih =>
          obtain ⟨p, hpCarrier, hpRank⟩ := ih
          obtain ⟨pSwap, hpSwapCarrier, hpSwapRank⟩ :=
            hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description p
              (@finAddFlip m (n + k))
          obtain ⟨pAssoc, hpAssocCarrier, hpAssocRank⟩ :=
            hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description pSwap
              (finAddAssocCoordinateEquiv m n k)
          let projected : CharbonnelDescription S (m + n) :=
            .projection (by omega) pAssoc
          obtain ⟨answer, hanswerCarrier, hanswerRank⟩ :=
            hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description projected
              (@finAddFlip n m)
          refine ⟨answer, ?_, ?_⟩
          · calc
              answer.carrier =
                  realEuclideanCoordinateReindex (@finAddFlip n m) ''
                    projected.carrier := hanswerCarrier
              _ = realEuclideanCoordinateReindex (@finAddFlip n m) ''
                    realEuclideanSetProduct
                      (CharbonnelDescription.base hm B hB).carrier
                      (CharbonnelDescription.projection hn A).carrier := by
                    apply congrArg (fun T ↦
                      realEuclideanCoordinateReindex (@finAddFlip n m) '' T)
                    simp only [projected,
                      CharbonnelDescription.carrier_projection,
                      hpAssocCarrier, hpSwapCarrier, hpCarrier,
                      CharbonnelDescription.carrier_base,
                      CharbonnelDescription.carrier_projection]
                    rw [coordinateReindex_finAddFlip_image_product]
                    exact realEuclideanExistentialProjection_assoc_image_product
                      B A.carrier
              _ = realEuclideanSetProduct
                    (CharbonnelDescription.projection hn A).carrier
                    (CharbonnelDescription.base hm B hB).carrier :=
                coordinateReindex_finAddFlip_image_product _ _
          · simp only [hanswerRank, projected,
              CharbonnelDescription.rank_projection, hpAssocRank,
              hpSwapRank]
            omega
      | @topologicalClosure n A ih =>
          obtain ⟨p, hpCarrier, hpRank⟩ := ih
          refine ⟨.topologicalClosure p, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_topologicalClosure,
              hpCarrier, CharbonnelDescription.carrier_base]
            exact closure_realEuclideanSetProduct_of_right_isClosed
              A.carrier (hS.base_isClosed hm hB)
          · have hpRank0 : p.rank ≤ A.rank := by
              simpa only [CharbonnelDescription.rank_base, Nat.add_zero]
                using hpRank
            simpa only [CharbonnelDescription.rank_topologicalClosure,
              CharbonnelDescription.rank_base, Nat.add_zero] using
                Nat.add_le_add_left hpRank0 4
  | @union m B C ihB ihC =>
      obtain ⟨pB, hpBCarrier, hpBRank⟩ := ihB left
      obtain ⟨pC, hpCCarrier, hpCRank⟩ := ihC left
      refine ⟨.union pB pC, ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_union, hpBCarrier,
          hpCCarrier]
        exact (realEuclideanSetProduct_union_right _ _ _).symm
      · have hpB' : pB.rank ≤ left.rank + max B.rank C.rank :=
          hpBRank.trans (Nat.add_le_add_left
            (Nat.le_max_left B.rank C.rank) _)
        have hpC' : pC.rank ≤ left.rank + max B.rank C.rank :=
          hpCRank.trans (Nat.add_le_add_left
            (Nat.le_max_right B.rank C.rank) _)
        have hmax := max_le hpB' hpC'
        simp only [CharbonnelDescription.rank_union]
        omega
  | @integerAffineInter m B L hL ih =>
      obtain ⟨p, hpCarrier, hpRank⟩ := ih left
      have hCylinder := hL.univ_prod_left n
      refine ⟨.integerAffineInter p
        (realEuclideanSetProduct
          (Set.univ : Set (RealEuclidean n)) L) hCylinder, ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_integerAffineInter,
          hpCarrier]
        exact (realEuclideanSetProduct_inter_right _ _ _).symm
      · simp only [CharbonnelDescription.rank_integerAffineInter]
        omega
  | @projection m k hm B ih =>
      obtain ⟨p, hpCarrier, hpRank⟩ := ih left
      obtain ⟨pAssoc, hpAssocCarrier, hpAssocRank⟩ :=
        hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description p
          (finAddAssocCoordinateEquiv n m k)
      refine ⟨.projection (by omega) pAssoc, ?_, ?_⟩
      · simp only [CharbonnelDescription.carrier_projection,
          hpAssocCarrier, hpCarrier]
        exact realEuclideanExistentialProjection_assoc_image_product
          left.carrier B.carrier
      · simp only [CharbonnelDescription.rank_projection, hpAssocRank]
        omega
  | @topologicalClosure m B ihRight =>
      induction left with
      | @base n hn A hA =>
          obtain ⟨p, hpCarrier, hpRank⟩ :=
            ihRight (CharbonnelDescription.base hn A hA)
          refine ⟨.topologicalClosure p, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_topologicalClosure,
              hpCarrier, CharbonnelDescription.carrier_base]
            exact closure_realEuclideanSetProduct_of_left_isClosed
              B.carrier (hS.base_isClosed hn hA)
          · simp only [CharbonnelDescription.rank_topologicalClosure]
            omega
      | @union n A C ihA ihC =>
          obtain ⟨pA, hpACarrier, hpARank⟩ := ihA
          obtain ⟨pC, hpCCarrier, hpCRank⟩ := ihC
          refine ⟨.union pA pC, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_union, hpACarrier,
              hpCCarrier]
            exact (realEuclideanSetProduct_union_left _ _ _).symm
          · have hpA' : pA.rank ≤ max A.rank C.rank +
                (CharbonnelDescription.topologicalClosure B).rank :=
              hpARank.trans (Nat.add_le_add_right
                (Nat.le_max_left A.rank C.rank) _)
            have hpC' : pC.rank ≤ max A.rank C.rank +
                (CharbonnelDescription.topologicalClosure B).rank :=
              hpCRank.trans (Nat.add_le_add_right
                (Nat.le_max_right A.rank C.rank) _)
            have hmax := max_le hpA' hpC'
            simp only [CharbonnelDescription.rank_union]
            omega
      | @integerAffineInter n A L hL ih =>
          obtain ⟨p, hpCarrier, hpRank⟩ := ih
          have hCylinder := hL.prod_univ_right m
          refine ⟨.integerAffineInter p
            (realEuclideanSetProduct L
              (Set.univ : Set (RealEuclidean m))) hCylinder, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_integerAffineInter,
              hpCarrier]
            exact (realEuclideanSetProduct_inter_left _ _ _).symm
          · simp only [CharbonnelDescription.rank_integerAffineInter]
            omega
      | @projection n k hn A ih =>
          obtain ⟨p, hpCarrier, hpRank⟩ := ih
          obtain ⟨pSwap, hpSwapCarrier, hpSwapRank⟩ :=
            hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description p
              (@finAddFlip m (n + k))
          obtain ⟨pAssoc, hpAssocCarrier, hpAssocRank⟩ :=
            hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description pSwap
              (finAddAssocCoordinateEquiv m n k)
          let projected : CharbonnelDescription S (m + n) :=
            .projection (by omega) pAssoc
          obtain ⟨answer, hanswerCarrier, hanswerRank⟩ :=
            hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description projected
              (@finAddFlip n m)
          refine ⟨answer, ?_, ?_⟩
          · calc
              answer.carrier =
                  realEuclideanCoordinateReindex (@finAddFlip n m) ''
                    projected.carrier := hanswerCarrier
              _ = realEuclideanCoordinateReindex (@finAddFlip n m) ''
                    realEuclideanSetProduct
                      (CharbonnelDescription.topologicalClosure B).carrier
                      (CharbonnelDescription.projection hn A).carrier := by
                    apply congrArg (fun T ↦
                      realEuclideanCoordinateReindex (@finAddFlip n m) '' T)
                    simp only [projected,
                      CharbonnelDescription.carrier_projection,
                      hpAssocCarrier, hpSwapCarrier, hpCarrier,
                      CharbonnelDescription.carrier_topologicalClosure,
                      CharbonnelDescription.carrier_projection]
                    rw [coordinateReindex_finAddFlip_image_product]
                    exact realEuclideanExistentialProjection_assoc_image_product
                      (closure B.carrier) A.carrier
              _ = realEuclideanSetProduct
                    (CharbonnelDescription.projection hn A).carrier
                    (CharbonnelDescription.topologicalClosure B).carrier :=
                coordinateReindex_finAddFlip_image_product _ _
          · simp only [hanswerRank, projected,
              CharbonnelDescription.rank_projection, hpAssocRank,
              hpSwapRank]
            omega
      | @topologicalClosure n A ih =>
          obtain ⟨p, hpCarrier, hpRank⟩ := ih
          refine ⟨.topologicalClosure p, ?_, ?_⟩
          · simp only [CharbonnelDescription.carrier_topologicalClosure,
              hpCarrier]
            exact closure_realEuclideanSetProduct_of_right_isClosed
              A.carrier isClosed_closure
          · have hpRank' :
                p.rank ≤ A.rank + (4 + B.rank) := by
              simpa only [CharbonnelDescription.rank_topologicalClosure]
                using hpRank
            simp only [CharbonnelDescription.rank_topologicalClosure]
            calc
              4 + p.rank ≤ 4 + (A.rank + (4 + B.rank)) :=
                Nat.add_le_add_left hpRank' 4
              _ = (4 + A.rank) + (4 + B.rank) := by omega

/-- Backward-compatible closed-weak-structure specialization of the product
lemma. -/
theorem PositiveArityWeakSetStructure.exists_product_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n m : ℕ} (left : CharbonnelDescription S n)
    (right : CharbonnelDescription S m) :
    ∃ product : CharbonnelDescription S (n + m),
      product.carrier =
          realEuclideanSetProduct left.carrier right.carrier ∧
        product.rank ≤ left.rank + right.rank :=
  (hS.toClosedDescriptionBase hclosed).exists_product_description left right

/-! ## Arbitrary intersections of descriptions -/

/-- Arbitrary binary intersection is obtained exactly as in the source:
form the product, intersect with the integer-affine diagonal, and project.
The two new description nodes account for the additive rank bound `2`. -/
theorem ClosedPositiveArityDescriptionBase.exists_inter_description
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    {n : ℕ} (left right : CharbonnelDescription S n) :
    ∃ intersection : CharbonnelDescription S n,
      intersection.carrier = left.carrier ∩ right.carrier ∧
        intersection.rank ≤ 2 + left.rank + right.rank := by
  obtain ⟨product, hproductCarrier, hproductRank⟩ :=
    hS.exists_product_description left right
  let diagonalCut : CharbonnelDescription S (n + n) :=
    .integerAffineInter product (realEuclideanDiagonal n)
      (isIntegerAffineSet_realEuclideanDiagonal n)
  let answer : CharbonnelDescription S n :=
    .projection left.positiveArity diagonalCut
  refine ⟨answer, ?_, ?_⟩
  · simp only [answer, diagonalCut,
      CharbonnelDescription.carrier_projection,
      CharbonnelDescription.carrier_integerAffineInter, hproductCarrier]
    exact projection_product_inter_diagonal left.carrier right.carrier
  · simp only [answer, diagonalCut,
      CharbonnelDescription.rank_projection,
      CharbonnelDescription.rank_integerAffineInter]
    omega

/-- Backward-compatible closed-weak-structure specialization of the
intersection lemma. -/
theorem PositiveArityWeakSetStructure.exists_inter_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n : ℕ} (left right : CharbonnelDescription S n) :
    ∃ intersection : CharbonnelDescription S n,
      intersection.carrier = left.carrier ∩ right.carrier ∧
        intersection.rank ≤ 2 + left.rank + right.rank :=
  (hS.toClosedDescriptionBase hclosed).exists_inter_description left right

/-- Closure-family form of the product theorem for the exact closed-base
interface used by its proof. -/
theorem ClosedPositiveArityDescriptionBase.charbonnelClosure_product
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    {n m : ℕ} {A : Set (RealEuclidean n)} {B : Set (RealEuclidean m)}
    (hA : A ∈ charbonnelClosure S n) (hB : B ∈ charbonnelClosure S m) :
    realEuclideanSetProduct A B ∈ charbonnelClosure S (n + m) := by
  obtain ⟨left, rfl⟩ := hA
  obtain ⟨right, rfl⟩ := hB
  obtain ⟨product, hproduct, _⟩ :=
    hS.exists_product_description left right
  exact ⟨product, hproduct⟩

/-- Closure-family form of the intersection theorem for the exact closed-base
interface used by its proof. -/
theorem ClosedPositiveArityDescriptionBase.charbonnelClosure_inter
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    {n : ℕ} {A B : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) (hB : B ∈ charbonnelClosure S n) :
    A ∩ B ∈ charbonnelClosure S n := by
  obtain ⟨left, rfl⟩ := hA
  obtain ⟨right, rfl⟩ := hB
  obtain ⟨intersection, hintersection, _⟩ :=
    hS.exists_inter_description left right
  exact ⟨intersection, hintersection⟩

/-- Closure-family form of the product theorem for a closed weak structure. -/
theorem charbonnelClosure_product
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n m : ℕ} {A : Set (RealEuclidean n)} {B : Set (RealEuclidean m)}
    (hA : A ∈ charbonnelClosure S n) (hB : B ∈ charbonnelClosure S m) :
    realEuclideanSetProduct A B ∈ charbonnelClosure S (n + m) := by
  obtain ⟨left, rfl⟩ := hA
  obtain ⟨right, rfl⟩ := hB
  obtain ⟨product, hproduct, _⟩ :=
    hS.exists_product_description hclosed left right
  exact ⟨product, hproduct⟩

/-- Closure-family form of the arbitrary intersection theorem. -/
theorem charbonnelClosure_inter
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n : ℕ} {A B : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) (hB : B ∈ charbonnelClosure S n) :
    A ∩ B ∈ charbonnelClosure S n := by
  obtain ⟨left, rfl⟩ := hA
  obtain ⟨right, rfl⟩ := hB
  obtain ⟨intersection, hintersection, _⟩ :=
    hS.exists_inter_description hclosed left right
  exact ⟨intersection, hintersection⟩

end AbelFormalization
