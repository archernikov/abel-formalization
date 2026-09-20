import AbelFormalization.CharbonnelSourceStageHierarchy

/-!
# Weak-family preservation for Wilkie's source stages

This file proves the operation-preservation lemma behind the phrase
"earlier weak family" in Wilkie 3.13.  Starting only from
`PositiveArityWeakSetStructure S`, the nonempty finite-union expansion,
arbitrary coordinate-projection expansion, and closure-at-infinity expansion
are again positive-arity weak set structures.  Induction therefore supplies
`WilkieSourceStagesAreWeak S` for the literal hierarchy formalized in
`CharbonnelSourceStageHierarchy`.

The projection proof keeps all hidden coordinates explicit.  Intersections
use a shared-visible fiber product, products reorder visible and hidden
blocks, and linear images extend the visible equivalence by the identity on
the hidden block.  No complement closure, o-minimality, or Sardian theorem is
used.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Finite unions preserve weak structures -/

private theorem wilkieFiniteUnionCarrier_map_inter
    {X : Type*} (A : Set X) (pieces : List (Set X)) :
    wilkieFiniteUnionCarrier (pieces.map (fun B ↦ A ∩ B)) =
      A ∩ wilkieFiniteUnionCarrier pieces := by
  induction pieces with
  | nil => simp
  | cons B pieces ih =>
      simp only [List.map_cons, wilkieFiniteUnionCarrier_cons, ih]
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto

private theorem wilkieFiniteUnionCarrier_flatMap_inter
    {X : Type*} (left right : List (Set X)) :
    wilkieFiniteUnionCarrier
        (left.flatMap (fun A ↦ right.map (fun B ↦ A ∩ B))) =
      wilkieFiniteUnionCarrier left ∩ wilkieFiniteUnionCarrier right := by
  induction left with
  | nil => simp
  | cons A left ih =>
      simp only [List.flatMap_cons, wilkieFiniteUnionCarrier_append,
        wilkieFiniteUnionCarrier_map_inter, wilkieFiniteUnionCarrier_cons, ih]
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto

private theorem wilkieFiniteUnionCarrier_map_product
    {n m : ℕ} (A : Set (RealEuclidean n))
    (pieces : List (Set (RealEuclidean m))) :
    wilkieFiniteUnionCarrier
        (pieces.map (fun B ↦ realEuclideanSetProduct A B)) =
      realEuclideanSetProduct A (wilkieFiniteUnionCarrier pieces) := by
  induction pieces with
  | nil =>
      ext x
      simp [wilkieFiniteUnionCarrier, realEuclideanSetProduct]
  | cons B pieces ih =>
      simp only [List.map_cons, wilkieFiniteUnionCarrier_cons, ih,
        realEuclideanSetProduct_union_right]

private theorem wilkieFiniteUnionCarrier_flatMap_product
    {n m : ℕ} (left : List (Set (RealEuclidean n)))
    (right : List (Set (RealEuclidean m))) :
    wilkieFiniteUnionCarrier
        (left.flatMap (fun A ↦
          right.map (fun B ↦ realEuclideanSetProduct A B))) =
      realEuclideanSetProduct
        (wilkieFiniteUnionCarrier left)
        (wilkieFiniteUnionCarrier right) := by
  induction left with
  | nil =>
      ext x
      simp [wilkieFiniteUnionCarrier, realEuclideanSetProduct]
  | cons A left ih =>
      simp only [List.flatMap_cons, wilkieFiniteUnionCarrier_append,
        wilkieFiniteUnionCarrier_map_product, wilkieFiniteUnionCarrier_cons,
        ih, realEuclideanSetProduct_union_left]

private theorem wilkieFiniteUnionCarrier_map_linearEquiv_image
    {n : ℕ} (e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n)
    (pieces : List (Set (RealEuclidean n))) :
    wilkieFiniteUnionCarrier (pieces.map (fun A ↦ e '' A)) =
      e '' wilkieFiniteUnionCarrier pieces := by
  induction pieces with
  | nil => simp
  | cons A pieces ih =>
      simp only [List.map_cons, wilkieFiniteUnionCarrier_cons, ih,
        Set.image_union]

/-- Nonempty finite unions of members of a weak family form a weak family. -/
theorem PositiveArityWeakSetStructure.wilkieFiniteUnionExpansion
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S) :
    PositiveArityWeakSetStructure (wilkieFiniteUnionExpansion S) := by
  refine
    { ws1_inter := ?_
      ws2_polynomialSign := ?_
      ws3_prod := ?_
      ws4_linearEquiv := ?_ }
  · intro n hn A B hA hB
    obtain ⟨left, hleftNonempty, hleft, hleftCarrier⟩ := hA
    obtain ⟨right, hrightNonempty, hright, hrightCarrier⟩ := hB
    let pieces := left.flatMap (fun C ↦ right.map (fun D ↦ C ∩ D))
    have hpiecesNonempty : pieces ≠ [] := by
      obtain ⟨C, hC⟩ := List.exists_mem_of_ne_nil left hleftNonempty
      obtain ⟨D, hD⟩ := List.exists_mem_of_ne_nil right hrightNonempty
      have hCD : C ∩ D ∈ pieces := by
        exact List.mem_flatMap.mpr
          ⟨C, hC, List.mem_map.mpr ⟨D, hD, rfl⟩⟩
      intro hempty
      rw [hempty] at hCD
      simpa using hCD
    refine ⟨pieces, hpiecesNonempty, ?_, ?_⟩
    · intro E hE
      obtain ⟨C, hC, hE⟩ := List.mem_flatMap.mp hE
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hE
      exact hS.ws1_inter hn (hleft C hC) (hright D hD)
    · simp only [pieces, wilkieFiniteUnionCarrier_flatMap_inter,
        hleftCarrier, hrightCarrier]
  · intro n _hn A hA
    exact mem_wilkieFiniteUnionExpansion_singleton
      (hS.ws2_polynomialSign (by assumption) hA)
  · intro n m hn hm A B hA hB
    obtain ⟨left, hleftNonempty, hleft, hleftCarrier⟩ := hA
    obtain ⟨right, hrightNonempty, hright, hrightCarrier⟩ := hB
    let pieces := left.flatMap (fun C ↦
      right.map (fun D ↦ realEuclideanSetProduct C D))
    have hpiecesNonempty : pieces ≠ [] := by
      obtain ⟨C, hC⟩ := List.exists_mem_of_ne_nil left hleftNonempty
      obtain ⟨D, hD⟩ := List.exists_mem_of_ne_nil right hrightNonempty
      have hCD : realEuclideanSetProduct C D ∈ pieces := by
        exact List.mem_flatMap.mpr
          ⟨C, hC, List.mem_map.mpr ⟨D, hD, rfl⟩⟩
      intro hempty
      rw [hempty] at hCD
      simpa using hCD
    refine ⟨pieces, hpiecesNonempty, ?_, ?_⟩
    · intro E hE
      obtain ⟨C, hC, hE⟩ := List.mem_flatMap.mp hE
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hE
      exact hS.ws3_prod hn hm (hleft C hC) (hright D hD)
    · simp only [pieces, wilkieFiniteUnionCarrier_flatMap_product,
        hleftCarrier, hrightCarrier]
  · intro n hn A hA e
    obtain ⟨pieces, hnonempty, hpieces, hcarrier⟩ := hA
    refine ⟨pieces.map (fun B ↦ e '' B), ?_, ?_, ?_⟩
    · simpa using hnonempty
    · intro B hB
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
      exact hS.ws4_linearEquiv hn (hpieces C hC) e
    · rw [wilkieFiniteUnionCarrier_map_linearEquiv_image, hcarrier]

/-! ## Arbitrary projections preserve weak structures -/

/-- Exchange the middle two blocks in a fourfold sum.  This is the type-level
permutation behind the identity
`((x,u),(y,v)) ↦ ((x,y),(u,v))`. -/
private def sumFourBlockExchange
    (X U Y V : Type*) :
    ((X ⊕ Y) ⊕ (U ⊕ V)) ≃ ((X ⊕ U) ⊕ (Y ⊕ V)) where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inl (Sum.inr y) => Sum.inr (Sum.inl y)
    | Sum.inr (Sum.inl u) => Sum.inl (Sum.inr u)
    | Sum.inr (Sum.inr v) => Sum.inr (Sum.inr v)
  invFun
    | Sum.inl (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inl (Sum.inr u) => Sum.inr (Sum.inl u)
    | Sum.inr (Sum.inl y) => Sum.inl (Sum.inr y)
    | Sum.inr (Sum.inr v) => Sum.inr (Sum.inr v)
  left_inv x := by
    rcases x with (x | x) <;> rcases x with (x | x) <;> rfl
  right_inv x := by
    rcases x with (x | x) <;> rcases x with (x | x) <;> rfl

/-- Reorder `((n+k),(m+l))` coordinates into `((n+m),(k+l))`
coordinates.  The direction matches `realEuclideanCoordinateReindex`: an
output coordinate is sent to the corresponding input coordinate. -/
private def finProjectionProductCoordinateEquiv
    (n m k l : ℕ) :
    Fin ((n + m) + (k + l)) ≃ Fin ((n + k) + (m + l)) :=
  (finSumFinEquiv :
      Fin (n + m) ⊕ Fin (k + l) ≃ Fin ((n + m) + (k + l))).symm |>.trans
    ((Equiv.sumCongr
      (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm
      (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).symm).trans
    ((sumFourBlockExchange (Fin n) (Fin k) (Fin m) (Fin l)).trans
    ((Equiv.sumCongr
      (finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n + k))
      (finSumFinEquiv : Fin m ⊕ Fin l ≃ Fin (m + l))).trans
      (finSumFinEquiv :
        Fin (n + k) ⊕ Fin (m + l) ≃ Fin ((n + k) + (m + l))))))

@[simp]
private theorem realEuclideanCoordinateReindex_projectionProduct_append
    {n m k l : ℕ} (x : RealEuclidean n) (u : RealEuclidean k)
    (y : RealEuclidean m) (v : RealEuclidean l) :
    realEuclideanCoordinateReindex
        (finProjectionProductCoordinateEquiv n m k l)
        (realEuclideanAppend (realEuclideanAppend x u)
          (realEuclideanAppend y v)) =
      realEuclideanAppend (realEuclideanAppend x y)
        (realEuclideanAppend u v) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro ixy
    refine Fin.addCases (fun ix ↦ ?_) (fun iy ↦ ?_) ixy <;>
      simp [realEuclideanCoordinateReindex,
        finProjectionProductCoordinateEquiv, sumFourBlockExchange,
        realEuclideanAppend]
  · intro iuv
    refine Fin.addCases (fun iu ↦ ?_) (fun iv ↦ ?_) iuv <;>
      simp [realEuclideanCoordinateReindex,
        finProjectionProductCoordinateEquiv, sumFourBlockExchange,
        realEuclideanAppend]

/-- A product of two projected sets has a single projected witness in the
original family.  Both hidden blocks are retained, after exchanging the
middle visible/hidden blocks. -/
private theorem PositiveArityWeakSetStructure.exists_projectionProductWitness
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {A : Set (RealEuclidean n)} {B : Set (RealEuclidean m)}
    (hA : A ∈ wilkieProjectionExpansion S n)
    (hB : B ∈ wilkieProjectionExpansion S m) :
    ∃ (q : ℕ) (Q : Set (RealEuclidean ((n + m) + q))),
      Q ∈ S ((n + m) + q) ∧
        realEuclideanExistentialProjection Q =
          realEuclideanSetProduct A B := by
  obtain ⟨k, C, hC, hCA⟩ := hA
  obtain ⟨l, D, hD, hDB⟩ := hB
  let e := finProjectionProductCoordinateEquiv n m k l
  let Q : Set (RealEuclidean ((n + m) + (k + l))) :=
    realEuclideanCoordinateReindex e '' realEuclideanSetProduct C D
  have hCD : realEuclideanSetProduct C D ∈ S ((n + k) + (m + l)) :=
    hS.ws3_prod (by omega) (by omega) hC hD
  have hQ : Q ∈ S ((n + m) + (k + l)) :=
    hS.toDescriptionReindexBase.coordinateReindex (by omega) hCD e
  refine ⟨k + l, Q, hQ, ?_⟩
  ext xy
  let x : RealEuclidean n := realEuclideanTakeLeft xy
  let y : RealEuclidean m := realEuclideanTakeRight xy
  have hxy : xy = realEuclideanAppend x y :=
    (realEuclideanAppend_takeLeft_takeRight xy).symm
  rw [hxy]
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    realEuclideanSetProduct, realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · rintro ⟨uv, w, hw, heq⟩
    let u : RealEuclidean k := realEuclideanTakeLeft uv
    let v : RealEuclidean l := realEuclideanTakeRight uv
    have huv : uv = realEuclideanAppend u v :=
      (realEuclideanAppend_takeLeft_takeRight uv).symm
    have hcanonical :
        realEuclideanCoordinateReindex e
            (realEuclideanAppend (realEuclideanAppend x u)
              (realEuclideanAppend y v)) =
          realEuclideanAppend (realEuclideanAppend x y) uv := by
      rw [huv]
      exact realEuclideanCoordinateReindex_projectionProduct_append x u y v
    have hwEq :
        w = realEuclideanAppend (realEuclideanAppend x u)
          (realEuclideanAppend y v) := by
      apply (realEuclideanCoordinateReindex e).injective
      exact heq.trans hcanonical.symm
    rw [hwEq] at hw
    rcases hw with ⟨hxu, hyv⟩
    refine ⟨?_, ?_⟩
    · rw [← hCA]
      exact ⟨u, by simpa using hxu⟩
    · rw [← hDB]
      exact ⟨v, by simpa using hyv⟩
  · rintro ⟨hx, hy⟩
    rw [← hCA] at hx
    rw [← hDB] at hy
    obtain ⟨u, hxu⟩ := hx
    obtain ⟨v, hyv⟩ := hy
    refine ⟨realEuclideanAppend u v,
      realEuclideanAppend (realEuclideanAppend x u)
        (realEuclideanAppend y v), ?_, ?_⟩
    · exact ⟨by simpa using hxu, by simpa using hyv⟩
    · exact realEuclideanCoordinateReindex_projectionProduct_append x u y v

/-- Arbitrary final-coordinate projections of members of a weak family again
form a weak family. -/
theorem PositiveArityWeakSetStructure.wilkieProjectionExpansion
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S) :
    PositiveArityWeakSetStructure (wilkieProjectionExpansion S) := by
  refine
    { ws1_inter := ?_
      ws2_polynomialSign := ?_
      ws3_prod := ?_
      ws4_linearEquiv := ?_ }
  · intro n hn A B hA hB
    obtain ⟨q, Q, hQ, hQproj⟩ :=
      hS.exists_projectionProductWitness hn hn hA hB
    let diagonalCylinder : Set (RealEuclidean ((n + n) + q)) :=
      realEuclideanSetProduct (realEuclideanDiagonal n)
        (Set.univ : Set (RealEuclidean q))
    have hdiagonalAffine : IsIntegerAffineSet diagonalCylinder :=
      (isIntegerAffineSet_realEuclideanDiagonal n).prod_univ_right q
    have hdiagonal : diagonalCylinder ∈ S ((n + n) + q) :=
      hS.ws2_polynomialSign (by omega)
        hdiagonalAffine.polynomialSignConstructible
    have hcut : Q ∩ diagonalCylinder ∈ S ((n + n) + q) :=
      hS.ws1_inter (by omega) hQ hdiagonal
    let R : Set (RealEuclidean (n + (n + q))) :=
      charbonnelWitnessReassociation (Q ∩ diagonalCylinder)
    have hR : R ∈ S (n + (n + q)) :=
      hS.toDescriptionReindexBase.coordinateReindex (by omega) hcut
        (finAddAssocCoordinateEquiv n n q).symm
    refine ⟨n + q, R, hR, ?_⟩
    calc
      realEuclideanExistentialProjection R =
          realEuclideanExistentialProjection (n := n) (m := n)
            (realEuclideanExistentialProjection
              (Q ∩ diagonalCylinder)) :=
        realEuclideanExistentialProjection_witnessReassociation _
      _ = realEuclideanExistentialProjection (n := n) (m := n)
            (realEuclideanSetProduct A B ∩ realEuclideanDiagonal n) := by
        rw [realEuclideanExistentialProjection_inter_product_univ,
          hQproj]
      _ = A ∩ B := projection_product_inter_diagonal A B
  · intro n hn A hA
    exact mem_wilkieProjectionExpansion_of_mem
      (hS.ws2_polynomialSign hn hA)
  · intro n m hn hm A B hA hB
    obtain ⟨q, Q, hQ, hQproj⟩ :=
      hS.exists_projectionProductWitness hn hm hA hB
    exact ⟨q, Q, hQ, hQproj⟩
  · intro n hn A hA e
    obtain ⟨q, C, hC, hCA⟩ := hA
    let E := realEuclideanVisibleBlockLinearEquiv e q
    have hEC : E '' C ∈ S (n + q) :=
      hS.ws4_linearEquiv (by omega) hC E
    refine ⟨q, E '' C, hEC, ?_⟩
    rw [realEuclideanExistentialProjection_visibleBlockLinearEquiv_image,
      hCA]

/-! ## Closure at infinity preserves weak structures -/

private theorem wilkieClosedIntersectionCarrier_map_product_univ_right
    {n m : ℕ} (pieces : List (Set (RealEuclidean n))) :
    wilkieClosedIntersectionCarrier
        (pieces.map (fun A ↦ realEuclideanSetProduct A
          (Set.univ : Set (RealEuclidean m)))) =
      realEuclideanSetProduct (wilkieClosedIntersectionCarrier pieces)
        (Set.univ : Set (RealEuclidean m)) := by
  induction pieces with
  | nil =>
      ext v
      simp [realEuclideanSetProduct]
  | cons A pieces ih =>
      simp only [List.map_cons, wilkieClosedIntersectionCarrier_cons,
        closure_realEuclideanSetProduct_of_right_isClosed A isClosed_univ,
        ih]
      exact (realEuclideanSetProduct_inter_left
        (closure A) (wilkieClosedIntersectionCarrier pieces)
        (Set.univ : Set (RealEuclidean m))).symm

private theorem wilkieClosedIntersectionCarrier_map_univ_product_left
    {n m : ℕ} (pieces : List (Set (RealEuclidean m))) :
    wilkieClosedIntersectionCarrier
        (pieces.map (fun B ↦ realEuclideanSetProduct
          (Set.univ : Set (RealEuclidean n)) B)) =
      realEuclideanSetProduct (Set.univ : Set (RealEuclidean n))
        (wilkieClosedIntersectionCarrier pieces) := by
  induction pieces with
  | nil =>
      ext v
      simp [realEuclideanSetProduct]
  | cons B pieces ih =>
      simp only [List.map_cons, wilkieClosedIntersectionCarrier_cons,
        closure_realEuclideanSetProduct_of_left_isClosed B isClosed_univ,
        ih]
      exact (realEuclideanSetProduct_inter_right
        (Set.univ : Set (RealEuclidean n))
        (closure B) (wilkieClosedIntersectionCarrier pieces)).symm

private theorem wilkieClosedIntersectionCarrier_map_linearEquiv_image
    {n : ℕ} (e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n)
    (pieces : List (Set (RealEuclidean n))) :
    wilkieClosedIntersectionCarrier (pieces.map (fun A ↦ e '' A)) =
      e '' wilkieClosedIntersectionCarrier pieces := by
  induction pieces with
  | nil =>
      ext y
      constructor
      · intro _hy
        exact ⟨e.symm y, Set.mem_univ _, e.apply_symm_apply y⟩
      · intro _hy
        exact Set.mem_univ y
  | cons A pieces ih =>
      simp only [List.map_cons, wilkieClosedIntersectionCarrier_cons, ih]
      have hclosure : closure (e '' A) = e '' closure A := by
        change closure (e.toContinuousLinearEquiv '' A) =
          e.toContinuousLinearEquiv '' closure A
        exact (e.toContinuousLinearEquiv.image_closure A).symm
      rw [hclosure]
      exact (Set.image_inter e.injective).symm

/-- Wilkie's closure-at-infinity operation preserves all four weak-family
clauses.  The product clause cylinders each closed factor in the unused
coordinate block; the linear-image clause uses that a linear equivalence is
a homeomorphism. -/
theorem PositiveArityWeakSetStructure.wilkieClosureExpansion
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S) :
    PositiveArityWeakSetStructure (wilkieClosureExpansion S) := by
  refine
    { ws1_inter := ?_
      ws2_polynomialSign := ?_
      ws3_prod := ?_
      ws4_linearEquiv := ?_ }
  · intro n hn A B hA hB
    obtain ⟨A₀, hA₀, left, hleft, hleftCarrier⟩ := hA
    obtain ⟨B₀, hB₀, right, hright, hrightCarrier⟩ := hB
    refine ⟨A₀ ∩ B₀, hS.ws1_inter hn hA₀ hB₀,
      left ++ right, ?_, ?_⟩
    · intro C hC
      rw [List.mem_append] at hC
      exact hC.elim (hleft C) (hright C)
    · rw [wilkieClosedIntersectionCarrier_append,
        ← hleftCarrier, ← hrightCarrier]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
  · intro n hn A hA
    exact mem_wilkieClosureExpansion_of_mem
      (hS.ws2_polynomialSign hn hA)
  · intro n m hn hm A B hA hB
    obtain ⟨A₀, hA₀, left, hleft, hleftCarrier⟩ := hA
    obtain ⟨B₀, hB₀, right, hright, hrightCarrier⟩ := hB
    have hunivN : (Set.univ : Set (RealEuclidean n)) ∈ S n :=
      hS.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
    have hunivM : (Set.univ : Set (RealEuclidean m)) ∈ S m :=
      hS.ws2_polynomialSign hm (polynomialSignConstructible_univ m)
    let leftCylinders := left.map (fun C ↦
      realEuclideanSetProduct C (Set.univ : Set (RealEuclidean m)))
    let rightCylinders := right.map (fun D ↦
      realEuclideanSetProduct (Set.univ : Set (RealEuclidean n)) D)
    refine ⟨realEuclideanSetProduct A₀ B₀,
      hS.ws3_prod hn hm hA₀ hB₀,
      leftCylinders ++ rightCylinders, ?_, ?_⟩
    · intro E hE
      rw [List.mem_append] at hE
      rcases hE with hE | hE
      · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hE
        exact hS.ws3_prod hn hm (hleft C hC) hunivM
      · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hE
        exact hS.ws3_prod hn hm hunivN (hright D hD)
    · simp only [wilkieClosedIntersectionCarrier_append,
        leftCylinders, rightCylinders,
        wilkieClosedIntersectionCarrier_map_product_univ_right,
        wilkieClosedIntersectionCarrier_map_univ_product_left]
      rw [← hleftCarrier, ← hrightCarrier]
      ext v
      simp only [Set.mem_inter_iff, realEuclideanSetProduct,
        Set.mem_ofPred_eq, Set.mem_univ, and_true, true_and]
      tauto
  · intro n hn A hA e
    obtain ⟨A₀, hA₀, pieces, hpieces, hcarrier⟩ := hA
    refine ⟨e '' A₀, hS.ws4_linearEquiv hn hA₀ e,
      pieces.map (fun B ↦ e '' B), ?_, ?_⟩
    · intro B hB
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
      exact hS.ws4_linearEquiv hn (hpieces C hC) e
    · rw [wilkieClosedIntersectionCarrier_map_linearEquiv_image,
        ← Set.image_inter e.injective, hcarrier]

/-! ## The complete successor and the stagewise theorem -/

/-- One complete Wilkie source successor preserves the weak-family
structure. -/
theorem PositiveArityWeakSetStructure.wilkieSourceSuccessor
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S) :
    PositiveArityWeakSetStructure (wilkieSourceSuccessor S) :=
  (hS.wilkieFiniteUnionExpansion.wilkieProjectionExpansion).wilkieClosureExpansion

/-- Every stage in Wilkie's literal hierarchy is weak as soon as its base
family is weak.  This discharges the stagewise hypothesis formerly carried
by the hierarchy API. -/
theorem PositiveArityWeakSetStructure.wilkieSourceStagesAreWeak
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S) :
    WilkieSourceStagesAreWeak S := by
  intro i
  induction i with
  | zero => simpa only [wilkieSourceStage_zero] using hS
  | succ i ih =>
      simpa only [wilkieSourceStage_succ] using ih.wilkieSourceSuccessor

end AbelFormalization
