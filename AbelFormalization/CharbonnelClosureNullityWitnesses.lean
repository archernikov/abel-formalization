import AbelFormalization.CharbonnelSemiClosed
import AbelFormalization.CharbonnelSection5ElementaryInputs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The closed-lift nullity witnesses in Charbonnel section 5.8

This file constructs the auxiliary set used in the last step of
Charbonnel's measure induction.  If

`S = {x | exists y, (x,y) in T}`

and `T` is closed, put

`M = {(x,epsilon) | 0 < epsilon and exists y in T,
  epsilon^2 * sum_i y_i^2 <= 1}`.

The sum-of-squares bound is the polynomial version of the norm bound in the
paper.  Its positive-epsilon fibres are compact, it exhausts every fixed
witness as epsilon tends to zero, and it has exactly the same zero trace.

There is a small interface point hidden by the printed phrase "closed weak
structure".  The family of literal zero sets is a closed description base,
but it is not itself closed under strict polynomial sign conditions.  We
therefore formulate the closed-lift description induction for the exact
closed-description-base operations it uses, plus membership of `univ`, and
then discharge the latter directly by the zero function.  No weak-structure
instance for the literal-zero base is asserted.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Closed lifts over the exact description-base interface -/

/-- The whole Euclidean space is a literal zero set, witnessed by the zero
function. -/
theorem literalZeroSetFamily_univ_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    (Set.univ : Set (RealEuclidean n)) ∈ literalZeroSetFamily G n := by
  refine ⟨0, hG.zero_mem, ?_⟩
  ext x
  simp

/-- Unused-coordinate padding only needs products, coordinate reindexing,
and a positive-arity `univ` generator. -/
theorem ClosedPositiveArityDescriptionBase.exists_witnessPad_description_of_univ
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    (huniv : ∀ {r : ℕ}, 0 < r →
      (Set.univ : Set (RealEuclidean r)) ∈ S r)
    {n q : ℕ} (description : CharbonnelDescription S (n + q))
    (r : ℕ) :
    ∃ padded : CharbonnelDescription S (n + (q + r)),
      padded.carrier = charbonnelWitnessPad description.carrier r := by
  cases r with
  | zero =>
      exact ⟨description,
        (charbonnelWitnessPad_zero description.carrier).symm⟩
  | succ r =>
      have huniv' : (Set.univ : Set (RealEuclidean (r + 1))) ∈ S (r + 1) :=
        huniv (by omega)
      let univDescription : CharbonnelDescription S (r + 1) :=
        .base (by omega) Set.univ huniv'
      obtain ⟨product, hproductCarrier, _hproductRank⟩ :=
        hS.exists_product_description description univDescription
      obtain ⟨padded, hpaddedCarrier, _hpaddedRank⟩ :=
        hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description
          product (finAddAssocCoordinateEquiv n q (r + 1)).symm
      refine ⟨padded, ?_⟩
      calc
        padded.carrier =
            realEuclideanCoordinateReindex
                (finAddAssocCoordinateEquiv n q (r + 1)).symm ''
              product.carrier := hpaddedCarrier
        _ = realEuclideanCoordinateReindex
                (finAddAssocCoordinateEquiv n q (r + 1)).symm ''
              realEuclideanSetProduct description.carrier
                (Set.univ : Set (RealEuclidean (r + 1))) := by
              rw [hproductCarrier]
              simp only [univDescription,
                CharbonnelDescription.carrier_base]
        _ = charbonnelWitnessPad description.carrier (r + 1) := rfl

/-- A closed description lift can be padded while preserving both
closedness and its visible projection. -/
theorem ClosedPositiveArityDescriptionBase.exists_closed_projection_padding_of_univ
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    (huniv : ∀ {r : ℕ}, 0 < r →
      (Set.univ : Set (RealEuclidean r)) ∈ S r)
    {n q : ℕ} (description : CharbonnelDescription S (n + q))
    (hdescription : IsClosed description.carrier) (r : ℕ) :
    ∃ padded : CharbonnelDescription S (n + (q + r)),
      IsClosed padded.carrier ∧
        realEuclideanExistentialProjection (n := n) (m := q + r)
            padded.carrier =
          realEuclideanExistentialProjection (n := n) (m := q)
            description.carrier := by
  obtain ⟨padded, hpadded⟩ :=
    hS.exists_witnessPad_description_of_univ huniv description r
  refine ⟨padded, ?_, ?_⟩
  · rw [hpadded]
    exact isClosed_charbonnelWitnessPad hdescription r
  · rw [hpadded]
    exact realEuclideanExistentialProjection_witnessPad
      description.carrier r

/-- Servi's closed-lift induction uses only the closed description-base
interface and positive-arity membership of `univ`. -/
theorem ClosedPositiveArityDescriptionBase.exists_closed_projection_description_of_univ
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    (huniv : ∀ {r : ℕ}, 0 < r →
      (Set.univ : Set (RealEuclidean r)) ∈ S r)
    {n : ℕ} (description : CharbonnelDescription S n) :
    ∃ (q : ℕ) (lift : CharbonnelDescription S (n + q)),
      IsClosed lift.carrier ∧
        description.carrier =
          realEuclideanExistentialProjection (n := n) (m := q)
            lift.carrier := by
  induction description with
  | @base n hn A hA =>
      refine ⟨0, .base hn A hA, hS.base_isClosed hn hA, ?_⟩
      simp
  | @union n left right ihleft ihright =>
      obtain ⟨q, leftLift, hleftClosed, hleftProjection⟩ := ihleft
      obtain ⟨r, rightLift, hrightClosed, hrightProjection⟩ := ihright
      obtain ⟨leftPadded, hleftPaddedClosed, hleftPaddedProjection⟩ :=
        hS.exists_closed_projection_padding_of_univ huniv leftLift
          hleftClosed r
      have hrightPadding :
          ∃ rightPadded : CharbonnelDescription S (n + (q + r)),
            IsClosed rightPadded.carrier ∧
              realEuclideanExistentialProjection (n := n) (m := q + r)
                  rightPadded.carrier =
                realEuclideanExistentialProjection (n := n) (m := r)
                  rightLift.carrier := by
        have hpadding :=
          hS.exists_closed_projection_padding_of_univ huniv rightLift
            hrightClosed q
        rw [Nat.add_comm r q] at hpadding
        exact hpadding
      obtain ⟨rightPadded, hrightPaddedClosed,
        hrightPaddedProjection⟩ := hrightPadding
      let answer : CharbonnelDescription S (n + (q + r)) :=
        .union leftPadded rightPadded
      refine ⟨q + r, answer, ?_, ?_⟩
      · exact hleftPaddedClosed.union hrightPaddedClosed
      · calc
          (CharbonnelDescription.union left right).carrier =
              left.carrier ∪ right.carrier := rfl
          _ = realEuclideanExistentialProjection leftLift.carrier ∪
                realEuclideanExistentialProjection rightLift.carrier := by
              rw [hleftProjection, hrightProjection]
          _ = realEuclideanExistentialProjection leftPadded.carrier ∪
                realEuclideanExistentialProjection rightPadded.carrier := by
              rw [hleftPaddedProjection, hrightPaddedProjection]
          _ = realEuclideanExistentialProjection
                (leftPadded.carrier ∪ rightPadded.carrier) :=
              (realEuclideanExistentialProjection_union _ _).symm
          _ = realEuclideanExistentialProjection answer.carrier := rfl
  | @integerAffineInter n inner L hL ih =>
      obtain ⟨q, lift, hliftClosed, hinnerProjection⟩ := ih
      let cylinder : Set (RealEuclidean (n + q)) :=
        realEuclideanSetProduct L (Set.univ : Set (RealEuclidean q))
      have hcylinderAffine : IsIntegerAffineSet cylinder :=
        hL.prod_univ_right q
      let answer : CharbonnelDescription S (n + q) :=
        .integerAffineInter lift cylinder hcylinderAffine
      refine ⟨q, answer, ?_, ?_⟩
      · exact hliftClosed.inter hcylinderAffine.isClosed
      · calc
          (CharbonnelDescription.integerAffineInter inner L hL).carrier =
              inner.carrier ∩ L := rfl
          _ = realEuclideanExistentialProjection lift.carrier ∩ L := by
              rw [hinnerProjection]
          _ = realEuclideanExistentialProjection
                (lift.carrier ∩ cylinder) :=
              (realEuclideanExistentialProjection_inter_product_univ
                lift.carrier L).symm
          _ = realEuclideanExistentialProjection answer.carrier := rfl
  | @projection n q hn inner ih =>
      obtain ⟨r, lift, hliftClosed, hinnerProjection⟩ := ih
      obtain ⟨answer, hanswerCarrier, _hanswerRank⟩ :=
        hS.toPositiveArityDescriptionReindexBase.exists_coordinateReindex_description
          lift (finAddAssocCoordinateEquiv n q r).symm
      refine ⟨q + r, answer, ?_, ?_⟩
      · rw [hanswerCarrier]
        exact isClosed_charbonnelWitnessReassociation hliftClosed
      · calc
          (CharbonnelDescription.projection hn inner).carrier =
              realEuclideanExistentialProjection inner.carrier := rfl
          _ = realEuclideanExistentialProjection
                (realEuclideanExistentialProjection lift.carrier) := by
              rw [hinnerProjection]
          _ = realEuclideanExistentialProjection
                (charbonnelWitnessReassociation lift.carrier) :=
              (realEuclideanExistentialProjection_witnessReassociation
                lift.carrier).symm
          _ = realEuclideanExistentialProjection answer.carrier := by
              rw [hanswerCarrier]
              rfl
  | @topologicalClosure n inner ih =>
      let answer : CharbonnelDescription S n :=
        .topologicalClosure inner
      refine ⟨0, answer, isClosed_closure, ?_⟩
      simp [answer]

/-- Family-level closed-lift theorem over the reduced interface. -/
theorem ClosedPositiveArityDescriptionBase.charbonnelClosure_semiClosed_of_univ
    {S : EuclideanSetFamily} (hS : ClosedPositiveArityDescriptionBase S)
    (huniv : ∀ {r : ℕ}, 0 < r →
      (Set.univ : Set (RealEuclidean r)) ∈ S r)
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) :
    ∃ (q : ℕ) (B : Set (RealEuclidean (n + q))),
      IsClosed B ∧ B ∈ charbonnelClosure S (n + q) ∧
        A = realEuclideanExistentialProjection (n := n) (m := q) B := by
  obtain ⟨description, hdescription⟩ := hA
  obtain ⟨q, lift, hliftClosed, hliftProjection⟩ :=
    hS.exists_closed_projection_description_of_univ huniv description
  refine ⟨q, lift.carrier, hliftClosed, ⟨lift, rfl⟩, ?_⟩
  rw [← hdescription]
  exact hliftProjection

/-- Every member of the literal-zero Charbonnel closure has a closed lift.
This is the form of Servi 3.3.9 needed by Charbonnel 5.8. -/
theorem literalZeroSet_charbonnelClosure_semiClosed
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure (literalZeroSetFamily G) n) :
    ∃ (q : ℕ) (B : Set (RealEuclidean (n + q))),
      IsClosed B ∧
        B ∈ charbonnelClosure (literalZeroSetFamily G) (n + q) ∧
        A = realEuclideanExistentialProjection (n := n) (m := q) B := by
  exact
    (literalZeroSetFamily_closedDescriptionBase hG hsmooth).charbonnelClosure_semiClosed_of_univ
        (fun {r} _hr ↦ literalZeroSetFamily_univ_mem hG r) hA

/-! ## Moving the new positive parameter in front of the witnesses -/

/-- Extend a coordinate equivalence on a final block by the identity on a
fixed initial block. -/
def finPrefixCoordinateEquiv (n : ℕ) {q r : ℕ} (e : Fin q ≃ Fin r) :
    Fin (n + q) ≃ Fin (n + r) :=
  (finSumFinEquiv : Fin n ⊕ Fin q ≃ Fin (n + q)).symm |>.trans
    ((Equiv.sumCongr (Equiv.refl (Fin n)) e).trans
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)))

@[simp]
theorem realEuclideanCoordinateReindex_trans
    {n m k : ℕ} (e : Fin m ≃ Fin n) (f : Fin k ≃ Fin m)
    (x : RealEuclidean n) :
    realEuclideanCoordinateReindex (f.trans e) x =
      realEuclideanCoordinateReindex f
        (realEuclideanCoordinateReindex e x) :=
  rfl

@[simp]
theorem realEuclideanCoordinateReindex_finPrefix_append
    {n q r : ℕ} (e : Fin q ≃ Fin r)
    (x : RealEuclidean n) (y : RealEuclidean r) :
    realEuclideanCoordinateReindex (finPrefixCoordinateEquiv n e)
        (realEuclideanAppend x y) =
      realEuclideanAppend x (realEuclideanCoordinateReindex e y) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [finPrefixCoordinateEquiv, realEuclideanCoordinateReindex,
      realEuclideanAppend]

/-- Coordinate permutation sending the flat order `(x,y,epsilon)` to
`(x,epsilon,y)`. -/
def charbonnelMoveLastBeforeWitnessesEquiv (n q : ℕ) :
    Fin ((n + 1) + q) ≃ Fin ((n + q) + 1) :=
  (finAddAssocCoordinateEquiv n 1 q).trans
    ((finPrefixCoordinateEquiv n (@finAddFlip 1 q)).trans
      (finAddAssocCoordinateEquiv n q 1).symm)

@[simp]
theorem realEuclideanCoordinateReindex_moveLastBeforeWitnesses
    {n q : ℕ} (x : RealEuclidean n) (y : RealEuclidean q)
    (epsilon : RealEuclidean 1) :
    realEuclideanCoordinateReindex
        (charbonnelMoveLastBeforeWitnessesEquiv n q)
        (realEuclideanAppend (realEuclideanAppend x y) epsilon) =
      realEuclideanAppend (realEuclideanAppend x epsilon) y := by
  rw [charbonnelMoveLastBeforeWitnessesEquiv,
    realEuclideanCoordinateReindex_trans,
    realEuclideanCoordinateReindex_trans,
    realEuclideanCoordinateReindex_finAddAssoc_symm_append,
    realEuclideanCoordinateReindex_finPrefix_append,
    realEuclideanCoordinateReindex_finAddFlip_append,
    realEuclideanCoordinateReindex_finAddAssoc_append]

/-- The cylinder `T × R`, reordered from `(x,y,epsilon)` to
`(x,epsilon,y)`. -/
def charbonnelClosureLiftCylinder {n q : ℕ}
    (T : Set (RealEuclidean (n + q))) :
    Set (RealEuclidean ((n + 1) + q)) :=
  realEuclideanCoordinateReindex
      (charbonnelMoveLastBeforeWitnessesEquiv n q) ''
    realEuclideanSetProduct T (Set.univ : Set (RealEuclidean 1))

@[simp]
theorem mem_charbonnelClosureLiftCylinder_append_iff
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    (x : RealEuclidean n) (epsilon : RealEuclidean 1)
    (y : RealEuclidean q) :
    realEuclideanAppend (realEuclideanAppend x epsilon) y ∈
        charbonnelClosureLiftCylinder T ↔
      realEuclideanAppend x y ∈ T := by
  let E := realEuclideanCoordinateReindex
    (charbonnelMoveLastBeforeWitnessesEquiv n q)
  have hcanonical :
      E (realEuclideanAppend (realEuclideanAppend x y) epsilon) =
        realEuclideanAppend (realEuclideanAppend x epsilon) y :=
    realEuclideanCoordinateReindex_moveLastBeforeWitnesses x y epsilon
  constructor
  · rintro ⟨w, hw, hwEq⟩
    have hwCanonical :
        w = realEuclideanAppend (realEuclideanAppend x y) epsilon :=
      E.injective (hwEq.trans hcanonical.symm)
    rw [hwCanonical] at hw
    simpa [realEuclideanSetProduct] using hw
  · intro hxy
    refine ⟨realEuclideanAppend (realEuclideanAppend x y) epsilon, ?_,
      hcanonical⟩
    simpa [realEuclideanSetProduct] using hxy

/-- Coordinate reindexing preserves the generated Charbonnel closure when
it preserves the base descriptions. -/
theorem PositiveArityDescriptionReindexBase.charbonnelClosure_coordinateReindex
    {S : EuclideanSetFamily} (hS : PositiveArityDescriptionReindexBase S)
    {n m : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) (e : Fin m ≃ Fin n) :
    realEuclideanCoordinateReindex e '' A ∈ charbonnelClosure S m := by
  obtain ⟨description, hdescription⟩ := hA
  obtain ⟨reindexed, hreindexed, _hrank⟩ :=
    hS.exists_coordinateReindex_description description e
  refine ⟨reindexed, ?_⟩
  rw [hreindexed, hdescription]

/-- The reordered cylinder belongs to the literal-zero Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_liftCylinder_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    (hT : T ∈ charbonnelClosure (literalZeroSetFamily G) (n + q)) :
    charbonnelClosureLiftCylinder T ∈
      charbonnelClosure (literalZeroSetFamily G) ((n + 1) + q) := by
  have huniv : (Set.univ : Set (RealEuclidean 1)) ∈
      charbonnelClosure (literalZeroSetFamily G) 1 :=
    mem_charbonnelClosure_of_mem (by omega)
      (literalZeroSetFamily_univ_mem hG 1)
  have hproduct : realEuclideanSetProduct T
      (Set.univ : Set (RealEuclidean 1)) ∈
      charbonnelClosure (literalZeroSetFamily G) ((n + q) + 1) :=
    literalZeroSet_charbonnelClosure_product hG hsmooth hT huniv
  exact
    (literalZeroSetFamily_descriptionReindexBase hG).charbonnelClosure_coordinateReindex
        hproduct
        (charbonnelMoveLastBeforeWitnessesEquiv n q)

/-! ## The polynomial compact-fibre constraint -/

/-- The squared Euclidean size used to exhaust a witness block. -/
def charbonnelWitnessSquaredSize {q : ℕ} (y : RealEuclidean q) : ℝ :=
  ∑ i : Fin q, (y i) ^ 2

theorem charbonnelWitnessSquaredSize_nonneg {q : ℕ}
    (y : RealEuclidean q) : 0 ≤ charbonnelWitnessSquaredSize y :=
  Finset.sum_nonneg fun i _hi ↦ sq_nonneg (y i)

theorem continuous_charbonnelWitnessSquaredSize {q : ℕ} :
    Continuous (@charbonnelWitnessSquaredSize q) := by
  exact continuous_finsetSum Finset.univ fun i _hi ↦
    (continuous_apply i).pow 2

/-- The polynomial `1 - epsilon^2 * sum_i y_i^2` on coordinates
`(x,epsilon,y)`. -/
def charbonnelClosureLiftBoundPolynomial (n q : ℕ) :
    MvPolynomial (Fin ((n + 1) + q)) ℝ :=
  MvPolynomial.C 1 -
    MvPolynomial.X (Fin.castAdd q (Fin.last n)) ^ 2 *
      ∑ i : Fin q,
        MvPolynomial.X (Fin.natAdd (n + 1) i) ^ 2

@[simp]
theorem charbonnelClosureLiftBoundPolynomial_eval
    {n q : ℕ} (x : RealEuclidean n) (epsilon : RealEuclidean 1)
    (y : RealEuclidean q) :
    MvPolynomial.eval (realEuclideanAppend
        (realEuclideanAppend x epsilon) y)
        (charbonnelClosureLiftBoundPolynomial n q) =
      1 - (epsilon 0) ^ 2 * charbonnelWitnessSquaredSize y := by
  simp [charbonnelClosureLiftBoundPolynomial,
    charbonnelWitnessSquaredSize]

/-- A weak polynomial sign formula for a non-strict inequality. -/
theorem polynomialSignConstructible_nonnegative
    {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    PolynomialSignConstructible d
      {x : RealEuclidean d | 0 ≤ MvPolynomial.eval x P} := by
  rw [show {x : RealEuclidean d | 0 ≤ MvPolynomial.eval x P} =
      {x | MvPolynomial.eval x P = 0} ∪
        {x | 0 < MvPolynomial.eval x P} by
    ext x
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro hx
      rcases hx.eq_or_lt with hx | hx
      · exact Or.inl hx.symm
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact hx.symm.le
      · exact hx.le]
  exact .union (.zero P) (.pos P)

/-- Positivity of epsilon together with the polynomial compact-fibre bound. -/
def charbonnelClosureLiftConstraint (n q : ℕ) :
    Set (RealEuclidean ((n + 1) + q)) :=
  {v | 0 < v (Fin.castAdd q (Fin.last n))} ∩
    {v | 0 ≤ MvPolynomial.eval v
      (charbonnelClosureLiftBoundPolynomial n q)}

theorem polynomialSignConstructible_charbonnelClosureLiftConstraint
    (n q : ℕ) :
    PolynomialSignConstructible ((n + 1) + q)
      (charbonnelClosureLiftConstraint n q) := by
  exact .inter
    (by
      simpa only [MvPolynomial.eval_X] using
        (PolynomialSignConstructible.pos
          (MvPolynomial.X (Fin.castAdd q (Fin.last n)))))
    (polynomialSignConstructible_nonnegative
      (charbonnelClosureLiftBoundPolynomial n q))

/-! ## The section 5.8 carrier and its membership -/

/-- The polynomially bounded lift used in Charbonnel 5.8. -/
def charbonnelClosureNullityCarrier {n q : ℕ}
    (T : Set (RealEuclidean (n + q))) :
    Set (RealEuclidean (n + 1)) :=
  {z | 0 < z (Fin.last n) ∧
    ∃ y : RealEuclidean q,
      realEuclideanAppend (realEuclideanDropLastLinearMap n z) y ∈ T ∧
      (z (Fin.last n)) ^ 2 * charbonnelWitnessSquaredSize y ≤ 1}

/-- The carrier is the projection of the reordered closed-lift cylinder cut
by the polynomial compact-fibre constraint. -/
theorem charbonnelClosureNullityCarrier_eq_projection
    {n q : ℕ} (T : Set (RealEuclidean (n + q))) :
    charbonnelClosureNullityCarrier T =
      realEuclideanExistentialProjection (n := n + 1) (m := q)
        (charbonnelClosureLiftCylinder T ∩
          charbonnelClosureLiftConstraint n q) := by
  ext z
  let x : RealEuclidean n := realEuclideanDropLastLinearMap n z
  let epsilon : RealEuclidean 1 := fun _ ↦ z (Fin.last n)
  have hz : realEuclideanAppend x epsilon = z := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [epsilon]
    · have hj : j.castSucc = Fin.castAdd 1 j := Fin.ext rfl
      rw [hj, realEuclideanAppend_castAdd]
      rfl
  rw [← hz]
  simp only [charbonnelClosureNullityCarrier,
    realEuclideanExistentialProjection, mem_ofPred_eq, mem_inter_iff,
    mem_charbonnelClosureLiftCylinder_append_iff,
    charbonnelClosureLiftConstraint,
    realEuclideanAppend_natAdd, realEuclideanAppend_castAdd,
    realEuclideanAppend_last_one,
    charbonnelClosureLiftBoundPolynomial_eval]
  simp [x, epsilon, charbonnelWitnessSquaredSize,
    realEuclideanDropLastLinearMap_append_one,
    and_assoc, and_left_comm, and_comm]

/-- The section 5.8 carrier stays in the literal-zero Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_nullityCarrier_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n q : ℕ} (hn : 0 < n)
    {T : Set (RealEuclidean (n + q))}
    (hT : T ∈ charbonnelClosure (literalZeroSetFamily G) (n + q)) :
    charbonnelClosureNullityCarrier T ∈
      charbonnelClosure (literalZeroSetFamily G) (n + 1) := by
  have hcylinder :=
    literalZeroSet_charbonnelClosure_liftCylinder_mem hG hsmooth hT
  have hconstraint : charbonnelClosureLiftConstraint n q ∈
      charbonnelClosure (literalZeroSetFamily G) ((n + 1) + q) :=
    ((polynomialSignConstructible_charbonnelClosureLiftConstraint n q)
      |>.isProjectedZeroSet hG)
      |>.mem_literalZeroSet_charbonnelClosure (by omega)
  have hinter : charbonnelClosureLiftCylinder T ∩
      charbonnelClosureLiftConstraint n q ∈
      charbonnelClosure (literalZeroSetFamily G) ((n + 1) + q) :=
    literalZeroSet_charbonnelClosure_inter hG hsmooth hcylinder hconstraint
  have hprojection := charbonnelClosure_projection (by omega : 0 < n + 1)
    (n := n + 1) (k := q) hinter
  rwa [← charbonnelClosureNullityCarrier_eq_projection T] at hprojection

/-! ## Relative closedness above positive epsilon -/

/-- A thresholded version of the carrier.  At `epsilon >= delta > 0`, all
hidden witnesses lie in one fixed compact ball. -/
def charbonnelClosureNullityCarrierAtLeast {n q : ℕ}
    (T : Set (RealEuclidean (n + q))) (delta : ℝ) :
    Set (RealEuclidean (n + 1)) :=
  {z | delta ≤ z (Fin.last n) ∧
    ∃ y : RealEuclidean q,
      realEuclideanAppend (realEuclideanDropLastLinearMap n z) y ∈ T ∧
      (z (Fin.last n)) ^ 2 * charbonnelWitnessSquaredSize y ≤ 1}

/-- The sum-of-squares inequality and `delta <= epsilon` bound the hidden
witness in the sup-norm ball of radius `delta⁻¹`. -/
theorem norm_le_inv_of_closureLift_bound
    {q : ℕ} {delta epsilon : ℝ} (hdelta : 0 < delta)
    (hdeltaEpsilon : delta ≤ epsilon) (y : RealEuclidean q)
    (hbound : epsilon ^ 2 * charbonnelWitnessSquaredSize y ≤ 1) :
    ‖y‖ ≤ delta⁻¹ := by
  have hepsilon : 0 ≤ epsilon := hdelta.le.trans hdeltaEpsilon
  have hdeltaSq : delta ^ 2 ≤ epsilon ^ 2 :=
    (sq_le_sq₀ hdelta.le hepsilon).2 hdeltaEpsilon
  have hinv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  rw [pi_norm_le_iff_of_nonneg hinv]
  intro i
  have hi : (y i) ^ 2 ≤ charbonnelWitnessSquaredSize y := by
    exact Finset.single_le_sum
      (fun j _hj ↦ sq_nonneg (y j)) (Finset.mem_univ i)
  have hsquare : delta ^ 2 * (y i) ^ 2 ≤ 1 :=
    calc
      delta ^ 2 * (y i) ^ 2 ≤ epsilon ^ 2 * (y i) ^ 2 :=
        mul_le_mul_of_nonneg_right hdeltaSq (sq_nonneg (y i))
      _ ≤ epsilon ^ 2 * charbonnelWitnessSquaredSize y :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg epsilon)
      _ ≤ 1 := hbound
  have hmulSquare : (delta * |y i|) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa [mul_pow, sq_abs] using hsquare
  have hmul : delta * |y i| ≤ 1 :=
    (sq_le_sq₀ (mul_nonneg hdelta.le (abs_nonneg _)) zero_le_one).1
      hmulSquare
  have habs : |y i| ≤ delta⁻¹ * 1 :=
    (le_inv_mul_iff₀ hdelta).2 hmul
  simpa using habs

/-- Every positive-threshold carrier is closed.  The proof projects a closed
incidence set along a compact hidden-coordinate subtype. -/
theorem isClosed_charbonnelClosureNullityCarrierAtLeast
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    (hT : IsClosed T) {delta : ℝ} (hdelta : 0 < delta) :
    IsClosed (charbonnelClosureNullityCarrierAtLeast T delta) := by
  let K : Set (RealEuclidean q) := Metric.closedBall 0 delta⁻¹
  let Y := {y : RealEuclidean q // y ∈ K}
  letI : CompactSpace Y :=
    isCompact_iff_compactSpace.mp
      (isCompact_closedBall (0 : RealEuclidean q) delta⁻¹)
  let appendMap : RealEuclidean (n + 1) × Y → RealEuclidean (n + q) :=
    fun p ↦ realEuclideanAppend
      (realEuclideanDropLastLinearMap n p.1) p.2.1
  have happendMap : Continuous appendMap := by
    let E := (realEuclideanAppendLinearEquiv n q).toContinuousLinearEquiv
    change Continuous (fun p : RealEuclidean (n + 1) × Y ↦
      E (realEuclideanDropLastLinearMap n p.1, p.2.1))
    exact E.continuous.comp
      (((realEuclideanDropLastLinearMap n).continuous_of_finiteDimensional.comp
          continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hepsilon : Continuous
      (fun p : RealEuclidean (n + 1) × Y ↦ p.1 (Fin.last n)) :=
    (continuous_apply (Fin.last n)).comp continuous_fst
  have hsize : Continuous
      (fun p : RealEuclidean (n + 1) × Y ↦
        charbonnelWitnessSquaredSize p.2.1) :=
    continuous_charbonnelWitnessSquaredSize.comp
      (continuous_subtype_val.comp continuous_snd)
  let D : Set (RealEuclidean (n + 1) × Y) :=
    appendMap ⁻¹' T ∩
      ({p | delta ≤ p.1 (Fin.last n)} ∩
        {p | (p.1 (Fin.last n)) ^ 2 *
          charbonnelWitnessSquaredSize p.2.1 ≤ 1})
  have hD : IsClosed D := by
    exact (hT.preimage happendMap).inter
      ((isClosed_le continuous_const hepsilon).inter
        (isClosed_le ((hepsilon.pow 2).mul hsize) continuous_const))
  have hImage : Prod.fst '' D =
      charbonnelClosureNullityCarrierAtLeast T delta := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨hp.2.1, p.2.1, hp.1, hp.2.2⟩
    · rintro ⟨hdeltaZ, y, hyT, hyBound⟩
      have hyBall : y ∈ K := by
        change dist y 0 ≤ delta⁻¹
        simpa [dist_zero_right] using
          norm_le_inv_of_closureLift_bound hdelta hdeltaZ y hyBound
      let yK : Y := ⟨y, hyBall⟩
      exact ⟨(z, yK), ⟨hyT, hdeltaZ, hyBound⟩, rfl⟩
  rw [← hImage]
  exact isClosedMap_fst_of_compactSpace D hD

/-- A thresholded carrier with positive threshold is contained in the
unthresholded positive carrier. -/
theorem charbonnelClosureNullityCarrierAtLeast_subset
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    {delta : ℝ} (hdelta : 0 < delta) :
    charbonnelClosureNullityCarrierAtLeast T delta ⊆
      charbonnelClosureNullityCarrier T := by
  rintro z ⟨hdeltaZ, y, hyT, hyBound⟩
  exact ⟨hdelta.trans_le hdeltaZ, y, hyT, hyBound⟩

/-- The carrier is relatively closed in the positive-last-coordinate
half-space. -/
theorem charbonnelClosureNullityCarrier_relativelyClosed
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    (hT : IsClosed T) :
    CharbonnelRelativelyClosedInPositiveLast
      (charbonnelClosureNullityCarrier T) := by
  refine ⟨?_, ?_⟩
  · rintro z hz
    exact hz.1
  · rw [← closure_subset_iff_isClosed]
    intro z hz
    let delta : ℝ := z.1 (Fin.last n) / 2
    have hdelta : 0 < delta := half_pos z.2
    let U : Set (charbonnelPositiveLastCoordinateLocus n) :=
      {w | delta < w.1 (Fin.last n)}
    have hUopen : IsOpen U :=
      isOpen_lt continuous_const
        ((continuous_apply (Fin.last n)).comp continuous_subtype_val)
    have hzU : z ∈ U := by
      change z.1 (Fin.last n) / 2 < z.1 (Fin.last n)
      exact half_lt_self z.2
    have hU : U ∈ 𝓝 z := hUopen.mem_nhds hzU
    have hzInter := mem_closure_inter_of_mem_nhds hU hz
    have hmaps : MapsTo
        (fun w : charbonnelPositiveLastCoordinateLocus n ↦
          (w : RealEuclidean (n + 1)))
        (((fun w : charbonnelPositiveLastCoordinateLocus n ↦
            (w : RealEuclidean (n + 1))) ⁻¹'
              charbonnelClosureNullityCarrier T) ∩ U)
        (charbonnelClosureNullityCarrierAtLeast T delta) := by
      rintro w ⟨hwM, hwU⟩
      exact ⟨hwU.le, hwM.2⟩
    have hzThresholdClosure : z.1 ∈
        closure (charbonnelClosureNullityCarrierAtLeast T delta) :=
      map_mem_closure continuous_subtype_val hzInter hmaps
    have hzThreshold : z.1 ∈
        charbonnelClosureNullityCarrierAtLeast T delta :=
      (isClosed_charbonnelClosureNullityCarrierAtLeast hT hdelta).closure_eq ▸
        hzThresholdClosure
    exact charbonnelClosureNullityCarrierAtLeast_subset hdelta hzThreshold

/-! ## Nullity by the coordinate-product Fubini argument -/

/-- The cylinder over a null subset of `RealEuclidean n` is null after one
new coordinate is appended. -/
theorem volume_dropLast_preimage_eq_zero
    {n : ℕ} {S : Set (RealEuclidean n)}
    (hS : (volume : Measure (RealEuclidean n)) S = 0) :
    (volume : Measure (RealEuclidean (n + 1)))
      ((realEuclideanDropLastLinearMap n) ⁻¹' S) = 0 := by
  obtain ⟨B, hSB, hBmeasurable, hBnull⟩ :=
    exists_measurable_superset_of_null hS
  let E := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  have hproduct : (volume : Measure (ℝ × RealEuclidean n))
      ((Set.univ : Set ℝ) ×ˢ B) = 0 := by
    rw [Measure.volume_eq_prod]
    apply Measure.measure_prod_null_of_ae_null
      (MeasurableSet.univ.prod hBmeasurable)
    exact Filter.Eventually.of_forall fun t ↦ by
      simpa using hBnull
  have hsecond (z : RealEuclidean (n + 1)) :
      (E z).2 = realEuclideanDropLastLinearMap n z := by
    funext j
    change z ((Fin.last n).succAbove j) = z j.castSucc
    rw [Fin.succAbove_last_apply]
  have hpreimage : E ⁻¹' ((Set.univ : Set ℝ) ×ˢ B) =
      (realEuclideanDropLastLinearMap n) ⁻¹' B := by
    ext z
    change ((E z).1 ∈ (Set.univ : Set ℝ) ∧ (E z).2 ∈ B) ↔
      realEuclideanDropLastLinearMap n z ∈ B
    simp [hsecond]
  apply measure_mono_null (preimage_mono hSB)
  rw [← hpreimage]
  exact (volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).quasiMeasurePreserving.preimage_null
      hproduct

/-- The section 5.8 carrier lies over the source set. -/
theorem charbonnelClosureNullityCarrier_subset_dropLast_preimage
    {n q : ℕ} {S : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + q))}
    (hprojection : S =
      realEuclideanExistentialProjection (n := n) (m := q) T) :
    charbonnelClosureNullityCarrier T ⊆
      (realEuclideanDropLastLinearMap n) ⁻¹' S := by
  rintro z ⟨_hzPositive, y, hyT, _hyBound⟩
  rw [hprojection]
  exact ⟨y, hyT⟩

/-- Source nullity therefore implies nullity of the section 5.8 carrier. -/
theorem volume_charbonnelClosureNullityCarrier_eq_zero
    {n q : ℕ} {S : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + q))}
    (hprojection : S =
      realEuclideanExistentialProjection (n := n) (m := q) T)
    (hS : (volume : Measure (RealEuclidean n)) S = 0) :
    (volume : Measure (RealEuclidean (n + 1)))
      (charbonnelClosureNullityCarrier T) = 0 := by
  exact measure_mono_null
    (charbonnelClosureNullityCarrier_subset_dropLast_preimage hprojection)
    (volume_dropLast_preimage_eq_zero hS)

/-! ## The zero trace is exactly the source closure -/

/-- Every source point occurs as a limit of the positive bounded-lift
carrier, because a fixed witness satisfies the bound for every sufficiently
small positive epsilon. -/
theorem charbonnelAppendLastCoordinate_zero_mem_closure_nullityCarrier
    {n q : ℕ} {S : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + q))}
    (hprojection : S =
      realEuclideanExistentialProjection (n := n) (m := q) T)
    {x : RealEuclidean n} (hx : x ∈ S) :
    charbonnelAppendLastCoordinate x 0 ∈
      closure (charbonnelClosureNullityCarrier T) := by
  rw [hprojection] at hx
  obtain ⟨y, hyT⟩ := hx
  rw [Metric.mem_closure_iff]
  intro r hr
  let a : ℝ := charbonnelWitnessSquaredSize y
  let epsilon : ℝ := min (r / 2) (1 / (1 + a))
  have ha : 0 ≤ a := charbonnelWitnessSquaredSize_nonneg y
  have hdenom : 0 < 1 + a := by linarith
  have hepsilon : 0 < epsilon := by
    exact lt_min (half_pos hr) (one_div_pos.mpr hdenom)
  have hepsilonR : epsilon < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  have hepsilonBound : epsilon ≤ 1 / (1 + a) := min_le_right _ _
  have hepsilonMul : epsilon * (1 + a) ≤ 1 :=
    (le_div_iff₀ hdenom).1 hepsilonBound
  have hepsilonOne : epsilon ≤ 1 := by
    have hnonneg : 0 ≤ epsilon * a :=
      mul_nonneg hepsilon.le ha
    nlinarith
  have hmass : epsilon ^ 2 * charbonnelWitnessSquaredSize y ≤ 1 := by
    change epsilon ^ 2 * a ≤ 1
    calc
      epsilon ^ 2 * a = epsilon * (epsilon * a) := by ring
      _ ≤ 1 * (epsilon * a) :=
        mul_le_mul_of_nonneg_right hepsilonOne
          (mul_nonneg hepsilon.le ha)
      _ = epsilon * a := one_mul _
      _ ≤ epsilon * (1 + a) :=
        mul_le_mul_of_nonneg_left (by linarith) hepsilon.le
      _ ≤ 1 := hepsilonMul
  refine ⟨charbonnelAppendLastCoordinate x epsilon, ?_, ?_⟩
  · refine ⟨?_, y, ?_, ?_⟩
    · simpa only [charbonnelAppendLastCoordinate_last] using hepsilon
    · simpa [charbonnelAppendLastCoordinate,
        realEuclideanDropLastLinearMap_append_one] using hyT
    · simpa only [charbonnelAppendLastCoordinate_last] using hmass
  · apply (dist_pi_lt_iff hr).2
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [charbonnelAppendLastCoordinate, Real.dist_eq,
        abs_of_pos hepsilon] using hepsilonR
    · simpa only [charbonnelAppendLastCoordinate_castSucc, dist_self] using hr

/-- The zero section of the carrier closure is the closure of the source. -/
theorem charbonnelZeroSection_closure_nullityCarrier
    {n q : ℕ} {S : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + q))}
    (hprojection : S =
      realEuclideanExistentialProjection (n := n) (m := q) T) :
    charbonnelZeroSection (closure (charbonnelClosureNullityCarrier T)) =
      closure S := by
  apply Subset.antisymm
  · intro x hx
    have hmap : MapsTo (realEuclideanDropLastLinearMap n)
        (charbonnelClosureNullityCarrier T) S := by
      intro z hz
      exact charbonnelClosureNullityCarrier_subset_dropLast_preimage
        hprojection hz
    have hx' := map_mem_closure
      (realEuclideanDropLastLinearMap n).continuous_of_finiteDimensional
      hx hmap
    simpa [charbonnelZeroSection, charbonnelAppendLastCoordinate,
      realEuclideanDropLastLinearMap_append_one] using hx'
  · intro x hx
    have hmap : MapsTo
        (fun u : RealEuclidean n ↦ charbonnelAppendLastCoordinate u 0)
        S (closure (charbonnelClosureNullityCarrier T)) := by
      intro u hu
      exact charbonnelAppendLastCoordinate_zero_mem_closure_nullityCarrier
        hprojection hu
    have hx' := map_mem_closure
      continuous_charbonnelAppendLastCoordinate_zero hx hmap
    simpa [charbonnelZeroSection] using hx'

/-- The positive zero trace of the section 5.8 carrier is exactly
`closure S`. -/
theorem charbonnelPositiveZeroTrace_nullityCarrier
    {n q : ℕ} {S : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + q))}
    (hprojection : S =
      realEuclideanExistentialProjection (n := n) (m := q) T) :
    charbonnelPositiveZeroTrace (charbonnelClosureNullityCarrier T) =
      closure S := by
  rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure]
  · exact charbonnelZeroSection_closure_nullityCarrier hprojection
  · rintro z hz
    exact hz.1

/-! ## Assembly of the closure-nullity witness interface -/

/-- The closed lift of a literal-zero Charbonnel member yields the complete
section 5.8 nullity witness. -/
theorem literalZeroSet_charbonnelClosure_nullityWitness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (hn : 0 < n) {S : Set (RealEuclidean n)}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) n) :
    Nonempty (CharbonnelClosureNullityWitness
      (charbonnelClosure (literalZeroSetFamily G)) n S) := by
  obtain ⟨q, T, hTclosed, hTmem, hprojection⟩ :=
    literalZeroSet_charbonnelClosure_semiClosed hG hsmooth hS
  refine ⟨{
    carrier := charbonnelClosureNullityCarrier T
    mem := literalZeroSet_charbonnelClosure_nullityCarrier_mem
      hG hsmooth hn hTmem
    relativelyClosed :=
      charbonnelClosureNullityCarrier_relativelyClosed hTclosed
    null_of_source_null := fun hSnull ↦
      volume_charbonnelClosureNullityCarrier_eq_zero hprojection hSnull
    positiveZeroTrace_eq_closure :=
      charbonnelPositiveZeroTrace_nullityCarrier hprojection }⟩

/-- Charbonnel section 5.8 supplies closure-nullity witnesses in every
positive arity for the literal-zero Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_hasClosureNullityWitnesses
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    HasCharbonnelClosureNullityWitnesses
      (charbonnelClosure (literalZeroSetFamily G)) := by
  intro n hn S hS
  exact literalZeroSet_charbonnelClosure_nullityWitness
    hG hsmooth hn hS

/-- After section 5.8, the section 5 reduction has only its WS5 analytic
step and finite locally closed decomposition left as geometric inputs. -/
theorem literalZeroSet_charbonnelClosure_approximationTraceSmallness_of_section5Inputs
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) n) :
    CharbonnelApproximationTraceSmallness
      (charbonnelClosure (literalZeroSetFamily G)) :=
  literalZeroSet_charbonnelClosure_approximationTraceSmallness_of_section5
    hG hsmooth hC hanalytic hdecomp
      (literalZeroSet_charbonnelClosure_hasClosureNullityWitnesses hG hsmooth)

end AbelFormalization
