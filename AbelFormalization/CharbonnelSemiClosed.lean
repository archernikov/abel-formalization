import AbelFormalization.CharbonnelDescriptionAlgebra

/-!
# Closed lifts for Charbonnel descriptions

This file formalizes Servi, Lemma 3.3.9: if the positive-arity base family is
a closed weak structure, then every set in its Charbonnel closure is the
projection of a closed set in the same closure.

The proof follows the induction in the source.  At a union node, the two
closed lifts are padded by unused Euclidean coordinates to a common witness
arity.  At an integer-affine intersection, the affine set is replaced by its
cylinder.  At a projection node, the two successive witness blocks are
reassociated into one block.  Base and closure nodes use zero additional
coordinates.

The positive-arity bookkeeping is explicit.  In particular, padding by a
zero-dimensional block reuses the original description; it does not attempt
to create a forbidden arity-zero base description.

Source: Tamara Servi, *On the First Order Theory of Real Exponentiation*,
Lemma 3.3.9, pp. 50--51:

* https://www.oocities.org/tamara_servi/servithesis.pdf
* https://ricerca.sns.it/retrieve/e3aacdfd-ef33-4c98-e053-3705fe0acb7e/Servi_Tamara.pdf
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Semantic witness-block identities -/

/-- Reassociate a closed lift from coordinates `((x,y),z)` to coordinates
`(x,(y,z))`. -/
def charbonnelWitnessReassociation {n q r : ℕ}
    (B : Set (RealEuclidean ((n + q) + r))) :
    Set (RealEuclidean (n + (q + r))) :=
  realEuclideanCoordinateReindex
      (finAddAssocCoordinateEquiv n q r).symm '' B

@[simp]
theorem realEuclideanCoordinateReindex_symm_apply
    {n m : ℕ} (e : Fin m ≃ Fin n) (x : RealEuclidean m) :
    (realEuclideanCoordinateReindex e).symm x =
      realEuclideanCoordinateReindex e.symm x :=
  rfl

@[simp]
theorem realEuclideanCoordinateReindex_finAddAssoc_symm_append
    {n q r : ℕ} (x : RealEuclidean n) (y : RealEuclidean q)
    (z : RealEuclidean r) :
    realEuclideanCoordinateReindex
        (finAddAssocCoordinateEquiv n q r).symm
        (realEuclideanAppend (realEuclideanAppend x y) z) =
      realEuclideanAppend x (realEuclideanAppend y z) := by
  let E := realEuclideanCoordinateReindex
    (finAddAssocCoordinateEquiv n q r)
  have hforward :
      E (realEuclideanAppend x (realEuclideanAppend y z)) =
        realEuclideanAppend (realEuclideanAppend x y) z :=
    realEuclideanCoordinateReindex_finAddAssoc_append x y z
  calc
    realEuclideanCoordinateReindex
        (finAddAssocCoordinateEquiv n q r).symm
        (realEuclideanAppend (realEuclideanAppend x y) z) =
      E.symm (realEuclideanAppend (realEuclideanAppend x y) z) :=
        (realEuclideanCoordinateReindex_symm_apply _ _).symm
    _ = E.symm (E
        (realEuclideanAppend x (realEuclideanAppend y z))) := by
          rw [hforward]
    _ = realEuclideanAppend x (realEuclideanAppend y z) :=
      E.symm_apply_apply _

@[simp]
theorem mem_charbonnelWitnessReassociation_append_iff
    {n q r : ℕ} {B : Set (RealEuclidean ((n + q) + r))}
    (x : RealEuclidean n) (y : RealEuclidean q)
    (z : RealEuclidean r) :
    realEuclideanAppend x (realEuclideanAppend y z) ∈
        charbonnelWitnessReassociation B ↔
      realEuclideanAppend (realEuclideanAppend x y) z ∈ B := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    have hw' : w = realEuclideanAppend (realEuclideanAppend x y) z := by
      apply (realEuclideanCoordinateReindex
        (finAddAssocCoordinateEquiv n q r).symm).injective
      exact hwx.trans
        (realEuclideanCoordinateReindex_finAddAssoc_symm_append x y z).symm
    simpa only [hw'] using hw
  · intro hxyz
    exact ⟨realEuclideanAppend (realEuclideanAppend x y) z, hxyz,
      realEuclideanCoordinateReindex_finAddAssoc_symm_append x y z⟩

/-- Reassociating the two hidden coordinate blocks turns two successive
existential projections into one projection. -/
theorem realEuclideanExistentialProjection_witnessReassociation
    {n q r : ℕ} (B : Set (RealEuclidean ((n + q) + r))) :
    realEuclideanExistentialProjection (n := n) (m := q + r)
        (charbonnelWitnessReassociation B) =
      realEuclideanExistentialProjection (n := n) (m := q)
        (realEuclideanExistentialProjection (n := n + q) (m := r) B) := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨yz, hyz⟩
    let y : RealEuclidean q := realEuclideanTakeLeft yz
    let z : RealEuclidean r := realEuclideanTakeRight yz
    have hyz' : realEuclideanAppend y z = yz :=
      realEuclideanAppend_takeLeft_takeRight yz
    refine ⟨y, z, ?_⟩
    rw [← hyz'] at hyz
    exact (mem_charbonnelWitnessReassociation_append_iff x y z).mp hyz
  · rintro ⟨y, z, hxyz⟩
    refine ⟨realEuclideanAppend y z, ?_⟩
    exact (mem_charbonnelWitnessReassociation_append_iff x y z).mpr hxyz

/-- Projection through a zero-dimensional final block is the identity. -/
@[simp]
theorem realEuclideanExistentialProjection_zero
    {n : ℕ} (A : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection (n := n) (m := 0) A = A := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hx⟩
    simpa only [realEuclideanAppend_zero] using hx
  · intro hx
    exact ⟨0, by simpa only [realEuclideanAppend_zero] using hx⟩

/-- Existential projection distributes over a binary union. -/
theorem realEuclideanExistentialProjection_union
    {n q : ℕ} (A B : Set (RealEuclidean (n + q))) :
    realEuclideanExistentialProjection (A ∪ B) =
      realEuclideanExistentialProjection A ∪
        realEuclideanExistentialProjection B := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    Set.mem_union]
  constructor
  · rintro ⟨y, hyA | hyB⟩
    · exact Or.inl ⟨y, hyA⟩
    · exact Or.inr ⟨y, hyB⟩
  · rintro (⟨y, hyA⟩ | ⟨y, hyB⟩)
    · exact ⟨y, Or.inl hyA⟩
    · exact ⟨y, Or.inr hyB⟩

/-- Projecting away a free final factor recovers the first factor. -/
@[simp]
theorem realEuclideanExistentialProjection_product_univ
    {n q : ℕ} (A : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection (n := n) (m := q)
        (realEuclideanSetProduct A
          (Set.univ : Set (RealEuclidean q))) = A := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    realEuclideanSetProduct, realEuclideanTakeLeft_append,
    Set.mem_univ, and_true]
  constructor
  · rintro ⟨_, hx⟩
    exact hx
  · intro hx
    exact ⟨0, hx⟩

/-- Intersecting a lift with the cylinder over a visible set commutes with
projection. -/
theorem realEuclideanExistentialProjection_inter_product_univ
    {n q : ℕ} (B : Set (RealEuclidean (n + q)))
    (L : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection
        (B ∩ realEuclideanSetProduct L
          (Set.univ : Set (RealEuclidean q))) =
      realEuclideanExistentialProjection B ∩ L := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    Set.mem_inter_iff, realEuclideanSetProduct,
    realEuclideanTakeLeft_append, Set.mem_univ, and_true]
  constructor
  · rintro ⟨z, hzB, hxL⟩
    exact ⟨⟨z, hzB⟩, hxL⟩
  · rintro ⟨⟨z, hzB⟩, hxL⟩
    exact ⟨z, hzB, hxL⟩

/-- Flat products of closed Euclidean sets are closed. -/
theorem isClosed_realEuclideanSetProduct
    {n m : ℕ} {A : Set (RealEuclidean n)}
    {B : Set (RealEuclidean m)} (hA : IsClosed A) (hB : IsClosed B) :
    IsClosed (realEuclideanSetProduct A B) := by
  apply closure_eq_iff_isClosed.mp
  rw [closure_realEuclideanSetProduct, hA.closure_eq, hB.closure_eq]

/-- A coordinate reassociation preserves closedness. -/
theorem isClosed_charbonnelWitnessReassociation
    {n q r : ℕ} {B : Set (RealEuclidean ((n + q) + r))}
    (hB : IsClosed B) :
    IsClosed (charbonnelWitnessReassociation B) := by
  exact (realEuclideanCoordinateReindex
    (finAddAssocCoordinateEquiv n q r).symm).toContinuousLinearEquiv.isClosed_image.mpr hB

/-! ## Padding closed description lifts -/

/-- Add an unused final witness block and then reassociate all witnesses into
one final block. -/
def charbonnelWitnessPad {n q : ℕ}
    (A : Set (RealEuclidean (n + q))) (r : ℕ) :
    Set (RealEuclidean (n + (q + r))) :=
  charbonnelWitnessReassociation
    (realEuclideanSetProduct A
      (Set.univ : Set (RealEuclidean r)))

@[simp]
theorem mem_charbonnelWitnessPad_append_iff
    {n q r : ℕ} {A : Set (RealEuclidean (n + q))}
    (x : RealEuclidean n) (y : RealEuclidean q)
    (z : RealEuclidean r) :
    realEuclideanAppend x (realEuclideanAppend y z) ∈
        charbonnelWitnessPad A r ↔
      realEuclideanAppend x y ∈ A := by
  rw [charbonnelWitnessPad,
    mem_charbonnelWitnessReassociation_append_iff]
  simp [realEuclideanSetProduct]

@[simp]
theorem charbonnelWitnessPad_zero
    {n q : ℕ} (A : Set (RealEuclidean (n + q))) :
    charbonnelWitnessPad A 0 = A := by
  ext v
  let x : RealEuclidean n := realEuclideanTakeLeft v
  let y : RealEuclidean q := realEuclideanTakeRight v
  have hv : realEuclideanAppend x y = v :=
    realEuclideanAppend_takeLeft_takeRight v
  rw [← hv]
  simpa only [realEuclideanAppend_zero] using
    (mem_charbonnelWitnessPad_append_iff
      (A := A) x y (0 : RealEuclidean 0))

/-- Padding by unused coordinates does not change the visible projection. -/
theorem realEuclideanExistentialProjection_witnessPad
    {n q : ℕ} (A : Set (RealEuclidean (n + q))) (r : ℕ) :
    realEuclideanExistentialProjection (n := n) (m := q + r)
        (charbonnelWitnessPad A r) =
      realEuclideanExistentialProjection (n := n) (m := q) A := by
  calc
    realEuclideanExistentialProjection (n := n) (m := q + r)
        (charbonnelWitnessPad A r) =
      realEuclideanExistentialProjection (n := n) (m := q)
        (realEuclideanExistentialProjection (n := n + q) (m := r)
          (realEuclideanSetProduct A
            (Set.univ : Set (RealEuclidean r)))) :=
      realEuclideanExistentialProjection_witnessReassociation _
    _ = realEuclideanExistentialProjection (n := n) (m := q) A := by
      rw [realEuclideanExistentialProjection_product_univ]

/-- Padding a closed set by unused witness coordinates preserves closedness. -/
theorem isClosed_charbonnelWitnessPad
    {n q : ℕ} {A : Set (RealEuclidean (n + q))}
    (hA : IsClosed A) (r : ℕ) :
    IsClosed (charbonnelWitnessPad A r) := by
  exact isClosed_charbonnelWitnessReassociation
    (isClosed_realEuclideanSetProduct hA isClosed_univ)

/-- Description-level unused-coordinate padding.  The zero case is separate
because `CharbonnelDescription` has no arity-zero base constructor. -/
theorem PositiveArityWeakSetStructure.exists_witnessPad_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n q : ℕ} (description : CharbonnelDescription S (n + q))
    (r : ℕ) :
    ∃ padded : CharbonnelDescription S (n + (q + r)),
      padded.carrier = charbonnelWitnessPad description.carrier r := by
  cases r with
  | zero =>
      exact ⟨description, (charbonnelWitnessPad_zero description.carrier).symm⟩
  | succ r =>
      have huniv : (Set.univ : Set (RealEuclidean (r + 1))) ∈ S (r + 1) :=
        hS.ws2_polynomialSign (by omega)
          (polynomialSignConstructible_univ (r + 1))
      let univDescription : CharbonnelDescription S (r + 1) :=
        .base (by omega) Set.univ huniv
      obtain ⟨product, hproductCarrier, _⟩ :=
        hS.exists_product_description hclosed description univDescription
      obtain ⟨padded, hpaddedCarrier, _⟩ :=
        hS.exists_coordinateReindex_description product
          (finAddAssocCoordinateEquiv n q (r + 1)).symm
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

/-- A closed lift can be padded by any number of unused coordinates while
remaining a closed description lift of the same visible set. -/
theorem PositiveArityWeakSetStructure.exists_closed_projection_padding
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n q : ℕ} (description : CharbonnelDescription S (n + q))
    (hdescription : IsClosed description.carrier) (r : ℕ) :
    ∃ padded : CharbonnelDescription S (n + (q + r)),
      IsClosed padded.carrier ∧
        realEuclideanExistentialProjection (n := n) (m := q + r)
            padded.carrier =
          realEuclideanExistentialProjection (n := n) (m := q)
            description.carrier := by
  obtain ⟨padded, hpadded⟩ :=
    hS.exists_witnessPad_description hclosed description r
  refine ⟨padded, ?_, ?_⟩
  · rw [hpadded]
    exact isClosed_charbonnelWitnessPad hdescription r
  · rw [hpadded]
    exact realEuclideanExistentialProjection_witnessPad
      description.carrier r

/-! ## Servi's closed-lift induction -/

/-- Servi's Lemma 3.3.9 at the level of a single description: every carrier
over a closed positive-arity weak structure is the projection of the carrier
of a closed higher-arity description. -/
theorem PositiveArityWeakSetStructure.exists_closed_projection_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n : ℕ} (description : CharbonnelDescription S n) :
    ∃ (q : ℕ) (lift : CharbonnelDescription S (n + q)),
      IsClosed lift.carrier ∧
        description.carrier =
          realEuclideanExistentialProjection (n := n) (m := q)
            lift.carrier := by
  induction description with
  | @base n hn A hA =>
      refine ⟨0, .base hn A hA, hclosed hn hA, ?_⟩
      simp
  | @union n left right ihleft ihright =>
      obtain ⟨q, leftLift, hleftClosed, hleftProjection⟩ := ihleft
      obtain ⟨r, rightLift, hrightClosed, hrightProjection⟩ := ihright
      obtain ⟨leftPadded, hleftPaddedClosed, hleftPaddedProjection⟩ :=
        hS.exists_closed_projection_padding hclosed leftLift hleftClosed r
      have hrightPadding :
          ∃ rightPadded : CharbonnelDescription S (n + (q + r)),
            IsClosed rightPadded.carrier ∧
              realEuclideanExistentialProjection (n := n) (m := q + r)
                  rightPadded.carrier =
                realEuclideanExistentialProjection (n := n) (m := r)
                  rightLift.carrier := by
        have hpadding :=
          hS.exists_closed_projection_padding hclosed rightLift
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
        realEuclideanSetProduct L
          (Set.univ : Set (RealEuclidean q))
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
      obtain ⟨answer, hanswerCarrier, _⟩ :=
        hS.exists_coordinateReindex_description lift
          (finAddAssocCoordinateEquiv n q r).symm
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

/-- Family-level form of Servi's Lemma 3.3.9.  No separate positivity
hypothesis is needed here: membership in `charbonnelClosure S n` already
supplies a description, and every description has positive ambient arity. -/
theorem PositiveArityWeakSetStructure.charbonnelClosure_semiClosed
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    (hclosed : IsClosedPositiveAritySetFamily S)
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) :
    ∃ (q : ℕ) (B : Set (RealEuclidean (n + q))),
      IsClosed B ∧ B ∈ charbonnelClosure S (n + q) ∧
        A = realEuclideanExistentialProjection (n := n) (m := q) B := by
  obtain ⟨description, hdescription⟩ := hA
  obtain ⟨q, lift, hliftClosed, hliftProjection⟩ :=
    hS.exists_closed_projection_description hclosed description
  refine ⟨q, lift.carrier, hliftClosed, ⟨lift, rfl⟩, ?_⟩
  rw [← hdescription]
  exact hliftProjection

end AbelFormalization
