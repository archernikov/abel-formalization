import AbelFormalization.WilkieSection4DeepGraphInsertion
import AbelFormalization.WilkieSection4DeepSimultaneousInduction

/-!
# Inserting a retained graph below arbitrarily many vertical cell layers

The non-open branch of Wilkie's Section 4 induction deletes the first graph
coordinate of a deep cell, applies the lower-dimensional induction, and then
inserts that coordinate back.  The graph need not be the final coordinate:
it may lie below any finite string of graph, band, ray, or cylinder layers.

This file gives the coordinate maps and the recursive cell transport needed
for that operation.  Boundary functions above the inserted graph are pulled
back along the linear coordinate-deletion map.  Their graph certificates are
therefore obtained from linear preimages and intersection with the lifted
base cylinder; no complement operation is used.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite partition precover by deep cells.  This is the local output used
before the successor assembly performs its single global projection-coherence
normalization. -/
structure CharbonnelFinitePartitionedDeepRelativeCellPrecover
    (S : EuclideanSetFamily) {n : ℕ}
    (D A : Set (RealEuclidean n)) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelDeepEnrichedCell S n
  contained : ∀ i, (cell i).carrier ⊆ D
  covers : ∀ z ∈ D, ∃ i, z ∈ (cell i).carrier
  compatible : ∀ i,
    (cell i).carrier ⊆ A ∨ Disjoint (cell i).carrier A
  cells_eq_or_disjoint : ∀ i j,
    (cell i).carrier = (cell j).carrier ∨
      Disjoint (cell i).carrier (cell j).carrier

namespace CharbonnelFinitePartitionedDeepRelativeCellPrecover

/-- Pull a lower-dimensional partition back through a map which is injective
on a common constraint.  This is the set-theoretic core of both buried-graph
and unary-point reinsertion. -/
def pullbackAlongInjectiveConstraint
    {S : EuclideanSetFamily} {d e : ℕ}
    (P : RealEuclidean (d + 1) → RealEuclidean (e + 1))
    (constraint D A : Set (RealEuclidean (d + 1)))
    (source : Set (RealEuclidean (e + 1)))
    (hD : D = constraint ∩ P ⁻¹' source)
    (hAD : A ⊆ D)
    (hinj : Set.InjOn P constraint)
    (lower :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S source (fun _ : Unit ↦ P '' A))
    (cell : lower.Index → CharbonnelDeepEnrichedCell S (d + 1))
    (hcell : ∀ i, (cell i).carrier =
      constraint ∩ P ⁻¹' (lower.cell i).carrier) :
    CharbonnelFinitePartitionedDeepRelativeCellPrecover S D A where
  Index := lower.Index
  indexFinite := lower.indexFinite
  cell := cell
  contained := by
    intro i z hz
    rw [hcell i] at hz
    rw [hD]
    exact ⟨hz.1, lower.contained i hz.2⟩
  covers := by
    intro z hz
    have hz' := hz
    rw [hD] at hz'
    obtain ⟨i, hi⟩ := lower.covers (P z) hz'.2
    refine ⟨i, ?_⟩
    rw [hcell i]
    exact ⟨hz'.1, hi⟩
  compatible := by
    intro i
    rcases lower.compatible i () with hinside | hdisjoint
    · left
      intro z hz
      rw [hcell i] at hz
      obtain ⟨w, hwA, hwP⟩ := hinside hz.2
      have hwD := hAD hwA
      rw [hD] at hwD
      have hzw : z = w := hinj hz.1 hwD.1 hwP.symm
      simpa only [hzw] using hwA
    · right
      rw [Set.disjoint_left]
      intro z hz hzA
      rw [hcell i] at hz
      exact Set.disjoint_left.mp hdisjoint hz.2 ⟨z, hzA, rfl⟩
  cells_eq_or_disjoint := by
    intro i j
    rcases lower.cells_eq_or_disjoint i j with heq | hdisjoint
    · left
      rw [hcell i, hcell j, heq]
    · right
      rw [hcell i, hcell j]
      exact (hdisjoint.preimage P).mono
        Set.inter_subset_right Set.inter_subset_right

end CharbonnelFinitePartitionedDeepRelativeCellPrecover

/-! ## Coordinate deletion and insertion -/

/-- Delete the coordinate immediately after an initial block of length `n`,
leaving a trailing block of length `q` in place. -/
def charbonnelBuriedGraphProjectionLinearMap (n q : ℕ) :
    RealEuclidean ((n + 1) + q) →ₗ[ℝ] RealEuclidean (n + q) where
  toFun z := realEuclideanAppend
    (realEuclideanTakeLeft (realEuclideanTakeLeft z))
    (realEuclideanTakeRight z)
  map_add' := by
    intro x y
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c x
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem charbonnelBuriedGraphProjectionLinearMap_apply
    {n q : ℕ} (z : RealEuclidean ((n + 1) + q)) :
    charbonnelBuriedGraphProjectionLinearMap n q z =
      realEuclideanAppend
        (realEuclideanTakeLeft (realEuclideanTakeLeft z))
        (realEuclideanTakeRight z) :=
  rfl

@[simp]
theorem charbonnelBuriedGraphProjectionLinearMap_append
    {n q : ℕ} (x : RealEuclidean n) (u : RealEuclidean 1)
    (y : RealEuclidean q) :
    charbonnelBuriedGraphProjectionLinearMap n q
        (realEuclideanAppend (realEuclideanAppend x u) y) =
      realEuclideanAppend x y := by
  simp [charbonnelBuriedGraphProjectionLinearMap]

@[simp]
theorem charbonnelBuriedGraphProjectionLinearMap_zero
    {n : ℕ} (z : RealEuclidean (n + 1)) :
    charbonnelBuriedGraphProjectionLinearMap n 0 z =
      realEuclideanTakeLeft (n := n) (m := 1) z := by
  funext i
  simp [charbonnelBuriedGraphProjectionLinearMap,
    realEuclideanAppend, realEuclideanTakeLeft, realEuclideanTakeRight]

/-- Extend a linear map of bases by the identity on one final coordinate. -/
def charbonnelExtendLinearMapLast {a b : ℕ}
    (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b) :
    RealEuclidean (a + 1) →ₗ[ℝ] RealEuclidean (b + 1) where
  toFun z := realEuclideanAppend (P (realEuclideanTakeLeft z))
    (realEuclideanTakeRight z)
  map_add' := by
    intro x y
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [realEuclideanAppend_castAdd]
      rw [show realEuclideanTakeLeft (x + y) =
          realEuclideanTakeLeft x + realEuclideanTakeLeft y by rfl,
        map_add]
      simp
    · simp [realEuclideanAppend, realEuclideanTakeRight]
  map_smul' := by
    intro c x
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [realEuclideanAppend_castAdd]
      rw [show realEuclideanTakeLeft (c • x) =
          c • realEuclideanTakeLeft x by rfl,
        map_smul]
      simp
    · simp [realEuclideanAppend, realEuclideanTakeRight]

@[simp]
theorem charbonnelExtendLinearMapLast_apply
    {a b : ℕ} (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    (z : RealEuclidean (a + 1)) :
    charbonnelExtendLinearMapLast P z =
      realEuclideanAppend (P (realEuclideanTakeLeft z))
        (realEuclideanTakeRight z) :=
  rfl

@[simp]
theorem charbonnelExtendLinearMapLast_append
    {a b : ℕ} (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    (x : RealEuclidean a) (y : RealEuclidean 1) :
    charbonnelExtendLinearMapLast P (realEuclideanAppend x y) =
      realEuclideanAppend (P x) y := by
  simp only [charbonnelExtendLinearMapLast_apply,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append]

/-- Reassociate a visible block, a trailing block, and one final coordinate. -/
theorem charbonnelRealEuclideanAppend_assoc_last
    {n q : ℕ} (x : RealEuclidean n) (y : RealEuclidean q)
    (z : RealEuclidean 1) :
    realEuclideanAppend x (realEuclideanAppend y z) =
      realEuclideanAppend (realEuclideanAppend x y) z := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [realEuclideanAppend_castAdd]
    rw [show Fin.castAdd (q + 1) i =
      Fin.castAdd 1 (Fin.castAdd q i) by apply Fin.ext; rfl]
    simp only [realEuclideanAppend_castAdd]
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun l ↦ ?_) j
    · simp only [realEuclideanAppend_natAdd,
        realEuclideanAppend_castAdd]
      rw [show Fin.natAdd n (Fin.castAdd 1 i) =
        Fin.castAdd 1 (Fin.natAdd n i) by apply Fin.ext; rfl]
      simp only [realEuclideanAppend_castAdd,
        realEuclideanAppend_natAdd]
    · simp only [realEuclideanAppend_natAdd]
      rw [show Fin.natAdd n (Fin.natAdd q l) =
        Fin.natAdd (n + q) l by apply Fin.ext; simp [Fin.natAdd]]
      simp only [realEuclideanAppend_natAdd]

/-- Deleting a buried coordinate commutes with adjoining one further final
coordinate. -/
theorem charbonnelBuriedGraphProjectionLinearMap_succ
    (n q : ℕ) :
    charbonnelBuriedGraphProjectionLinearMap n (q + 1) =
      charbonnelExtendLinearMapLast
        (charbonnelBuriedGraphProjectionLinearMap n q) := by
  apply LinearMap.ext
  intro z
  let xu : RealEuclidean (n + 1) :=
    realEuclideanTakeLeft (n := n + 1) (m := q + 1) z
  let yt : RealEuclidean (q + 1) :=
    realEuclideanTakeRight (n := n + 1) (m := q + 1) z
  let x : RealEuclidean n :=
    realEuclideanTakeLeft (n := n) (m := 1) xu
  let u : RealEuclidean 1 :=
    realEuclideanTakeRight (n := n) (m := 1) xu
  let yv : RealEuclidean q :=
    realEuclideanTakeLeft (n := q) (m := 1) yt
  let t : RealEuclidean 1 :=
    realEuclideanTakeRight (n := q) (m := 1) yt
  have hz : z = realEuclideanAppend xu yt :=
    (realEuclideanAppend_takeLeft_takeRight z).symm
  have hxu : xu = realEuclideanAppend x u :=
    (realEuclideanAppend_takeLeft_takeRight xu).symm
  have hyt : yt = realEuclideanAppend yv t :=
    (realEuclideanAppend_takeLeft_takeRight yt).symm
  calc
    charbonnelBuriedGraphProjectionLinearMap n (q + 1) z =
        charbonnelBuriedGraphProjectionLinearMap n (q + 1)
          (realEuclideanAppend (realEuclideanAppend x u)
            (realEuclideanAppend yv t)) := by rw [hz, hxu, hyt]
    _ = realEuclideanAppend x (realEuclideanAppend yv t) :=
      charbonnelBuriedGraphProjectionLinearMap_append x u
        (realEuclideanAppend yv t)
    _ = realEuclideanAppend (realEuclideanAppend x yv) t :=
      charbonnelRealEuclideanAppend_assoc_last x yv t
    _ = charbonnelExtendLinearMapLast
        (charbonnelBuriedGraphProjectionLinearMap n q)
        (realEuclideanAppend
          (realEuclideanAppend (realEuclideanAppend x u) yv) t) := by
      simp
    _ = charbonnelExtendLinearMapLast
        (charbonnelBuriedGraphProjectionLinearMap n q) z := by
      rw [hz, hxu, hyt,
        charbonnelRealEuclideanAppend_assoc_last
          (realEuclideanAppend x u) yv t]

/-- Insert the value `f x` after the first `n` coordinates of `(x,y)`. -/
def charbonnelBuriedGraphInsertion
    {n q : ℕ} (f : RealEuclidean n → ℝ)
    (z : RealEuclidean (n + q)) :
    RealEuclidean ((n + 1) + q) :=
  realEuclideanAppend
    (realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ ↦ f (realEuclideanTakeLeft z)))
    (realEuclideanTakeRight z)

@[simp]
theorem charbonnelBuriedGraphInsertion_append
    {n q : ℕ} (f : RealEuclidean n → ℝ)
    (x : RealEuclidean n) (y : RealEuclidean q) :
    charbonnelBuriedGraphInsertion f (realEuclideanAppend x y) =
      realEuclideanAppend (realEuclideanAppend x (fun _ ↦ f x)) y := by
  simp [charbonnelBuriedGraphInsertion]

@[simp]
theorem charbonnelBuriedGraphProjection_insertion
    {n q : ℕ} (f : RealEuclidean n → ℝ)
    (z : RealEuclidean (n + q)) :
    charbonnelBuriedGraphProjectionLinearMap n q
        (charbonnelBuriedGraphInsertion f z) = z := by
  let x : RealEuclidean n := realEuclideanTakeLeft z
  let y : RealEuclidean q := realEuclideanTakeRight z
  have hz : z = realEuclideanAppend x y := by
    exact (realEuclideanAppend_takeLeft_takeRight z).symm
  rw [hz]
  simp

/-- The common graph constraint for every cell obtained by inserting the
same buried graph coordinate. -/
def charbonnelBuriedGraphConstraint {n : ℕ} :
    (q : ℕ) → (base : Set (RealEuclidean n)) →
      (f : RealEuclidean n → ℝ) →
      Set (RealEuclidean ((n + 1) + q))
  | 0, base, f => charbonnelRestrictedGraph base f
  | q + 1, base, f =>
      charbonnelCylinderCell (charbonnelBuriedGraphConstraint q base f)

@[simp]
theorem mem_charbonnelBuriedGraphConstraint_append_iff
    {n q : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ}
    (x : RealEuclidean n) (u : RealEuclidean 1)
    (y : RealEuclidean q) :
    realEuclideanAppend (realEuclideanAppend x u) y ∈
        charbonnelBuriedGraphConstraint q base f ↔
      x ∈ base ∧ f x = u 0 := by
  induction q with
  | zero =>
      rw [realEuclideanAppend_zero]
      simp [charbonnelBuriedGraphConstraint,
        charbonnelRestrictedGraph, eq_comm]
  | succ q ih =>
      let y0 : RealEuclidean q := realEuclideanTakeLeft y
      let t : RealEuclidean 1 := realEuclideanTakeRight y
      have hy : y = realEuclideanAppend y0 t :=
        (realEuclideanAppend_takeLeft_takeRight y).symm
      rw [hy, charbonnelRealEuclideanAppend_assoc_last
        (realEuclideanAppend x u) y0 t]
      change realEuclideanTakeLeft
          (realEuclideanAppend
            (realEuclideanAppend (realEuclideanAppend x u) y0) t) ∈
            charbonnelBuriedGraphConstraint q base f ↔
        x ∈ base ∧ f x = u 0
      rw [realEuclideanTakeLeft_append]
      exact ih y0

/-- On the buried graph constraint, insertion after deletion is the identity. -/
theorem charbonnelBuriedGraphInsertion_projection
    {n q : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ}
    {z : RealEuclidean ((n + 1) + q)}
    (hz : z ∈ charbonnelBuriedGraphConstraint q base f) :
    charbonnelBuriedGraphInsertion f
        (charbonnelBuriedGraphProjectionLinearMap n q z) = z := by
  let xu := realEuclideanTakeLeft z
  let x : RealEuclidean n := realEuclideanTakeLeft xu
  let u : RealEuclidean 1 := realEuclideanTakeRight xu
  let y : RealEuclidean q := realEuclideanTakeRight z
  have hzdecomp : z = realEuclideanAppend (realEuclideanAppend x u) y := by
    dsimp only [x, u, y, xu]
    rw [realEuclideanAppend_takeLeft_takeRight
      (realEuclideanTakeLeft z)]
    exact (realEuclideanAppend_takeLeft_takeRight z).symm
  rw [hzdecomp] at hz ⊢
  have hfu : f x = u 0 :=
    (mem_charbonnelBuriedGraphConstraint_append_iff x u y).mp hz |>.2
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · simp
    · fin_cases k
      simpa [charbonnelBuriedGraphInsertion] using hfu
  · simp

/-- Deleting the buried graph coordinate is injective on its graph
constraint. -/
theorem charbonnelBuriedGraphProjection_injectiveOn
    {n q : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ} :
    Set.InjOn (charbonnelBuriedGraphProjectionLinearMap n q)
      (charbonnelBuriedGraphConstraint q base f) := by
  intro z hz w hw hzw
  rw [← charbonnelBuriedGraphInsertion_projection hz,
    ← charbonnelBuriedGraphInsertion_projection hw, hzw]

/-! ## Membership after deleting the buried coordinate -/

@[simp]
theorem realEuclideanCoordinateReindex_moveLastBeforeWitnesses_symm
    {n q : ℕ} (x : RealEuclidean n) (u : RealEuclidean 1)
    (y : RealEuclidean q) :
    (realEuclideanCoordinateReindex
        (charbonnelMoveLastBeforeWitnessesEquiv n q)).symm
        (realEuclideanAppend (realEuclideanAppend x u) y) =
      realEuclideanAppend (realEuclideanAppend x y) u := by
  rw [← realEuclideanCoordinateReindex_moveLastBeforeWitnesses x y u]
  exact (realEuclideanCoordinateReindex
    (charbonnelMoveLastBeforeWitnessesEquiv n q)).symm_apply_apply _

/-- The image of a set under buried-coordinate deletion is a genuine final
coordinate projection after one coordinate permutation. -/
theorem charbonnelBuriedGraphProjection_image_eq
    {n q : ℕ} (A : Set (RealEuclidean ((n + 1) + q))) :
    charbonnelBuriedGraphProjectionLinearMap n q '' A =
      realEuclideanExistentialProjection
        ((realEuclideanCoordinateReindex
          (charbonnelMoveLastBeforeWitnessesEquiv n q)).symm '' A) := by
  ext v
  let E := realEuclideanCoordinateReindex
    (charbonnelMoveLastBeforeWitnessesEquiv n q)
  constructor
  · rintro ⟨z, hzA, rfl⟩
    let xu : RealEuclidean (n + 1) := realEuclideanTakeLeft z
    let x : RealEuclidean n := realEuclideanTakeLeft xu
    let u : RealEuclidean 1 := realEuclideanTakeRight xu
    let y : RealEuclidean q := realEuclideanTakeRight z
    have hz : z = realEuclideanAppend (realEuclideanAppend x u) y := by
      dsimp only [x, u, y, xu]
      rw [realEuclideanAppend_takeLeft_takeRight
        (realEuclideanTakeLeft z)]
      exact (realEuclideanAppend_takeLeft_takeRight z).symm
    refine ⟨u, ?_⟩
    refine ⟨z, hzA, ?_⟩
    rw [hz]
    simp only [charbonnelBuriedGraphProjectionLinearMap_append,
      realEuclideanCoordinateReindex_moveLastBeforeWitnesses_symm]
  · rintro ⟨u, z, hzA, hz⟩
    refine ⟨z, hzA, ?_⟩
    let x : RealEuclidean n := realEuclideanTakeLeft v
    let y : RealEuclidean q := realEuclideanTakeRight v
    have hv : v = realEuclideanAppend x y :=
      (realEuclideanAppend_takeLeft_takeRight v).symm
    have hz' : z = realEuclideanAppend (realEuclideanAppend x u) y := by
      apply E.symm.injective
      rw [show E.symm z = realEuclideanAppend v u by
        simpa only [E] using hz]
      rw [realEuclideanCoordinateReindex_moveLastBeforeWitnesses_symm, hv]
    rw [hz', hv]
    exact charbonnelBuriedGraphProjectionLinearMap_append x u y

/-- Charbonnel membership survives deletion of an arbitrary buried graph
coordinate.  This is just WS4 followed by one Charbonnel projection. -/
theorem charbonnelBuriedGraphProjection_image_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hnq : 0 < n + q)
    {A : Set (RealEuclidean ((n + 1) + q))}
    (hA : A ∈ charbonnelClosure S ((n + 1) + q)) :
    charbonnelBuriedGraphProjectionLinearMap n q '' A ∈
      charbonnelClosure S (n + q) := by
  have hreindexed :
      (realEuclideanCoordinateReindex
        (charbonnelMoveLastBeforeWitnessesEquiv n q)).symm '' A ∈
          charbonnelClosure S ((n + q) + 1) := by
    exact hC.toDescriptionReindexBase.coordinateReindex (by omega) hA
      (charbonnelMoveLastBeforeWitnessesEquiv n q).symm
  rw [charbonnelBuriedGraphProjection_image_eq]
  exact charbonnelClosure_projection hnq hreindexed

/-! ## Pulling one vertical constructor along a linear base map -/

theorem charbonnelRestrictedGraph_comp_linearMap_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    {small : Set (RealEuclidean b)} {large : Set (RealEuclidean a)}
    (hlarge : large ∈ charbonnelClosure S a)
    (hmap : Set.MapsTo P large small)
    {g : RealEuclidean b → ℝ}
    (hggraph : charbonnelRestrictedGraph small g ∈
      charbonnelClosure S (b + 1)) :
    charbonnelRestrictedGraph large (fun z ↦ g (P z)) ∈
      charbonnelClosure S (a + 1) := by
  have hpull : (charbonnelExtendLinearMapLast P) ⁻¹'
        charbonnelRestrictedGraph small g ∈
      charbonnelClosure S (a + 1) :=
    hC.linear_preimage_mem (by omega) (by omega) hggraph
      (charbonnelExtendLinearMapLast P)
  have hcylinder : charbonnelCylinderCell large ∈
      charbonnelClosure S (a + 1) :=
    charbonnelCylinderCell_mem_charbonnelClosure hC ha hlarge
  rw [show charbonnelRestrictedGraph large (fun z ↦ g (P z)) =
      charbonnelCylinderCell large ∩
        (charbonnelExtendLinearMapLast P) ⁻¹'
          charbonnelRestrictedGraph small g by
    ext z
    simp only [charbonnelRestrictedGraph, charbonnelCylinderCell,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      charbonnelExtendLinearMapLast_apply,
      realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
    constructor
    · rintro ⟨hz, heq⟩
      exact ⟨hz, hmap hz, heq⟩
    · rintro ⟨hz, _hPz, heq⟩
      exact ⟨hz, heq⟩]
  exact hC.ws1_inter (by omega) hcylinder hpull

namespace CharbonnelEnrichedVerticalCell

/-- Pull an enriched vertical cell back along a linear map between its
recorded bases. -/
def pullbackLinear
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    (small : CharbonnelDeepEnrichedCell S b)
    (large : CharbonnelDeepEnrichedCell S a)
    (hmap : Set.MapsTo P large.carrier small.carrier)
    (cell : CharbonnelEnrichedVerticalCell S (small.toCell hC)) :
    CharbonnelEnrichedVerticalCell S (large.toCell hC) := by
  cases cell with
  | graph g hg hggraph =>
      exact .graph (fun z ↦ g (P z))
        (hg.comp P.toContinuousLinearMap.continuous.continuousOn hmap)
        (charbonnelRestrictedGraph_comp_linearMap_mem_charbonnelClosure
          hC ha hb P (large.toCell hC).carrier_mem
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using hmap)
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hggraph))
  | band g k hg hk hgk hggraph hkgraph =>
      exact .band (fun z ↦ g (P z)) (fun z ↦ k (P z))
        (hg.comp P.toContinuousLinearMap.continuous.continuousOn hmap)
        (hk.comp P.toContinuousLinearMap.continuous.continuousOn hmap)
        (fun z hz ↦ hgk (P z) (hmap hz))
        (charbonnelRestrictedGraph_comp_linearMap_mem_charbonnelClosure
          hC ha hb P (large.toCell hC).carrier_mem
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using hmap)
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hggraph))
        (charbonnelRestrictedGraph_comp_linearMap_mem_charbonnelClosure
          hC ha hb P (large.toCell hC).carrier_mem
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using hmap)
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hkgraph))
  | lowerRay g hg hggraph =>
      exact .lowerRay (fun z ↦ g (P z))
        (hg.comp P.toContinuousLinearMap.continuous.continuousOn hmap)
        (charbonnelRestrictedGraph_comp_linearMap_mem_charbonnelClosure
          hC ha hb P (large.toCell hC).carrier_mem
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using hmap)
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hggraph))
  | upperRay g hg hggraph =>
      exact .upperRay (fun z ↦ g (P z))
        (hg.comp P.toContinuousLinearMap.continuous.continuousOn hmap)
        (charbonnelRestrictedGraph_comp_linearMap_mem_charbonnelClosure
          hC ha hb P (large.toCell hC).carrier_mem
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using hmap)
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hggraph))
  | cylinder => exact .cylinder

@[simp]
theorem pullbackLinear_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    (small : CharbonnelDeepEnrichedCell S b)
    (large : CharbonnelDeepEnrichedCell S a)
    (hmap : Set.MapsTo P large.carrier small.carrier)
    (cell : CharbonnelEnrichedVerticalCell S (small.toCell hC)) :
    (cell.pullbackLinear hC ha hb P small large hmap).carrier =
      charbonnelCylinderCell large.carrier ∩
        (charbonnelExtendLinearMapLast P) ⁻¹' cell.carrier := by
  cases cell <;>
    ext z <;>
    simp [pullbackLinear, carrier, charbonnelRestrictedGraph,
      charbonnelOpenBand, charbonnelLowerRayCell,
      charbonnelUpperRayCell, charbonnelCylinderCell] <;>
    aesop

end CharbonnelEnrichedVerticalCell

/-! ## Recursive deep-cell insertion -/

namespace CharbonnelDeepEnrichedCell

/-- The retained top vertical constructor of a deep successor cell, with its
recursive projected base as the recorded base. -/
def topVertical
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {d : ℕ} (hd : 0 < d)
    (cell : CharbonnelDeepEnrichedCell S (d + 1)) :
    CharbonnelEnrichedVerticalCell S ((cell.projectedBase hd).toCell hC) := by
  rcases cell with ⟨carrier, shape⟩
  cases shape with
  | unary piece => omega
  | graph hm baseShape f hf hgraph => exact .graph f hf hgraph
  | band hm baseShape f g hf hg hfg hfgraph hggraph =>
      exact .band f g hf hg hfg hfgraph hggraph
  | lowerRay hm baseShape g hg hgraph => exact .lowerRay g hg hgraph
  | upperRay hm baseShape f hf hgraph => exact .upperRay f hf hgraph
  | cylinder hm baseShape => exact .cylinder

@[simp]
theorem topVertical_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {d : ℕ} (hd : 0 < d)
    (cell : CharbonnelDeepEnrichedCell S (d + 1)) :
    (cell.topVertical hC hd).carrier = cell.carrier := by
  rcases cell with ⟨carrier, shape⟩
  cases shape with
  | unary piece => omega
  | graph => rfl
  | band => rfl
  | lowerRay => rfl
  | upperRay => rfl
  | cylinder => rfl

/-- Membership in a deep successor cell implies membership of the visible
prefix in its retained projected base. -/
theorem mem_projectedBase_of_mem
    {S : EuclideanSetFamily}
    {d : ℕ} (hd : 0 < d)
    (cell : CharbonnelDeepEnrichedCell S (d + 1))
    {z : RealEuclidean (d + 1)} (hz : z ∈ cell.carrier) :
    realEuclideanTakeLeft z ∈ (cell.projectedBase hd).carrier := by
  rcases cell with ⟨carrier, shape⟩
  cases shape with
  | unary piece => omega
  | graph => exact hz.1
  | band => exact hz.1
  | lowerRay => exact hz.1
  | upperRay => exact hz.1
  | cylinder => exact hz

/-- Project through the last `q` recursive layers of a deep cell. -/
def projectedBaseN
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n) :
    (q : ℕ) → CharbonnelDeepEnrichedCell S (n + q) →
      CharbonnelDeepEnrichedCell S n
  | 0, cell => cell
  | q + 1, cell =>
      projectedBaseN hn q (cell.projectedBase (by omega))

@[simp]
theorem projectedBaseN_zero
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S n) :
    cell.projectedBaseN hn 0 = cell :=
  rfl

@[simp]
theorem projectedBaseN_succ
    {S : EuclideanSetFamily} {n q : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + (q + 1))) :
    cell.projectedBaseN hn (q + 1) =
      (cell.projectedBase (show 0 < n + q by omega)).projectedBaseN hn q :=
  rfl

/-- Membership descends through all `q` retained projected bases. -/
theorem mem_projectedBaseN_of_mem
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n) :
    ∀ (q : ℕ) (cell : CharbonnelDeepEnrichedCell S (n + q))
      {z : RealEuclidean (n + q)},
      z ∈ cell.carrier →
      realEuclideanTakeLeft z ∈ (cell.projectedBaseN hn q).carrier := by
  intro q
  induction q with
  | zero =>
      intro cell z hz
      have htake : realEuclideanTakeLeft (n := n) (m := 0) z = z := by
        funext i
        rfl
      rw [htake]
      exact hz
  | succ q ih =>
      intro cell z hz
      let hd : 0 < n + q := by omega
      have hzbase := cell.mem_projectedBase_of_mem hd hz
      have hroot := ih (cell.projectedBase hd) hzbase
      have htake : realEuclideanTakeLeft (n := n) (m := q + 1) z =
          realEuclideanTakeLeft (n := n) (m := q)
            (realEuclideanTakeLeft (n := n + q) (m := 1) z) := by
        funext i
        rfl
      rw [htake]
      exact hroot

/-- Inclusion of deep cells descends to their retained projected bases. -/
theorem projectedBase_carrier_mono
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {d : ℕ} (hd : 0 < d)
    (left right : CharbonnelDeepEnrichedCell S (d + 1))
    (hsub : left.carrier ⊆ right.carrier) :
    (left.projectedBase hd).carrier ⊆
      (right.projectedBase hd).carrier := by
  rw [← left.existentialProjection_carrier hC hd,
    ← right.existentialProjection_carrier hC hd]
  rintro x ⟨y, hy⟩
  exact ⟨y, hsub hy⟩

/-- Inclusion descends through any finite number of retained projections. -/
theorem projectedBaseN_carrier_mono
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) :
    ∀ (q : ℕ)
      (left right : CharbonnelDeepEnrichedCell S (n + q)),
      left.carrier ⊆ right.carrier →
      (left.projectedBaseN hn q).carrier ⊆
        (right.projectedBaseN hn q).carrier := by
  intro q
  induction q with
  | zero =>
      intro left right hsub
      exact hsub
  | succ q ih =>
      intro left right hsub
      let hd : 0 < n + q := by omega
      exact ih (left.projectedBase hd) (right.projectedBase hd)
        (projectedBase_carrier_mono hC hd left right hsub)

/-- Internal result package for recursive graph insertion.  The map field is
the fact needed to pull the next vertical constructor back. -/
structure BuriedGraphInsertionResult
    {S : EuclideanSetFamily} {n q : ℕ}
    (source : CharbonnelDeepEnrichedCell S (n + q)) where
  cell : CharbonnelDeepEnrichedCell S ((n + 1) + q)
  projection_maps : Set.MapsTo
    (charbonnelBuriedGraphProjectionLinearMap n q)
    cell.carrier source.carrier

/-- Insert one retained graph coordinate below `q` trailing recursive
constructors. -/
def insertGraphAtDepthResult
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    (q : ℕ) → (source : CharbonnelDeepEnrichedCell S (n + q)) →
      (source.projectedBaseN hn q).carrier ⊆ base.carrier →
      BuriedGraphInsertionResult source
  | 0, source, hroot => by
      have hfsmall : ContinuousOn f source.carrier := hf.mono hroot
      have hsmallGraph : charbonnelRestrictedGraph source.carrier f ∈
          charbonnelClosure S (n + 1) :=
        charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hn hroot (source.toCell hC).carrier_mem hgraph
      let lifted := source.insertGraph hn f hfsmall hsmallGraph
      exact
        { cell := lifted
          projection_maps := by
            intro z hz
            rw [charbonnelBuriedGraphProjectionLinearMap_zero]
            exact hz.1 }
  | q + 1, source, hroot => by
      let small := source.projectedBase (show 0 < n + q by omega)
      let lower := insertGraphAtDepthResult hC hn base f hf hgraph q small hroot
      let P := charbonnelBuriedGraphProjectionLinearMap n q
      let vertical := source.topVertical hC (show 0 < n + q by omega)
      let liftedVertical := vertical.pullbackLinear hC (by omega) (by omega)
        P small lower.cell lower.projection_maps
      let lifted := lower.cell.ofVertical hC
        (show 0 < (n + 1) + q by omega) liftedVertical
      refine
        { cell := lifted
          projection_maps := ?_ }
      intro z hz
      have hz' : z ∈ charbonnelCylinderCell lower.cell.carrier ∩
          (charbonnelExtendLinearMapLast P) ⁻¹' vertical.carrier := by
        simpa only [lifted, CharbonnelDeepEnrichedCell.ofVertical_carrier,
          liftedVertical,
          CharbonnelEnrichedVerticalCell.pullbackLinear_carrier] using hz
      have hsource : charbonnelExtendLinearMapLast P z ∈ source.carrier := by
        rw [← source.topVertical_carrier hC (show 0 < n + q by omega)]
        exact hz'.2
      rw [charbonnelBuriedGraphProjectionLinearMap_succ]
      exact hsource
termination_by q => q

/-- The recursively inserted deep cell. -/
def insertGraphAtDepth
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (q : ℕ) (source : CharbonnelDeepEnrichedCell S (n + q))
    (hroot : (source.projectedBaseN hn q).carrier ⊆ base.carrier) :
    CharbonnelDeepEnrichedCell S ((n + 1) + q) :=
  (insertGraphAtDepthResult hC hn base f hf hgraph q source hroot).cell

theorem insertGraphAtDepth_projection_maps
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (q : ℕ) (source : CharbonnelDeepEnrichedCell S (n + q))
    (hroot : (source.projectedBaseN hn q).carrier ⊆ base.carrier) :
    Set.MapsTo (charbonnelBuriedGraphProjectionLinearMap n q)
      (insertGraphAtDepth hC hn base f hf hgraph q source hroot).carrier
      source.carrier :=
  (insertGraphAtDepthResult hC hn base f hf hgraph q source hroot).projection_maps

/-- Exact carrier formula for arbitrary-depth graph insertion.  Every lifted
cell is the inverse image of its source cell inside the common buried graph
constraint. -/
theorem insertGraphAtDepth_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    ∀ (q : ℕ) (source : CharbonnelDeepEnrichedCell S (n + q))
      (hroot : (source.projectedBaseN hn q).carrier ⊆ base.carrier),
      (insertGraphAtDepth hC hn base f hf hgraph q source hroot).carrier =
        charbonnelBuriedGraphConstraint q base.carrier f ∩
          (charbonnelBuriedGraphProjectionLinearMap n q) ⁻¹'
            source.carrier := by
  intro q
  induction q with
  | zero =>
      intro source hroot
      ext z
      simp only [insertGraphAtDepth, insertGraphAtDepthResult,
        insertGraph_carrier, charbonnelBuriedGraphConstraint,
        Set.mem_inter_iff, Set.mem_preimage,
        charbonnelRestrictedGraph, Set.mem_ofPred_eq,
        charbonnelBuriedGraphProjectionLinearMap_zero]
      constructor
      · rintro ⟨hzSource, hzGraph⟩
        exact ⟨⟨hroot hzSource, hzGraph⟩, hzSource⟩
      · rintro ⟨⟨_base, hzGraph⟩, hzSource⟩
        exact ⟨hzSource, hzGraph⟩
  | succ q ih =>
      intro source hroot
      let hd : 0 < n + q := by omega
      let small := source.projectedBase hd
      let lower := insertGraphAtDepthResult hC hn base f hf hgraph q small hroot
      let P := charbonnelBuriedGraphProjectionLinearMap n q
      let vertical := source.topVertical hC hd
      let liftedVertical := vertical.pullbackLinear hC (by omega) hd
        P small lower.cell lower.projection_maps
      have ihCarrier : lower.cell.carrier =
          charbonnelBuriedGraphConstraint q base.carrier f ∩
            P ⁻¹' small.carrier := by
        exact ih small hroot
      simp only [insertGraphAtDepth, insertGraphAtDepthResult]
      change
        (lower.cell.ofVertical hC (by omega) liftedVertical).carrier =
          charbonnelBuriedGraphConstraint (q + 1) base.carrier f ∩
            (charbonnelBuriedGraphProjectionLinearMap n (q + 1)) ⁻¹'
              source.carrier
      rw [CharbonnelDeepEnrichedCell.ofVertical_carrier,
        CharbonnelEnrichedVerticalCell.pullbackLinear_carrier,
        ihCarrier,
        charbonnelBuriedGraphProjectionLinearMap_succ]
      ext z
      simp only [charbonnelBuriedGraphConstraint,
        charbonnelCylinderCell, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_ofPred_eq, charbonnelExtendLinearMapLast_apply]
      constructor
      · rintro ⟨⟨hzConstraint, _hzSmall⟩, hzSource⟩
        rw [source.topVertical_carrier hC hd] at hzSource
        exact ⟨hzConstraint, hzSource⟩
      · rintro ⟨hzConstraint, hzSource⟩
        have hzSmall : P (realEuclideanTakeLeft z) ∈ small.carrier := by
          simpa only [P, small, charbonnelExtendLinearMapLast_apply,
            realEuclideanTakeLeft_append] using
            (source.mem_projectedBase_of_mem hd hzSource)
        rw [← source.topVertical_carrier hC hd] at hzSource
        exact ⟨⟨hzConstraint, hzSmall⟩, hzSource⟩

/-- Inserting the same buried graph into two source cells preserves
equality-or-disjointness of their carriers. -/
theorem insertGraphAtDepth_eq_or_disjoint
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    {q : ℕ}
    (left right : CharbonnelDeepEnrichedCell S (n + q))
    (hleft : (left.projectedBaseN hn q).carrier ⊆ base.carrier)
    (hright : (right.projectedBaseN hn q).carrier ⊆ base.carrier)
    (hpair : left.carrier = right.carrier ∨
      Disjoint left.carrier right.carrier) :
    (insertGraphAtDepth hC hn base f hf hgraph q left hleft).carrier =
        (insertGraphAtDepth hC hn base f hf hgraph q right hright).carrier ∨
      Disjoint
        (insertGraphAtDepth hC hn base f hf hgraph q left hleft).carrier
        (insertGraphAtDepth hC hn base f hf hgraph q right hright).carrier := by
  rw [insertGraphAtDepth_carrier hC hn base f hf hgraph q left hleft,
    insertGraphAtDepth_carrier hC hn base f hf hgraph q right hright]
  rcases hpair with heq | hdisjoint
  · left
    rw [heq]
  · right
    exact (hdisjoint.preimage
      (charbonnelBuriedGraphProjectionLinearMap n q)).mono
        Set.inter_subset_right Set.inter_subset_right

@[simp]
theorem insertGraphAtDepth_projectedBase_zero
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base source : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (hroot : source.carrier ⊆ base.carrier) :
    ((insertGraphAtDepth hC hn base f hf hgraph 0 source hroot).projectedBase hn).carrier =
      source.carrier := by
  let lifted := insertGraphAtDepth hC hn base f hf hgraph 0 source hroot
  rw [← lifted.existentialProjection_carrier hC hn]
  rw [insertGraphAtDepth_carrier hC hn base f hf hgraph 0 source hroot]
  ext x
  constructor
  · rintro ⟨u, _hconstraint, hsource⟩
    simpa using hsource
  · intro hx
    let u : RealEuclidean 1 := fun _ ↦ f x
    refine ⟨u, ?_, ?_⟩
    · exact ⟨by simpa using hroot hx, by simp [u]⟩
    · simpa [u] using hx

@[simp]
theorem insertGraphAtDepth_projectedBase_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (source : CharbonnelDeepEnrichedCell S (n + (q + 1)))
    (hroot : (source.projectedBaseN hn (q + 1)).carrier ⊆ base.carrier) :
    (insertGraphAtDepth hC hn base f hf hgraph (q + 1) source hroot).projectedBase
        (show 0 < (n + 1) + q by omega) =
      insertGraphAtDepth hC hn base f hf hgraph q
        (source.projectedBase (show 0 < n + q by omega)) hroot := by
  simp only [insertGraphAtDepth, insertGraphAtDepthResult,
    CharbonnelDeepEnrichedCell.ofVertical_projectedBase]

/-! ## The unary-point root -/

/-- Delete the first (unary-point) coordinate, retaining the following `q`
coordinates verbatim.  Unlike the general buried-graph map at `n = 0`, this
has the syntactically convenient codomain `RealEuclidean q`. -/
def charbonnelUnaryPointProjectionLinearMap (q : ℕ) :
    RealEuclidean (1 + q) →ₗ[ℝ] RealEuclidean q :=
  realEuclideanTakeRightLinearMap 1 q

@[simp]
theorem charbonnelUnaryPointProjectionLinearMap_apply
    {q : ℕ} (z : RealEuclidean (1 + q)) :
    charbonnelUnaryPointProjectionLinearMap q z =
      realEuclideanTakeRight z :=
  rfl

@[simp]
theorem charbonnelUnaryPointProjectionLinearMap_apply_coord
    {q : ℕ} (z : RealEuclidean (1 + q)) (i : Fin q) :
    charbonnelUnaryPointProjectionLinearMap q z i =
      realEuclideanTakeRight z i :=
  rfl

@[simp]
theorem charbonnelUnaryPointProjectionLinearMap_append
    {q : ℕ} (u : RealEuclidean 1) (y : RealEuclidean q) :
    charbonnelUnaryPointProjectionLinearMap q
        (realEuclideanAppend u y) = y := by
  change realEuclideanTakeRight (realEuclideanAppend u y) = y
  exact realEuclideanTakeRight_append u y

/-- First-coordinate deletion commutes with adjoining one final coordinate. -/
theorem charbonnelUnaryPointProjectionLinearMap_succ (q : ℕ) :
    charbonnelUnaryPointProjectionLinearMap (q + 1) =
      charbonnelExtendLinearMapLast
        (charbonnelUnaryPointProjectionLinearMap q) := by
  apply LinearMap.ext
  intro z
  let u : RealEuclidean 1 := realEuclideanTakeLeft z
  let yt : RealEuclidean (q + 1) := realEuclideanTakeRight z
  let y : RealEuclidean q := realEuclideanTakeLeft yt
  let t : RealEuclidean 1 := realEuclideanTakeRight yt
  have hz : z = realEuclideanAppend u yt :=
    (realEuclideanAppend_takeLeft_takeRight z).symm
  have hyt : yt = realEuclideanAppend y t :=
    (realEuclideanAppend_takeLeft_takeRight yt).symm
  calc
    charbonnelUnaryPointProjectionLinearMap (q + 1) z =
        charbonnelUnaryPointProjectionLinearMap (q + 1)
          (realEuclideanAppend u (realEuclideanAppend y t)) := by
      rw [hz, hyt]
    _ = realEuclideanAppend y t := by simp
    _ = charbonnelExtendLinearMapLast
        (charbonnelUnaryPointProjectionLinearMap q)
          (realEuclideanAppend (realEuclideanAppend u y) t) := by simp
    _ = charbonnelExtendLinearMapLast
        (charbonnelUnaryPointProjectionLinearMap q) z := by
      rw [hz, hyt, charbonnelRealEuclideanAppend_assoc_last u y t]

/-- The common constraint fixing the first coordinate to the unary point
`a`. -/
def charbonnelBuriedUnaryPointConstraint (q : ℕ) (a : ℝ) :
    Set (RealEuclidean (1 + q)) :=
  {z | realEuclideanTakeLeft z 0 = a}

@[simp]
theorem mem_charbonnelBuriedUnaryPointConstraint_append_iff
    {q : ℕ} (a : ℝ) (u : RealEuclidean 1)
    (y : RealEuclidean q) :
    realEuclideanAppend u y ∈ charbonnelBuriedUnaryPointConstraint q a ↔
      u 0 = a := by
  simp [charbonnelBuriedUnaryPointConstraint]

/-- Reinsert the constant first coordinate. -/
def charbonnelUnaryPointInsertion {q : ℕ} (a : ℝ)
    (y : RealEuclidean q) : RealEuclidean (1 + q) :=
  realEuclideanAppend (fun _ ↦ a) y

@[simp]
theorem charbonnelUnaryPointProjection_insertion
    {q : ℕ} (a : ℝ) (y : RealEuclidean q) :
    charbonnelUnaryPointProjectionLinearMap q
        (charbonnelUnaryPointInsertion a y) = y := by
  simp [charbonnelUnaryPointInsertion]

theorem charbonnelUnaryPointInsertion_projection
    {q : ℕ} {a : ℝ} {z : RealEuclidean (1 + q)}
    (hz : z ∈ charbonnelBuriedUnaryPointConstraint q a) :
    charbonnelUnaryPointInsertion a
        (charbonnelUnaryPointProjectionLinearMap q z) = z := by
  let u : RealEuclidean 1 := realEuclideanTakeLeft z
  let y : RealEuclidean q := realEuclideanTakeRight z
  have hzdecomp : z = realEuclideanAppend u y :=
    (realEuclideanAppend_takeLeft_takeRight z).symm
  have hu : u = fun _ ↦ a := by
    funext i
    rw [Fin.eq_zero i]
    exact hz
  rw [hzdecomp]
  simp [charbonnelUnaryPointInsertion, hu]

theorem charbonnelUnaryPointProjection_injectiveOn
    {q : ℕ} {a : ℝ} :
    Set.InjOn (charbonnelUnaryPointProjectionLinearMap q)
      (charbonnelBuriedUnaryPointConstraint q a) := by
  intro z hz w hw hzw
  rw [← charbonnelUnaryPointInsertion_projection hz,
    ← charbonnelUnaryPointInsertion_projection hw, hzw]

/-- Deleting the first coordinate is a genuine final-coordinate projection
after exchanging the first coordinate with the trailing block. -/
theorem charbonnelUnaryPointProjection_image_eq
    {q : ℕ} (A : Set (RealEuclidean (1 + q))) :
    charbonnelUnaryPointProjectionLinearMap q '' A =
      realEuclideanExistentialProjection
        (realEuclideanCoordinateReindex (@finAddFlip q 1) '' A) := by
  ext v
  constructor
  · rintro ⟨z, hzA, rfl⟩
    let u : RealEuclidean 1 := realEuclideanTakeLeft z
    let y : RealEuclidean q := realEuclideanTakeRight z
    have hz : z = realEuclideanAppend u y :=
      (realEuclideanAppend_takeLeft_takeRight z).symm
    refine ⟨u, ?_⟩
    refine ⟨z, hzA, ?_⟩
    rw [hz]
    simp only [charbonnelUnaryPointProjectionLinearMap_append,
      realEuclideanCoordinateReindex_finAddFlip_append]
  · rintro ⟨u, z, hzA, hz⟩
    refine ⟨z, hzA, ?_⟩
    let u' : RealEuclidean 1 := realEuclideanTakeLeft z
    let y : RealEuclidean q := realEuclideanTakeRight z
    have hzdecomp : z = realEuclideanAppend u' y :=
      (realEuclideanAppend_takeLeft_takeRight z).symm
    have hy : y = v := by
      have h := congrArg
        (realEuclideanTakeLeft (n := q) (m := 1)) hz
      simpa only [hzdecomp,
        realEuclideanCoordinateReindex_finAddFlip_append,
        realEuclideanTakeLeft_append] using h
    rw [hzdecomp, charbonnelUnaryPointProjectionLinearMap_append, hy]

/-- Charbonnel membership survives deletion of a fixed unary-point
coordinate.  The proof swaps that coordinate to the end and applies the
genuine Charbonnel projection constructor. -/
theorem charbonnelUnaryPointProjection_image_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {q : ℕ} (hq : 0 < q)
    {A : Set (RealEuclidean (1 + q))}
    (hA : A ∈ charbonnelClosure S (1 + q)) :
    charbonnelUnaryPointProjectionLinearMap q '' A ∈
      charbonnelClosure S q := by
  have hreindexed :
      realEuclideanCoordinateReindex (@finAddFlip q 1) '' A ∈
        charbonnelClosure S (q + 1) := by
    exact hC.toDescriptionReindexBase.coordinateReindex (by omega) hA
      (@finAddFlip q 1)
  rw [charbonnelUnaryPointProjection_image_eq]
  exact charbonnelClosure_projection hq hreindexed

/-- Polynomial cutting out a constant final coordinate.  This local version
keeps the unary-point transport independent of the later bounded-reduction
module. -/
def charbonnelBuriedPointLastCoordinatePolynomial (n : ℕ) (c : ℝ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.X (Fin.last n) - MvPolynomial.C c

@[simp]
theorem charbonnelBuriedPointLastCoordinatePolynomial_eval
    (n : ℕ) (c : ℝ) (z : RealEuclidean (n + 1)) :
    MvPolynomial.eval z
        (charbonnelBuriedPointLastCoordinatePolynomial n c) =
      realEuclideanTakeRight z 0 - c := by
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  simp only [charbonnelBuriedPointLastCoordinatePolynomial, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [hlast]
  rfl

/-- Constant graphs over a positive-dimensional Charbonnel set. -/
theorem charbonnelRestrictedConstantGraph_mem_charbonnelClosure_for_point
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {base : Set (RealEuclidean n)}
    (hbase : base ∈ charbonnelClosure S n) (c : ℝ) :
    charbonnelRestrictedGraph base (fun _ ↦ c) ∈
      charbonnelClosure S (n + 1) := by
  have hbasePull : realEuclideanTakeLeftLinearMap n 1 ⁻¹' base ∈
      charbonnelClosure S (n + 1) :=
    hC.linear_preimage_mem (by omega) hn hbase
      (realEuclideanTakeLeftLinearMap n 1)
  have hlevel : {z : RealEuclidean (n + 1) |
        MvPolynomial.eval z
          (charbonnelBuriedPointLastCoordinatePolynomial n c) = 0} ∈
      charbonnelClosure S (n + 1) :=
    hC.ws2_polynomialSign (by omega) (.zero _)
  rw [show charbonnelRestrictedGraph base (fun _ ↦ c) =
      realEuclideanTakeLeftLinearMap n 1 ⁻¹' base ∩
        {z : RealEuclidean (n + 1) |
          MvPolynomial.eval z
            (charbonnelBuriedPointLastCoordinatePolynomial n c) = 0} by
    ext z
    simp [charbonnelRestrictedGraph, sub_eq_zero]]
  exact hC.ws1_inter (by omega) hbasePull hlevel

/-- The retained unary point used as the base of point-coordinate insertion. -/
def charbonnelDeepUnaryPoint
    {S : EuclideanSetFamily} (a : ℝ) :
    CharbonnelDeepEnrichedCell S 1 :=
  { carrier := realEuclideanUnaryPiece (.point a)
    shape := .unary (.point a) }

@[simp]
theorem charbonnelDeepUnaryPoint_carrier
    {S : EuclideanSetFamily} (a : ℝ) :
    (charbonnelDeepUnaryPoint (S := S) a).carrier =
      realEuclideanUnaryPiece (.point a) :=
  rfl

/-- A canonical empty unary deep cell, used only when an ill-ordered open
interval already has empty carrier. -/
def charbonnelDeepEmptyUnary
    {S : EuclideanSetFamily} : CharbonnelDeepEnrichedCell S 1 :=
  { carrier := realEuclideanUnaryPiece (.bounded 0 0)
    shape := .unary (.bounded 0 0) }

@[simp]
theorem charbonnelDeepEmptyUnary_carrier
    {S : EuclideanSetFamily} :
    (charbonnelDeepEmptyUnary (S := S)).carrier = ∅ := by
  ext x
  simp [charbonnelDeepEmptyUnary, realEuclideanUnaryPiece,
    realEuclideanUnaryLift, UnaryPiece.carrier]

/-- Insert a constant first coordinate in front of a unary deep cell.  This is
the root case missing from positive-dimensional graph insertion. -/
def insertUnaryPointBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) (source : CharbonnelDeepEnrichedCell S 1) :
    CharbonnelDeepEnrichedCell S 2 := by
  rcases source with ⟨carrier, shape⟩
  cases shape with
  | unary piece =>
      let base := charbonnelDeepUnaryPoint (S := S) a
      have hconst (c : ℝ) : charbonnelRestrictedGraph base.carrier
          (fun _ ↦ c) ∈ charbonnelClosure S 2 :=
        charbonnelRestrictedConstantGraph_mem_charbonnelClosure_for_point
          hC (by omega) (base.toCell hC).carrier_mem c
      cases piece with
      | point b =>
          exact base.ofVertical hC (by omega)
            (.graph (fun _ ↦ b) continuousOn_const (hconst b))
      | bounded b c =>
          by_cases hbc : b < c
          · exact base.ofVertical hC (by omega)
              (.band (fun _ ↦ b) (fun _ ↦ c)
                continuousOn_const continuousOn_const
                (fun _ _ ↦ hbc) (hconst b) (hconst c))
          · exact charbonnelDeepEmptyUnary.ofVertical hC (by omega) .cylinder
      | leftRay b =>
          exact base.ofVertical hC (by omega)
            (.lowerRay (fun _ ↦ b) continuousOn_const (hconst b))
      | rightRay b =>
          exact base.ofVertical hC (by omega)
            (.upperRay (fun _ ↦ b) continuousOn_const (hconst b))
      | whole =>
          exact base.ofVertical hC (by omega) .cylinder
  | graph hn _ _ _ _ => omega
  | band hn _ _ _ _ _ _ _ _ => omega
  | lowerRay hn _ _ _ _ => omega
  | upperRay hn _ _ _ _ => omega
  | cylinder hn _ => omega

/-- Exact carrier formula for the unary root of point-coordinate insertion. -/
theorem insertUnaryPointBase_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) (source : CharbonnelDeepEnrichedCell S 1) :
    (insertUnaryPointBase hC a source).carrier =
      charbonnelBuriedUnaryPointConstraint 1 a ∩
        (charbonnelUnaryPointProjectionLinearMap 1) ⁻¹'
          source.carrier := by
  rcases source with ⟨carrier, shape⟩
  cases shape with
  | unary piece =>
      cases piece with
      | point b =>
          ext z
          simp [insertUnaryPointBase, charbonnelBuriedUnaryPointConstraint,
            CharbonnelDeepEnrichedCell.ofVertical_carrier,
            CharbonnelEnrichedVerticalCell.carrier,
            charbonnelRestrictedGraph, charbonnelCylinderCell,
            charbonnelDeepUnaryPoint, realEuclideanUnaryPiece,
            realEuclideanUnaryLift, UnaryPiece.carrier]
          intro _
          rfl
      | bounded b c =>
          by_cases hbc : b < c
          · ext z
            simp [insertUnaryPointBase, hbc,
              charbonnelBuriedUnaryPointConstraint,
              CharbonnelDeepEnrichedCell.ofVertical_carrier,
              CharbonnelEnrichedVerticalCell.carrier,
              charbonnelOpenBand, charbonnelRestrictedGraph,
              charbonnelCylinderCell, charbonnelDeepUnaryPoint,
              realEuclideanUnaryPiece, realEuclideanUnaryLift,
              UnaryPiece.carrier]
            intro _
            rfl
          ·
            ext z
            simp [insertUnaryPointBase, hbc,
              CharbonnelDeepEnrichedCell.ofVertical_carrier,
              CharbonnelEnrichedVerticalCell.carrier,
              charbonnelBuriedUnaryPointConstraint,
              charbonnelCylinderCell, charbonnelRestrictedGraph,
              charbonnelDeepEmptyUnary, realEuclideanUnaryPiece,
              realEuclideanUnaryLift, UnaryPiece.carrier,
              not_lt.mp hbc]
      | leftRay b =>
          ext z
          simp [insertUnaryPointBase, charbonnelBuriedUnaryPointConstraint,
            CharbonnelDeepEnrichedCell.ofVertical_carrier,
            CharbonnelEnrichedVerticalCell.carrier,
            charbonnelLowerRayCell, charbonnelRestrictedGraph,
            charbonnelCylinderCell, charbonnelDeepUnaryPoint,
            realEuclideanUnaryPiece, realEuclideanUnaryLift,
            UnaryPiece.carrier]
          intro _
          rfl
      | rightRay b =>
          ext z
          simp [insertUnaryPointBase, charbonnelBuriedUnaryPointConstraint,
            CharbonnelDeepEnrichedCell.ofVertical_carrier,
            CharbonnelEnrichedVerticalCell.carrier,
            charbonnelUpperRayCell, charbonnelRestrictedGraph,
            charbonnelCylinderCell, charbonnelDeepUnaryPoint,
            realEuclideanUnaryPiece, realEuclideanUnaryLift,
            UnaryPiece.carrier]
          intro _
          rfl
      | whole =>
          ext z
          simp [insertUnaryPointBase, charbonnelBuriedUnaryPointConstraint,
            CharbonnelDeepEnrichedCell.ofVertical_carrier,
            CharbonnelEnrichedVerticalCell.carrier,
            charbonnelRestrictedGraph, charbonnelCylinderCell,
            charbonnelDeepUnaryPoint, realEuclideanUnaryPiece,
            realEuclideanUnaryLift, UnaryPiece.carrier]
  | graph hn _ _ _ _ => omega
  | band hn _ _ _ _ _ _ _ _ => omega
  | lowerRay hn _ _ _ _ => omega
  | upperRay hn _ _ _ _ => omega
  | cylinder hn _ => omega

/-- Internal result for insertion of a unary point below at least one trailing
coordinate.  The source has `q + 1` coordinates, so the unavailable
zero-dimensional deep-cell case never occurs. -/
structure BuriedUnaryPointInsertionResult
    {S : EuclideanSetFamily} {q : ℕ}
    (source : CharbonnelDeepEnrichedCell S (q + 1)) where
  cell : CharbonnelDeepEnrichedCell S ((1 + q) + 1)
  projection_maps : Set.MapsTo
    (charbonnelUnaryPointProjectionLinearMap (q + 1))
    cell.carrier source.carrier

/-- Insert the constant first coordinate `a` below `q + 1` trailing recursive
constructors. -/
def insertUnaryPointAtDepthResult
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) :
    (q : ℕ) → (source : CharbonnelDeepEnrichedCell S (q + 1)) →
      BuriedUnaryPointInsertionResult source
  | 0, source => by
      refine
        { cell := insertUnaryPointBase hC a source
          projection_maps := ?_ }
      intro z hz
      rw [insertUnaryPointBase_carrier hC a source] at hz
      exact hz.2
  | q + 1, source => by
      let hd : 0 < q + 1 := by omega
      let small := source.projectedBase hd
      let lower := insertUnaryPointAtDepthResult hC a q small
      let P := charbonnelUnaryPointProjectionLinearMap (q + 1)
      let vertical := source.topVertical hC hd
      let liftedVertical := vertical.pullbackLinear hC (by omega) hd
        P small lower.cell lower.projection_maps
      let lifted := lower.cell.ofVertical hC (by omega) liftedVertical
      refine
        { cell := lifted
          projection_maps := ?_ }
      intro z hz
      have hz' : z ∈ charbonnelCylinderCell lower.cell.carrier ∩
          (charbonnelExtendLinearMapLast P) ⁻¹' vertical.carrier := by
        simpa only [lifted,
          CharbonnelDeepEnrichedCell.ofVertical_carrier,
          liftedVertical,
          CharbonnelEnrichedVerticalCell.pullbackLinear_carrier] using hz
      have hsource : charbonnelExtendLinearMapLast P z ∈ source.carrier := by
        rw [← source.topVertical_carrier hC hd]
        exact hz'.2
      rw [charbonnelUnaryPointProjectionLinearMap_succ]
      exact hsource
termination_by q => q

/-- The deep cell obtained by inserting a unary point below `q + 1` trailing
layers. -/
def insertUnaryPointAtDepth
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) (q : ℕ)
    (source : CharbonnelDeepEnrichedCell S (q + 1)) :
    CharbonnelDeepEnrichedCell S ((1 + q) + 1) :=
  (insertUnaryPointAtDepthResult hC a q source).cell

theorem insertUnaryPointAtDepth_projection_maps
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) (q : ℕ)
    (source : CharbonnelDeepEnrichedCell S (q + 1)) :
    Set.MapsTo (charbonnelUnaryPointProjectionLinearMap (q + 1))
      (insertUnaryPointAtDepth hC a q source).carrier source.carrier :=
  (insertUnaryPointAtDepthResult hC a q source).projection_maps

/-- Exact carrier formula for unary-point insertion at arbitrary positive
depth. -/
theorem insertUnaryPointAtDepth_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) :
    ∀ (q : ℕ) (source : CharbonnelDeepEnrichedCell S (q + 1)),
      (insertUnaryPointAtDepth hC a q source).carrier =
        charbonnelBuriedUnaryPointConstraint (q + 1) a ∩
          (charbonnelUnaryPointProjectionLinearMap (q + 1)) ⁻¹'
            source.carrier := by
  intro q
  induction q with
  | zero =>
      intro source
      simpa [insertUnaryPointAtDepth, insertUnaryPointAtDepthResult] using
        insertUnaryPointBase_carrier hC a source
  | succ q ih =>
      intro source
      let hd : 0 < q + 1 := by omega
      let small := source.projectedBase hd
      let lower := insertUnaryPointAtDepthResult hC a q small
      let P := charbonnelUnaryPointProjectionLinearMap (q + 1)
      let vertical := source.topVertical hC hd
      let liftedVertical := vertical.pullbackLinear hC (by omega) hd
        P small lower.cell lower.projection_maps
      have ihCarrier : lower.cell.carrier =
          charbonnelBuriedUnaryPointConstraint (q + 1) a ∩
            P ⁻¹' small.carrier := by
        exact ih small
      simp only [insertUnaryPointAtDepth, insertUnaryPointAtDepthResult]
      change
        (lower.cell.ofVertical hC (by omega) liftedVertical).carrier =
          charbonnelBuriedUnaryPointConstraint ((q + 1) + 1) a ∩
            (charbonnelUnaryPointProjectionLinearMap ((q + 1) + 1)) ⁻¹'
              source.carrier
      rw [CharbonnelDeepEnrichedCell.ofVertical_carrier,
        CharbonnelEnrichedVerticalCell.pullbackLinear_carrier,
        ihCarrier,
        charbonnelUnaryPointProjectionLinearMap_succ]
      ext z
      simp only [charbonnelBuriedUnaryPointConstraint,
        charbonnelCylinderCell, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_ofPred_eq, charbonnelExtendLinearMapLast_apply]
      constructor
      · rintro ⟨⟨hzConstraint, _hzSmall⟩, hzSource⟩
        rw [source.topVertical_carrier hC hd] at hzSource
        exact ⟨hzConstraint, hzSource⟩
      · rintro ⟨hzConstraint, hzSource⟩
        have hzSmall : P (realEuclideanTakeLeft z) ∈ small.carrier := by
          simpa only [P, small, charbonnelExtendLinearMapLast_apply,
            realEuclideanTakeLeft_append] using
            (source.mem_projectedBase_of_mem hd hzSource)
        rw [← source.topVertical_carrier hC hd] at hzSource
        exact ⟨⟨hzConstraint, hzSmall⟩, hzSource⟩

/-- Unary-point insertion preserves equality-or-disjointness. -/
theorem insertUnaryPointAtDepth_eq_or_disjoint
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) {q : ℕ}
    (left right : CharbonnelDeepEnrichedCell S (q + 1))
    (hpair : left.carrier = right.carrier ∨
      Disjoint left.carrier right.carrier) :
    (insertUnaryPointAtDepth hC a q left).carrier =
        (insertUnaryPointAtDepth hC a q right).carrier ∨
      Disjoint
        (insertUnaryPointAtDepth hC a q left).carrier
        (insertUnaryPointAtDepth hC a q right).carrier := by
  rw [insertUnaryPointAtDepth_carrier hC a q left,
    insertUnaryPointAtDepth_carrier hC a q right]
  rcases hpair with heq | hdisjoint
  · left
    rw [heq]
  · right
    exact (hdisjoint.preimage
      (charbonnelUnaryPointProjectionLinearMap (q + 1))).mono
        Set.inter_subset_right Set.inter_subset_right

/-- Pull a lower-dimensional partition back through insertion of a fixed
unary point.  The result deliberately retains only the local precover data:
the successor assembly performs projection-coherence normalization once,
after all local branches have been flattened. -/
def insertUnaryPointAtDepthPrecover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (a : ℝ) (q : ℕ)
    (source : CharbonnelDeepEnrichedCell S (q + 1))
    {A : Set (RealEuclidean ((1 + q) + 1))}
    (hA : A ⊆ (insertUnaryPointAtDepth hC a q source).carrier)
    (lower :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S source.carrier
          (fun _ : Unit ↦
            charbonnelUnaryPointProjectionLinearMap (q + 1) '' A)) :
    CharbonnelFinitePartitionedDeepRelativeCellPrecover S
      (insertUnaryPointAtDepth hC a q source).carrier A :=
  CharbonnelFinitePartitionedDeepRelativeCellPrecover.pullbackAlongInjectiveConstraint
      (charbonnelUnaryPointProjectionLinearMap (q + 1))
      (charbonnelBuriedUnaryPointConstraint (q + 1) a)
      (insertUnaryPointAtDepth hC a q source).carrier A source.carrier
      (insertUnaryPointAtDepth_carrier hC a q source)
      hA charbonnelUnaryPointProjection_injectiveOn lower
      (fun i ↦ insertUnaryPointAtDepth hC a q (lower.cell i))
      (fun i ↦ insertUnaryPointAtDepth_carrier hC a q (lower.cell i))

/-- Pull a lower-dimensional partition back through a graph which occurs at
the top recursive layer.  This is the zero-trailing-layer half of the graph
transport API; separating it from the successor case keeps all dimensions
definitionally aligned with the positive-dimensional cover structure. -/
def insertGraphAtDepthZeroPrecover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {m : ℕ}
    (base : CharbonnelDeepEnrichedCell S (m + 1))
    (f : RealEuclidean (m + 1) → ℝ)
    (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S ((m + 1) + 1))
    (source : CharbonnelDeepEnrichedCell S (m + 1))
    (hroot : source.carrier ⊆ base.carrier)
    {A : Set (RealEuclidean ((m + 1) + 1))}
    (hA : A ⊆
      (insertGraphAtDepth hC (by omega) base f hf hgraph 0 source
        hroot).carrier)
    (lower :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S source.carrier
          (fun _ : Unit ↦
            charbonnelBuriedGraphProjectionLinearMap (m + 1) 0 '' A)) :
    CharbonnelFinitePartitionedDeepRelativeCellPrecover S
      (insertGraphAtDepth hC (by omega) base f hf hgraph 0 source
        hroot).carrier A := by
  let liftedRoot (i : lower.Index) :
      (lower.cell i).carrier ⊆ base.carrier :=
    (lower.contained i).trans hroot
  let lifted (i : lower.Index) :
      CharbonnelDeepEnrichedCell S ((m + 1) + 1) :=
    insertGraphAtDepth hC (by omega) base f hf hgraph 0
      (lower.cell i) (liftedRoot i)
  exact
    CharbonnelFinitePartitionedDeepRelativeCellPrecover.pullbackAlongInjectiveConstraint
      (charbonnelBuriedGraphProjectionLinearMap (m + 1) 0)
      (charbonnelBuriedGraphConstraint 0 base.carrier f)
      (insertGraphAtDepth hC (by omega) base f hf hgraph 0 source
        hroot).carrier A source.carrier
      (insertGraphAtDepth_carrier hC (by omega) base f hf hgraph 0
        source hroot)
      hA charbonnelBuriedGraphProjection_injectiveOn lower lifted
      (fun i ↦ insertGraphAtDepth_carrier hC (by omega) base f hf hgraph 0
        (lower.cell i) (liftedRoot i))

/-- Pull a lower-dimensional partition back through a buried graph with at
least one trailing recursive layer.  Projected-base monotonicity supplies the
root certificate for every cell in the lower partition. -/
def insertGraphAtPositiveDepthPrecover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ)
    (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (source : CharbonnelDeepEnrichedCell S (n + (q + 1)))
    (hroot : (source.projectedBaseN hn (q + 1)).carrier ⊆ base.carrier)
    {A : Set (RealEuclidean ((n + 1) + (q + 1)))}
    (hA : A ⊆
      (insertGraphAtDepth hC hn base f hf hgraph (q + 1) source
        hroot).carrier)
    (lower :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S source.carrier
          (fun _ : Unit ↦
            charbonnelBuriedGraphProjectionLinearMap n (q + 1) '' A)) :
    CharbonnelFinitePartitionedDeepRelativeCellPrecover S
      (insertGraphAtDepth hC hn base f hf hgraph (q + 1) source
        hroot).carrier A := by
  let liftedRoot (i : lower.Index) :
      ((lower.cell i).projectedBaseN hn (q + 1)).carrier ⊆
        base.carrier :=
    (projectedBaseN_carrier_mono hC hn (q + 1)
      (lower.cell i) source (lower.contained i)).trans hroot
  let lifted (i : lower.Index) :
      CharbonnelDeepEnrichedCell S ((n + 1) + (q + 1)) :=
    insertGraphAtDepth hC hn base f hf hgraph (q + 1)
      (lower.cell i) (liftedRoot i)
  exact
    CharbonnelFinitePartitionedDeepRelativeCellPrecover.pullbackAlongInjectiveConstraint
      (charbonnelBuriedGraphProjectionLinearMap n (q + 1))
      (charbonnelBuriedGraphConstraint (q + 1) base.carrier f)
      (insertGraphAtDepth hC hn base f hf hgraph (q + 1) source
        hroot).carrier A source.carrier
      (insertGraphAtDepth_carrier hC hn base f hf hgraph (q + 1)
        source hroot)
      hA charbonnelBuriedGraphProjection_injectiveOn lower lifted
      (fun i ↦ insertGraphAtDepth_carrier hC hn base f hf hgraph (q + 1)
        (lower.cell i) (liftedRoot i))

end CharbonnelDeepEnrichedCell

end AbelFormalization
