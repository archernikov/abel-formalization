import AbelFormalization.CharbonnelOrderedSelectorCells
import AbelFormalization.MaxwellExtendedSlopeClusterMembership

/-!
# Family membership for ordered-selector cells

This file discharges the family-membership hypotheses left explicit in
`CharbonnelOrderedSelectorCells`.  If the base and the restricted graphs of
the scalar selectors belong to a Charbonnel closure carrying WS1--WS4, then
so do the two outer rays, every consecutive open band, and every graph.

The ray argument does not use complements.  In coordinates `(x,y,t)`, pull
the selector graph back along `(x,y,t) ↦ (x,t)`, intersect it with the
polynomial inequality `y < t` or `t < y`, and project away `t`.  Bands are
intersections of two such rays.  The zero-selector cylinder is the WS3
product of the base with the WS2 set `univ`.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## One hidden graph value -/

/-- From witness coordinates `(x,y,t)`, retain `(x,t)`.  Here `y` is the
visible scalar coordinate and `t` is the hidden value constrained to lie on
the selector graph. -/
def charbonnelSelectorWitnessGraphLinearMap (n : ℕ) :
    RealEuclidean ((n + 1) + 1) →ₗ[ℝ] RealEuclidean (n + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft (n := n) (m := 1)
      (realEuclideanTakeLeft (n := n + 1) (m := 1) w))
    (realEuclideanTakeRight (n := n + 1) (m := 1) w)
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem charbonnelSelectorWitnessGraphLinearMap_apply_append
    {n : ℕ} (z : RealEuclidean (n + 1)) (t : RealEuclidean 1) :
    charbonnelSelectorWitnessGraphLinearMap n
        (realEuclideanAppend z t) =
      realEuclideanAppend (realEuclideanTakeLeft z) t := by
  change realEuclideanAppend
      (realEuclideanTakeLeft
        (realEuclideanTakeLeft (realEuclideanAppend z t)))
      (realEuclideanTakeRight (realEuclideanAppend z t)) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeRight_append]

/-- The visible scalar coordinate `y` in witness coordinates `(x,y,t)`. -/
def charbonnelSelectorVisibleValueIndex (n : ℕ) :
    Fin ((n + 1) + 1) :=
  Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1))

/-- The hidden selector value `t` in witness coordinates `(x,y,t)`. -/
def charbonnelSelectorWitnessValueIndex (n : ℕ) :
    Fin ((n + 1) + 1) :=
  Fin.natAdd (n + 1) (0 : Fin 1)

/-- The polynomial-sign constraint `y < t`. -/
def charbonnelSelectorLowerRayConstraint (n : ℕ) :
    Set (RealEuclidean ((n + 1) + 1)) :=
  {w | 0 < MvPolynomial.eval w
    (MvPolynomial.X (charbonnelSelectorWitnessValueIndex n) -
      MvPolynomial.X (charbonnelSelectorVisibleValueIndex n))}

/-- The polynomial-sign constraint `t < y`. -/
def charbonnelSelectorUpperRayConstraint (n : ℕ) :
    Set (RealEuclidean ((n + 1) + 1)) :=
  {w | 0 < MvPolynomial.eval w
    (MvPolynomial.X (charbonnelSelectorVisibleValueIndex n) -
      MvPolynomial.X (charbonnelSelectorWitnessValueIndex n))}

theorem polynomialSignConstructible_charbonnelSelectorLowerRayConstraint
    (n : ℕ) :
    PolynomialSignConstructible ((n + 1) + 1)
      (charbonnelSelectorLowerRayConstraint n) :=
  .pos (MvPolynomial.X (charbonnelSelectorWitnessValueIndex n) -
    MvPolynomial.X (charbonnelSelectorVisibleValueIndex n))

theorem polynomialSignConstructible_charbonnelSelectorUpperRayConstraint
    (n : ℕ) :
    PolynomialSignConstructible ((n + 1) + 1)
      (charbonnelSelectorUpperRayConstraint n) :=
  .pos (MvPolynomial.X (charbonnelSelectorVisibleValueIndex n) -
    MvPolynomial.X (charbonnelSelectorWitnessValueIndex n))

@[simp]
theorem realEuclideanAppend_append_mem_charbonnelSelectorLowerRayConstraint_iff
    {n : ℕ} (x : RealEuclidean n) (y t : RealEuclidean 1) :
    realEuclideanAppend (realEuclideanAppend x y) t ∈
        charbonnelSelectorLowerRayConstraint n ↔
      y 0 < t 0 := by
  simp [charbonnelSelectorLowerRayConstraint,
    charbonnelSelectorWitnessValueIndex,
    charbonnelSelectorVisibleValueIndex, map_sub,
    MvPolynomial.eval_X, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd]

@[simp]
theorem realEuclideanAppend_append_mem_charbonnelSelectorUpperRayConstraint_iff
    {n : ℕ} (x : RealEuclidean n) (y t : RealEuclidean 1) :
    realEuclideanAppend (realEuclideanAppend x y) t ∈
        charbonnelSelectorUpperRayConstraint n ↔
      t 0 < y 0 := by
  simp [charbonnelSelectorUpperRayConstraint,
    charbonnelSelectorWitnessValueIndex,
    charbonnelSelectorVisibleValueIndex, map_sub,
    MvPolynomial.eval_X, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd]

/-- Incidence whose hidden coordinate is a graph value above the displayed
coordinate. -/
def charbonnelSelectorLowerRayIncidence {n : ℕ}
    (graph : Set (RealEuclidean (n + 1))) :
    Set (RealEuclidean ((n + 1) + 1)) :=
  charbonnelSelectorWitnessGraphLinearMap n ⁻¹' graph ∩
    charbonnelSelectorLowerRayConstraint n

/-- Incidence whose hidden coordinate is a graph value below the displayed
coordinate. -/
def charbonnelSelectorUpperRayIncidence {n : ℕ}
    (graph : Set (RealEuclidean (n + 1))) :
    Set (RealEuclidean ((n + 1) + 1)) :=
  charbonnelSelectorWitnessGraphLinearMap n ⁻¹' graph ∩
    charbonnelSelectorUpperRayConstraint n

@[simp]
theorem realEuclideanAppend_append_mem_charbonnelSelectorLowerRayIncidence_iff
    {n : ℕ} (graph : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) (y t : RealEuclidean 1) :
    realEuclideanAppend (realEuclideanAppend x y) t ∈
        charbonnelSelectorLowerRayIncidence graph ↔
      realEuclideanAppend x t ∈ graph ∧ y 0 < t 0 := by
  simp [charbonnelSelectorLowerRayIncidence]

@[simp]
theorem realEuclideanAppend_append_mem_charbonnelSelectorUpperRayIncidence_iff
    {n : ℕ} (graph : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) (y t : RealEuclidean 1) :
    realEuclideanAppend (realEuclideanAppend x y) t ∈
        charbonnelSelectorUpperRayIncidence graph ↔
      realEuclideanAppend x t ∈ graph ∧ t 0 < y 0 := by
  simp [charbonnelSelectorUpperRayIncidence]

/-! ## Projection identities and membership -/

theorem realEuclideanExistentialProjection_charbonnelSelectorLowerRayIncidence
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    realEuclideanExistentialProjection
        (charbonnelSelectorLowerRayIncidence
          (charbonnelRestrictedGraph base f)) =
      charbonnelLowerRayCell base f := by
  ext z
  let x : RealEuclidean n := realEuclideanTakeLeft z
  let y : RealEuclidean 1 := realEuclideanTakeRight z
  have hz : realEuclideanAppend x y = z :=
    realEuclideanAppend_takeLeft_takeRight z
  rw [← hz]
  change (∃ t : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x y) t ∈
        charbonnelSelectorLowerRayIncidence
          (charbonnelRestrictedGraph base f)) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨htGraph, hyt⟩ :=
      (realEuclideanAppend_append_mem_charbonnelSelectorLowerRayIncidence_iff
        (charbonnelRestrictedGraph base f) x y t).mp ht
    have htGraph' : x ∈ base ∧ t 0 = f x := by
      simpa [charbonnelRestrictedGraph] using htGraph
    have hyf : y 0 < f x := by
      simpa only [htGraph'.2] using hyt
    simpa [charbonnelLowerRayCell] using And.intro htGraph'.1 hyf
  · intro hzLower
    have hzLower' : x ∈ base ∧ y 0 < f x := by
      simpa [charbonnelLowerRayCell] using hzLower
    let t : RealEuclidean 1 := fun _ ↦ f x
    refine ⟨t,
      (realEuclideanAppend_append_mem_charbonnelSelectorLowerRayIncidence_iff
        (charbonnelRestrictedGraph base f) x y t).2 ?_⟩
    constructor
    · simpa [charbonnelRestrictedGraph, t] using hzLower'.1
    · simpa [t] using hzLower'.2

theorem realEuclideanExistentialProjection_charbonnelSelectorUpperRayIncidence
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    realEuclideanExistentialProjection
        (charbonnelSelectorUpperRayIncidence
          (charbonnelRestrictedGraph base f)) =
      charbonnelUpperRayCell base f := by
  ext z
  let x : RealEuclidean n := realEuclideanTakeLeft z
  let y : RealEuclidean 1 := realEuclideanTakeRight z
  have hz : realEuclideanAppend x y = z :=
    realEuclideanAppend_takeLeft_takeRight z
  rw [← hz]
  change (∃ t : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x y) t ∈
        charbonnelSelectorUpperRayIncidence
          (charbonnelRestrictedGraph base f)) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨htGraph, hty⟩ :=
      (realEuclideanAppend_append_mem_charbonnelSelectorUpperRayIncidence_iff
        (charbonnelRestrictedGraph base f) x y t).mp ht
    have htGraph' : x ∈ base ∧ t 0 = f x := by
      simpa [charbonnelRestrictedGraph] using htGraph
    have hfy : f x < y 0 := by
      simpa only [htGraph'.2] using hty
    simpa [charbonnelUpperRayCell] using And.intro htGraph'.1 hfy
  · intro hzUpper
    have hzUpper' : x ∈ base ∧ f x < y 0 := by
      simpa [charbonnelUpperRayCell] using hzUpper
    let t : RealEuclidean 1 := fun _ ↦ f x
    refine ⟨t,
      (realEuclideanAppend_append_mem_charbonnelSelectorUpperRayIncidence_iff
        (charbonnelRestrictedGraph base f) x y t).2 ?_⟩
    constructor
    · simpa [charbonnelRestrictedGraph, t] using hzUpper'.1
    · simpa [t] using hzUpper'.2

/-- A family-member restricted graph yields its lower open ray without any
use of complement closure. -/
theorem charbonnelLowerRayCell_mem_charbonnelClosure_of_graph_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ}
    (hgraph : charbonnelRestrictedGraph base f ∈
      charbonnelClosure S (n + 1)) :
    charbonnelLowerRayCell base f ∈ charbonnelClosure S (n + 1) := by
  have hpull :
      charbonnelSelectorWitnessGraphLinearMap n ⁻¹'
          charbonnelRestrictedGraph base f ∈
        charbonnelClosure S ((n + 1) + 1) :=
    hC.linear_preimage_mem (by omega) (by omega) hgraph
      (charbonnelSelectorWitnessGraphLinearMap n)
  have hsign : charbonnelSelectorLowerRayConstraint n ∈
      charbonnelClosure S ((n + 1) + 1) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_charbonnelSelectorLowerRayConstraint n)
  have hincidence :
      charbonnelSelectorLowerRayIncidence
          (charbonnelRestrictedGraph base f) ∈
        charbonnelClosure S ((n + 1) + 1) :=
    hC.ws1_inter (by omega) hpull hsign
  rw [← realEuclideanExistentialProjection_charbonnelSelectorLowerRayIncidence
    base f]
  exact charbonnelClosure_projection (by omega) hincidence

/-- A family-member restricted graph yields its upper open ray without any
use of complement closure. -/
theorem charbonnelUpperRayCell_mem_charbonnelClosure_of_graph_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ}
    (hgraph : charbonnelRestrictedGraph base f ∈
      charbonnelClosure S (n + 1)) :
    charbonnelUpperRayCell base f ∈ charbonnelClosure S (n + 1) := by
  have hpull :
      charbonnelSelectorWitnessGraphLinearMap n ⁻¹'
          charbonnelRestrictedGraph base f ∈
        charbonnelClosure S ((n + 1) + 1) :=
    hC.linear_preimage_mem (by omega) (by omega) hgraph
      (charbonnelSelectorWitnessGraphLinearMap n)
  have hsign : charbonnelSelectorUpperRayConstraint n ∈
      charbonnelClosure S ((n + 1) + 1) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_charbonnelSelectorUpperRayConstraint n)
  have hincidence :
      charbonnelSelectorUpperRayIncidence
          (charbonnelRestrictedGraph base f) ∈
        charbonnelClosure S ((n + 1) + 1) :=
    hC.ws1_inter (by omega) hpull hsign
  rw [← realEuclideanExistentialProjection_charbonnelSelectorUpperRayIncidence
    base f]
  exact charbonnelClosure_projection (by omega) hincidence

/-- Consecutive selector graphs yield the open band between them. -/
theorem charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ}
    (hf : charbonnelRestrictedGraph base f ∈
      charbonnelClosure S (n + 1))
    (hg : charbonnelRestrictedGraph base g ∈
      charbonnelClosure S (n + 1)) :
    charbonnelOpenBand base f g ∈ charbonnelClosure S (n + 1) := by
  have hupper :=
    charbonnelUpperRayCell_mem_charbonnelClosure_of_graph_mem hC hf
  have hlower :=
    charbonnelLowerRayCell_mem_charbonnelClosure_of_graph_mem hC hg
  rw [show charbonnelOpenBand base f g =
      charbonnelUpperRayCell base f ∩ charbonnelLowerRayCell base g by
    ext z
    simp [charbonnelOpenBand, charbonnelUpperRayCell,
      charbonnelLowerRayCell, and_assoc, and_left_comm, and_comm]]
  exact hC.ws1_inter (by omega) hupper hlower

/-- The empty-selector cylinder is the WS3 product of the base with the WS2
universal unary set. -/
theorem charbonnelCylinderCell_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {base : Set (RealEuclidean n)}
    (hbase : base ∈ charbonnelClosure S n) :
    charbonnelCylinderCell base ∈ charbonnelClosure S (n + 1) := by
  have huniv : (Set.univ : Set (RealEuclidean 1)) ∈
      charbonnelClosure S 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ 1)
  have hproduct : realEuclideanSetProduct base
      (Set.univ : Set (RealEuclidean 1)) ∈
        charbonnelClosure S (n + 1) :=
    hC.ws3_prod hn (by omega) hbase huniv
  simpa [charbonnelCylinderCell, realEuclideanSetProduct] using hproduct

/-! ## Discharging the ordered-selector API hypotheses -/

/-- Every positive-cardinality region of an ordered selector family belongs
to the Charbonnel closure as soon as each restricted selector graph does.
Continuity, ordering, and fibre cardinality play no role in this algebraic
membership statement. -/
theorem charbonnelOrderedSelectorRegionCarrier_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ)
    (hgraph : ∀ i, charbonnelRestrictedGraph base (f i) ∈
      charbonnelClosure S (n + 1))
    (hr : 0 < r) (region : CharbonnelOrderedSelectorRegion r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ∈
      charbonnelClosure S (n + 1) := by
  cases region with
  | lower =>
      exact charbonnelLowerRayCell_mem_charbonnelClosure_of_graph_mem hC
        (hgraph (charbonnelFirstSelectorIndex hr))
  | graph i =>
      exact hgraph i
  | band i =>
      exact charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem hC
        (hgraph (charbonnelBandLeftIndex i))
        (hgraph (charbonnelBandRightIndex i))
  | upper =>
      exact charbonnelUpperRayCell_mem_charbonnelClosure_of_graph_mem hC
        (hgraph (charbonnelLastSelectorIndex hr))

/-- The two membership obligations of
`charbonnelFiniteSelectorRelativeCellCover`, derived together from base and
selector-graph membership. -/
theorem charbonnelFiniteSelectorRelativeCellCover_membership
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n r : ℕ} (hn : 0 < n) {base : Set (RealEuclidean n)}
    (hbase : base ∈ charbonnelClosure S n)
    (f : Fin r → RealEuclidean n → ℝ)
    (hgraph : ∀ i, charbonnelRestrictedGraph base (f i) ∈
      charbonnelClosure S (n + 1)) :
    (r = 0 → charbonnelCylinderCell base ∈
      charbonnelClosure S (n + 1)) ∧
    (∀ (hr : 0 < r) region,
      charbonnelOrderedSelectorRegionCarrier base f hr region ∈
        charbonnelClosure S (n + 1)) := by
  exact ⟨fun _ ↦ charbonnelCylinderCell_mem_charbonnelClosure hC hn hbase,
    fun hr region ↦
      charbonnelOrderedSelectorRegionCarrier_mem_charbonnelClosure
        hC f hgraph hr region⟩

/-- Membership-complete form of
`charbonnelFiniteSelectorRelativeCellCover`: its callers supply the base and
selector graphs, rather than separate cylinder/ray/band membership proofs. -/
noncomputable def charbonnelFiniteSelectorRelativeCellCover_of_graph_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n r : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbaseShape : CharbonnelCellShape n base)
    (hbaseMem : base ∈ charbonnelClosure S n)
    (f : Fin r → RealEuclidean n → ℝ)
    (hcontinuous : ∀ i, ContinuousOn (f i) base)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    {A : Set (RealEuclidean (n + 1))}
    (hfiber : ∀ z, realEuclideanTakeLeft z ∈ base →
      (z ∈ A ↔ ∃ i, realEuclideanTakeRight z 0 =
        f i (realEuclideanTakeLeft z)))
    (hgraph : ∀ i, charbonnelRestrictedGraph base (f i) ∈
      charbonnelClosure S (n + 1)) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell base) A := by
  have hmem := charbonnelFiniteSelectorRelativeCellCover_membership
    hC hn hbaseMem f hgraph
  exact charbonnelFiniteSelectorRelativeCellCover hn hbaseShape f
    hcontinuous hordered hfiber hmem.1 hmem.2

/-- Global cylinder-cover form in which base-cell membership and selector
graph membership automatically discharge `hzeroMem` and `hpositiveMem` in
`finiteSelectorCylinderCover`. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.finiteSelectorCylinderCover_of_graph_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {B : Set (RealEuclidean n)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) B)
    {A : Set (RealEuclidean (n + 1))}
    (r : Fin baseCover.count → ℕ)
    (f : ∀ i, Fin (r i) → RealEuclidean n → ℝ)
    (hcontinuous : ∀ i j,
      ContinuousOn (f i j) (baseCover.cell i).carrier)
    (hordered : ∀ i x, x ∈ (baseCover.cell i).carrier →
      StrictMono (fun j ↦ f i j x))
    (hfiber : ∀ i z, realEuclideanTakeLeft z ∈
        (baseCover.cell i).carrier →
      (z ∈ A ↔ ∃ j, realEuclideanTakeRight z 0 =
        f i j (realEuclideanTakeLeft z)))
    (hgraph : ∀ i j,
      charbonnelRestrictedGraph (baseCover.cell i).carrier (f i j) ∈
        charbonnelClosure S (n + 1)) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  apply baseCover.finiteSelectorCylinderCover hn r f
    hcontinuous hordered hfiber
  · intro i _hzero
    exact charbonnelCylinderCell_mem_charbonnelClosure hC hn
      (baseCover.cell i).carrier_mem
  · intro i hri region
    exact charbonnelOrderedSelectorRegionCarrier_mem_charbonnelClosure
      hC (f i) (hgraph i) hri region

end AbelFormalization
