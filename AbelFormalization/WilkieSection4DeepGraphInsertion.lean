import AbelFormalization.WilkieSection4DeepEnrichedCells
import AbelFormalization.CharbonnelClosureNullityWitnesses

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Delete the graph coordinate from `(x,u,y)`, retaining `(x,y)`. -/
def charbonnelGraphCylinderProjectionLinearMap (n : ℕ) :
    RealEuclidean ((n + 1) + 1) →ₗ[ℝ] RealEuclidean (n + 1) where
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
theorem charbonnelGraphCylinderProjectionLinearMap_apply
    {n : ℕ} (z : RealEuclidean ((n + 1) + 1)) :
    charbonnelGraphCylinderProjectionLinearMap n z =
      realEuclideanAppend
        (realEuclideanTakeLeft (realEuclideanTakeLeft z))
        (realEuclideanTakeRight z) :=
  rfl

/-- Insert a retained graph coordinate immediately before the last
coordinate of a set. -/
def charbonnelGraphCylinderLiftCarrier
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) (T : Set (RealEuclidean (n + 1))) :
    Set (RealEuclidean ((n + 1) + 1)) :=
  charbonnelCylinderCell (charbonnelRestrictedGraph base f) ∩
    charbonnelClosureLiftCylinder T

theorem charbonnelGraphCylinderLiftCarrier_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)} {f : RealEuclidean n → ℝ}
    (hgraph : charbonnelRestrictedGraph base f ∈
      charbonnelClosure S (n + 1))
    {T : Set (RealEuclidean (n + 1))}
    (hT : T ∈ charbonnelClosure S (n + 1)) :
    charbonnelGraphCylinderLiftCarrier base f T ∈
      charbonnelClosure S ((n + 1) + 1) := by
  have hgraphPull :
      charbonnelCylinderCell (charbonnelRestrictedGraph base f) ∈
        charbonnelClosure S ((n + 1) + 1) :=
    charbonnelCylinderCell_mem_charbonnelClosure hC (by omega) hgraph
  have huniv : (Set.univ : Set (RealEuclidean 1)) ∈
      charbonnelClosure S 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ 1)
  have hproduct : realEuclideanSetProduct T
      (Set.univ : Set (RealEuclidean 1)) ∈
        charbonnelClosure S ((n + 1) + 1) :=
    hC.ws3_prod (by omega) (by omega) hT huniv
  have hTPull : charbonnelClosureLiftCylinder T ∈
      charbonnelClosure S ((n + 1) + 1) :=
    hC.ws4_linearEquiv (by omega) hproduct
      (realEuclideanCoordinateReindex
        (charbonnelMoveLastBeforeWitnessesEquiv n 1))
  exact hC.ws1_inter (by omega) hgraphPull hTPull

/-- A boundary function transported across an inserted graph coordinate. -/
def charbonnelGraphBaseLiftFunction
    {n : ℕ} (g : RealEuclidean n → ℝ) :
    RealEuclidean (n + 1) → ℝ :=
  fun z ↦ g (realEuclideanTakeLeft z)

theorem continuousOn_charbonnelGraphBaseLiftFunction
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ}
    (hg : ContinuousOn g base) :
    ContinuousOn (charbonnelGraphBaseLiftFunction g)
      (charbonnelRestrictedGraph base f) := by
  exact hg.comp
    (realEuclideanTakeLeftLinearMap n 1).toContinuousLinearMap.continuous.continuousOn
    (fun _ hz ↦ hz.1)

/-- The graph of a transported boundary is exactly the simultaneous lift of
the inserted graph and the old boundary graph. -/
theorem charbonnelRestrictedGraph_graphBaseLiftFunction
    {n : ℕ} (base : Set (RealEuclidean n))
    (f g : RealEuclidean n → ℝ) :
    charbonnelRestrictedGraph (charbonnelRestrictedGraph base f)
        (charbonnelGraphBaseLiftFunction g) =
      charbonnelGraphCylinderLiftCarrier base f
        (charbonnelRestrictedGraph base g) := by
  ext z
  have hz : z =
      realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanTakeLeft (realEuclideanTakeLeft z))
          (realEuclideanTakeRight (realEuclideanTakeLeft z)))
        (realEuclideanTakeRight z) := by
    simp only [realEuclideanAppend_takeLeft_takeRight]
  rw [hz]
  simp only [charbonnelRestrictedGraph,
    charbonnelGraphCylinderLiftCarrier, charbonnelCylinderCell,
    charbonnelGraphBaseLiftFunction, Set.mem_ofPred_eq, Set.mem_inter_iff,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    mem_charbonnelClosureLiftCylinder_append_iff]
  aesop

theorem charbonnelOpenBand_graphBaseLiftFunction
    {n : ℕ} (base : Set (RealEuclidean n))
    (f g h : RealEuclidean n → ℝ) :
    charbonnelOpenBand (charbonnelRestrictedGraph base f)
        (charbonnelGraphBaseLiftFunction g)
        (charbonnelGraphBaseLiftFunction h) =
      charbonnelGraphCylinderLiftCarrier base f
        (charbonnelOpenBand base g h) := by
  ext z
  have hz : z =
      realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanTakeLeft (realEuclideanTakeLeft z))
          (realEuclideanTakeRight (realEuclideanTakeLeft z)))
        (realEuclideanTakeRight z) := by
    simp only [realEuclideanAppend_takeLeft_takeRight]
  rw [hz]
  simp only [charbonnelOpenBand, charbonnelRestrictedGraph,
    charbonnelGraphCylinderLiftCarrier, charbonnelCylinderCell,
    charbonnelGraphBaseLiftFunction, Set.mem_ofPred_eq, Set.mem_inter_iff,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    mem_charbonnelClosureLiftCylinder_append_iff]
  aesop

theorem charbonnelLowerRayCell_graphBaseLiftFunction
    {n : ℕ} (base : Set (RealEuclidean n))
    (f g : RealEuclidean n → ℝ) :
    charbonnelLowerRayCell (charbonnelRestrictedGraph base f)
        (charbonnelGraphBaseLiftFunction g) =
      charbonnelGraphCylinderLiftCarrier base f
        (charbonnelLowerRayCell base g) := by
  ext z
  have hz : z =
      realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanTakeLeft (realEuclideanTakeLeft z))
          (realEuclideanTakeRight (realEuclideanTakeLeft z)))
        (realEuclideanTakeRight z) := by
    simp only [realEuclideanAppend_takeLeft_takeRight]
  rw [hz]
  simp only [charbonnelLowerRayCell, charbonnelRestrictedGraph,
    charbonnelGraphCylinderLiftCarrier, charbonnelCylinderCell,
    charbonnelGraphBaseLiftFunction, Set.mem_ofPred_eq, Set.mem_inter_iff,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    mem_charbonnelClosureLiftCylinder_append_iff]
  aesop

theorem charbonnelUpperRayCell_graphBaseLiftFunction
    {n : ℕ} (base : Set (RealEuclidean n))
    (f g : RealEuclidean n → ℝ) :
    charbonnelUpperRayCell (charbonnelRestrictedGraph base f)
        (charbonnelGraphBaseLiftFunction g) =
      charbonnelGraphCylinderLiftCarrier base f
        (charbonnelUpperRayCell base g) := by
  ext z
  have hz : z =
      realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanTakeLeft (realEuclideanTakeLeft z))
          (realEuclideanTakeRight (realEuclideanTakeLeft z)))
        (realEuclideanTakeRight z) := by
    simp only [realEuclideanAppend_takeLeft_takeRight]
  rw [hz]
  simp only [charbonnelUpperRayCell, charbonnelRestrictedGraph,
    charbonnelGraphCylinderLiftCarrier, charbonnelCylinderCell,
    charbonnelGraphBaseLiftFunction, Set.mem_ofPred_eq, Set.mem_inter_iff,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    mem_charbonnelClosureLiftCylinder_append_iff]
  aesop

theorem charbonnelCylinderCell_restrictedGraph
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    charbonnelCylinderCell (charbonnelRestrictedGraph base f) =
      charbonnelGraphCylinderLiftCarrier base f
        (charbonnelCylinderCell base) := by
  ext z
  have hz : z =
      realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanTakeLeft (realEuclideanTakeLeft z))
          (realEuclideanTakeRight (realEuclideanTakeLeft z)))
        (realEuclideanTakeRight z) := by
    simp only [realEuclideanAppend_takeLeft_takeRight]
  rw [hz]
  simp only [charbonnelRestrictedGraph,
    charbonnelGraphCylinderLiftCarrier, charbonnelCylinderCell,
    Set.mem_ofPred_eq, Set.mem_inter_iff,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    mem_charbonnelClosureLiftCylinder_append_iff]
  aesop

/-- Inserting a retained graph below another retained boundary preserves the
boundary-graph membership certificate. -/
theorem charbonnelRestrictedGraph_graphBaseLiftFunction_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)} {f g : RealEuclidean n → ℝ}
    (hfgraph : charbonnelRestrictedGraph base f ∈
      charbonnelClosure S (n + 1))
    (hggraph : charbonnelRestrictedGraph base g ∈
      charbonnelClosure S (n + 1)) :
    charbonnelRestrictedGraph (charbonnelRestrictedGraph base f)
        (charbonnelGraphBaseLiftFunction g) ∈
      charbonnelClosure S ((n + 1) + 1) := by
  rw [charbonnelRestrictedGraph_graphBaseLiftFunction]
  exact charbonnelGraphCylinderLiftCarrier_mem_charbonnelClosure
    hC hn hfgraph hggraph

namespace CharbonnelDeepEnrichedCell

/-- Insert a retained graph as the new last coordinate of a deep base. -/
def insertGraph
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    CharbonnelDeepEnrichedCell S (n + 1) :=
  { carrier := charbonnelRestrictedGraph base.carrier f
    shape := .graph hn base.shape f hf hgraph }

@[simp]
theorem insertGraph_carrier
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    (base.insertGraph hn f hf hgraph).carrier =
      charbonnelRestrictedGraph base.carrier f :=
  rfl

@[simp]
theorem insertGraph_toCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    ((base.insertGraph hn f hf hgraph).toCell hC).carrier =
      charbonnelRestrictedGraph base.carrier f := by
  rfl

end CharbonnelDeepEnrichedCell

namespace CharbonnelEnrichedVerticalCell

/-- Insert a retained graph coordinate below one trailing enriched vertical
constructor, transporting every outer boundary function and certificate. -/
def insertGraphBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hfgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (cell : CharbonnelEnrichedVerticalCell S (base.toCell hC)) :
    CharbonnelEnrichedVerticalCell S
      ((base.insertGraph hn f hf hfgraph).toCell hC) := by
  cases cell with
  | graph g hg hggraph =>
      exact .graph (charbonnelGraphBaseLiftFunction g)
        (continuousOn_charbonnelGraphBaseLiftFunction
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hg))
        (by
          simpa only [CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier]
            using
              (charbonnelRestrictedGraph_graphBaseLiftFunction_mem_charbonnelClosure
                hC hn hfgraph
                (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
                  using hggraph)))
  | band g h hg hh hgh hggraph hhgraph =>
      exact .band (charbonnelGraphBaseLiftFunction g)
        (charbonnelGraphBaseLiftFunction h)
        (continuousOn_charbonnelGraphBaseLiftFunction
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hg))
        (continuousOn_charbonnelGraphBaseLiftFunction
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hh))
        (fun z hz ↦ by
          have hz' : z ∈ charbonnelRestrictedGraph base.carrier f := by
            simpa only [CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier]
              using hz
          exact hgh (realEuclideanTakeLeft z)
            (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
              using hz'.1))
        (by
          simpa only [CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier]
            using
              (charbonnelRestrictedGraph_graphBaseLiftFunction_mem_charbonnelClosure
                hC hn hfgraph
                (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
                  using hggraph)))
        (by
          simpa only [CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier]
            using
              (charbonnelRestrictedGraph_graphBaseLiftFunction_mem_charbonnelClosure
                hC hn hfgraph
                (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
                  using hhgraph)))
  | lowerRay g hg hggraph =>
      exact .lowerRay (charbonnelGraphBaseLiftFunction g)
        (continuousOn_charbonnelGraphBaseLiftFunction
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hg))
        (by
          simpa only [CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier]
            using
              (charbonnelRestrictedGraph_graphBaseLiftFunction_mem_charbonnelClosure
                hC hn hfgraph
                (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
                  using hggraph)))
  | upperRay g hg hggraph =>
      exact .upperRay (charbonnelGraphBaseLiftFunction g)
        (continuousOn_charbonnelGraphBaseLiftFunction
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
            using hg))
        (by
          simpa only [CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier]
            using
              (charbonnelRestrictedGraph_graphBaseLiftFunction_mem_charbonnelClosure
                hC hn hfgraph
                (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier]
                  using hggraph)))
  | cylinder =>
      exact .cylinder

@[simp]
theorem insertGraphBase_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hfgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (cell : CharbonnelEnrichedVerticalCell S (base.toCell hC)) :
    (cell.insertGraphBase hC hn base f hf hfgraph).carrier =
      charbonnelGraphCylinderLiftCarrier base.carrier f cell.carrier := by
  cases cell with
  | graph g hg hggraph =>
      simpa only [insertGraphBase, carrier,
        CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier,
        CharbonnelDeepEnrichedCell.insertGraph_carrier,
        CharbonnelDeepEnrichedCell.toCell_carrier] using
        (charbonnelRestrictedGraph_graphBaseLiftFunction base.carrier f g)
  | band g h hg hh hgh hggraph hhgraph =>
      simpa only [insertGraphBase, carrier,
        CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier,
        CharbonnelDeepEnrichedCell.insertGraph_carrier,
        CharbonnelDeepEnrichedCell.toCell_carrier] using
        (charbonnelOpenBand_graphBaseLiftFunction base.carrier f g h)
  | lowerRay g hg hggraph =>
      simpa only [insertGraphBase, carrier,
        CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier,
        CharbonnelDeepEnrichedCell.insertGraph_carrier,
        CharbonnelDeepEnrichedCell.toCell_carrier] using
        (charbonnelLowerRayCell_graphBaseLiftFunction base.carrier f g)
  | upperRay g hg hggraph =>
      simpa only [insertGraphBase, carrier,
        CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier,
        CharbonnelDeepEnrichedCell.insertGraph_carrier,
        CharbonnelDeepEnrichedCell.toCell_carrier] using
        (charbonnelUpperRayCell_graphBaseLiftFunction base.carrier f g)
  | cylinder =>
      simpa only [insertGraphBase, carrier,
        CharbonnelDeepEnrichedCell.insertGraph_toCell_carrier,
        CharbonnelDeepEnrichedCell.insertGraph_carrier,
        CharbonnelDeepEnrichedCell.toCell_carrier] using
        (charbonnelCylinderCell_restrictedGraph base.carrier f)

end CharbonnelEnrichedVerticalCell

end AbelFormalization
