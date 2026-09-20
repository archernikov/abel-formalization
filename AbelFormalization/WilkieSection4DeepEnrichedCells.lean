import AbelFormalization.WilkieSection4EnrichedCells

/-!
# Recursively enriched cells for Wilkie's projection induction

`CharbonnelEnrichedSuccessorCell` retains the base and boundary graphs of one
successor cell, but its base is an ordinary `CharbonnelCell`.  Repeated
projection needs the same retained data at every lower positive dimension.
This file records that recursive object and proves that it forgets both to an
ordinary cell and, at every successor stage, to the existing one-step enriched
cell used by the selector and projection modules.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The recursive shape of a cell with all projected bases and all boundary
graph membership certificates retained.  The carrier is an index, so every
constructor records its exact carrier without an equality field. -/
inductive CharbonnelDeepEnrichedCellShape (S : EuclideanSetFamily) :
    (n : ℕ) → Set (RealEuclidean n) → Type 1
  | unary (piece : UnaryPiece) :
      CharbonnelDeepEnrichedCellShape S 1
        (realEuclideanUnaryPiece piece)
  | graph {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n)
      (baseShape : CharbonnelDeepEnrichedCellShape S n base)
      (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base)
      (hgraph : charbonnelRestrictedGraph base f ∈
        charbonnelClosure S (n + 1)) :
      CharbonnelDeepEnrichedCellShape S (n + 1)
        (charbonnelRestrictedGraph base f)
  | band {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n)
      (baseShape : CharbonnelDeepEnrichedCellShape S n base)
      (f g : RealEuclidean n → ℝ)
      (hf : ContinuousOn f base) (hg : ContinuousOn g base)
      (hfg : ∀ x ∈ base, f x < g x)
      (hfgraph : charbonnelRestrictedGraph base f ∈
        charbonnelClosure S (n + 1))
      (hggraph : charbonnelRestrictedGraph base g ∈
        charbonnelClosure S (n + 1)) :
      CharbonnelDeepEnrichedCellShape S (n + 1)
        (charbonnelOpenBand base f g)
  | lowerRay {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n)
      (baseShape : CharbonnelDeepEnrichedCellShape S n base)
      (g : RealEuclidean n → ℝ) (hg : ContinuousOn g base)
      (hgraph : charbonnelRestrictedGraph base g ∈
        charbonnelClosure S (n + 1)) :
      CharbonnelDeepEnrichedCellShape S (n + 1)
        (charbonnelLowerRayCell base g)
  | upperRay {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n)
      (baseShape : CharbonnelDeepEnrichedCellShape S n base)
      (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base)
      (hgraph : charbonnelRestrictedGraph base f ∈
        charbonnelClosure S (n + 1)) :
      CharbonnelDeepEnrichedCellShape S (n + 1)
        (charbonnelUpperRayCell base f)
  | cylinder {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n)
      (baseShape : CharbonnelDeepEnrichedCellShape S n base) :
      CharbonnelDeepEnrichedCellShape S (n + 1)
        (charbonnelCylinderCell base)

/-- A recursively enriched cell, packaged with its carrier. -/
structure CharbonnelDeepEnrichedCell
    (S : EuclideanSetFamily) (n : ℕ) where
  carrier : Set (RealEuclidean n)
  shape : CharbonnelDeepEnrichedCellShape S n carrier

namespace CharbonnelDeepEnrichedCellShape

/-- The two indexed certificates needed to package an ordinary cell with a
prescribed carrier.  Keeping the carrier in the type avoids losing it while
recursing through the projected bases. -/
structure CellCertificate
    (C : EuclideanSetFamily) {n : ℕ}
    (carrier : Set (RealEuclidean n)) where
  shape : CharbonnelCellShape n carrier
  carrier_mem : carrier ∈ C n

/-- Forget all retained source data and obtain the ordinary recursive cell.
Membership of bands and rays is rebuilt from their retained boundary graphs. -/
def toCellCertificate
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S)) :
    {n : ℕ} → {carrier : Set (RealEuclidean n)} →
      CharbonnelDeepEnrichedCellShape S n carrier →
        CellCertificate (charbonnelClosure S) carrier
  | 1, _, .unary piece =>
      { shape := (charbonnelUnaryCell hC piece).shape
        carrier_mem := (charbonnelUnaryCell hC piece).carrier_mem }
  | _ + 1, _, .graph hn baseShape f hf hgraph =>
      { shape := .graph hn (baseShape.toCellCertificate hC).shape f hf
        carrier_mem := hgraph }
  | _ + 1, _, .band hn baseShape f g hf hg hfg hfgraph hggraph =>
      { shape := .band hn (baseShape.toCellCertificate hC).shape f g hf hg hfg
        carrier_mem :=
          charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem
            hC hfgraph hggraph }
  | _ + 1, _, .lowerRay hn baseShape g hg hgraph =>
      { shape := .lowerRay hn (baseShape.toCellCertificate hC).shape g hg
        carrier_mem :=
          charbonnelLowerRayCell_mem_charbonnelClosure_of_graph_mem
            hC hgraph }
  | _ + 1, _, .upperRay hn baseShape f hf hgraph =>
      { shape := .upperRay hn (baseShape.toCellCertificate hC).shape f hf
        carrier_mem :=
          charbonnelUpperRayCell_mem_charbonnelClosure_of_graph_mem
            hC hgraph }
  | _ + 1, _, .cylinder hn baseShape =>
      { shape := .cylinder hn (baseShape.toCellCertificate hC).shape
        carrier_mem :=
          charbonnelCylinderCell_mem_charbonnelClosure
            hC hn (baseShape.toCellCertificate hC).carrier_mem }

/-- Forget all retained source data and obtain the ordinary recursive cell.
The carrier field is definitionally the indexed carrier of the deep shape. -/
def toCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} {carrier : Set (RealEuclidean n)}
    (shape : CharbonnelDeepEnrichedCellShape S n carrier) :
    CharbonnelCell (charbonnelClosure S) n :=
  { carrier := carrier
    shape := (shape.toCellCertificate hC).shape
    carrier_mem := (shape.toCellCertificate hC).carrier_mem }

@[simp]
theorem toCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} {carrier : Set (RealEuclidean n)}
    (shape : CharbonnelDeepEnrichedCellShape S n carrier) :
    (shape.toCell hC).carrier = carrier := by
  rfl

/-- At a successor dimension, forgetting only the deeper base information
gives the existing one-step enriched successor cell. -/
def toEnrichedSuccessorCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {carrier : Set (RealEuclidean (n + 1))}
    (shape : CharbonnelDeepEnrichedCellShape S (n + 1) carrier) :
    CharbonnelEnrichedSuccessorCell S n := by
  cases shape with
  | unary piece => omega
  | graph hm baseShape f hf hgraph =>
      exact ⟨baseShape.toCell hC, .graph f hf hgraph⟩
  | band hm baseShape f g hf hg hfg hfgraph hggraph =>
      exact ⟨baseShape.toCell hC,
        .band f g hf hg hfg hfgraph hggraph⟩
  | lowerRay hm baseShape g hg hgraph =>
      exact ⟨baseShape.toCell hC, .lowerRay g hg hgraph⟩
  | upperRay hm baseShape f hf hgraph =>
      exact ⟨baseShape.toCell hC, .upperRay f hf hgraph⟩
  | cylinder hm baseShape =>
      exact ⟨baseShape.toCell hC, .cylinder⟩

@[simp]
theorem toEnrichedSuccessorCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {carrier : Set (RealEuclidean (n + 1))}
    (shape : CharbonnelDeepEnrichedCellShape S (n + 1) carrier) :
    (shape.toEnrichedSuccessorCell hC hn).carrier = carrier := by
  cases shape with
  | unary piece => omega
  | graph => rfl
  | band => rfl
  | lowerRay => rfl
  | upperRay => rfl
  | cylinder => rfl

@[simp]
theorem toEnrichedSuccessorCell_toCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {carrier : Set (RealEuclidean (n + 1))}
    (shape : CharbonnelDeepEnrichedCellShape S (n + 1) carrier) :
    (shape.toEnrichedSuccessorCell hC hn).toCell hC hn =
      shape.toCell hC := by
  cases shape with
  | unary piece => omega
  | graph => rfl
  | band => rfl
  | lowerRay => rfl
  | upperRay => rfl
  | cylinder => rfl

/-- The recursively enriched projected base retained by a positive-dimensional
successor shape. -/
def projectedBase
    {S : EuclideanSetFamily}
    {n : ℕ} (hn : 0 < n)
    {carrier : Set (RealEuclidean (n + 1))}
    (shape : CharbonnelDeepEnrichedCellShape S (n + 1) carrier) :
    CharbonnelDeepEnrichedCell S n := by
  cases shape with
  | unary piece => omega
  | graph _ baseShape _ _ _ => exact ⟨_, baseShape⟩
  | band _ baseShape _ _ _ _ _ _ _ => exact ⟨_, baseShape⟩
  | lowerRay _ baseShape _ _ _ => exact ⟨_, baseShape⟩
  | upperRay _ baseShape _ _ _ => exact ⟨_, baseShape⟩
  | cylinder _ baseShape => exact ⟨_, baseShape⟩

@[simp]
theorem toEnrichedSuccessorCell_base_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {carrier : Set (RealEuclidean (n + 1))}
    (shape : CharbonnelDeepEnrichedCellShape S (n + 1) carrier) :
    (shape.toEnrichedSuccessorCell hC hn).base.carrier =
      (shape.projectedBase hn).carrier := by
  cases shape with
  | unary piece => omega
  | graph => rfl
  | band => rfl
  | lowerRay => rfl
  | upperRay => rfl
  | cylinder => rfl

/-- The existential projection of a deep successor cell is exactly its
retained deep base. -/
theorem existentialProjection_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {carrier : Set (RealEuclidean (n + 1))}
    (shape : CharbonnelDeepEnrichedCellShape S (n + 1) carrier) :
    realEuclideanExistentialProjection carrier =
      (shape.projectedBase hn).carrier := by
  let top := shape.toEnrichedSuccessorCell hC hn
  calc
    realEuclideanExistentialProjection carrier =
        realEuclideanExistentialProjection top.carrier := by
          rw [toEnrichedSuccessorCell_carrier hC hn shape]
    _ = top.base.carrier := top.existentialProjection_carrier
    _ = (shape.projectedBase hn).carrier :=
      toEnrichedSuccessorCell_base_carrier hC hn shape

end CharbonnelDeepEnrichedCellShape

namespace CharbonnelDeepEnrichedCell

/-- Forget a recursively enriched cell to the ordinary cell API. -/
def toCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (cell : CharbonnelDeepEnrichedCell S n) :
    CharbonnelCell (charbonnelClosure S) n :=
  cell.shape.toCell hC

@[simp]
theorem toCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (cell : CharbonnelDeepEnrichedCell S n) :
    (cell.toCell hC).carrier = cell.carrier :=
  cell.shape.toCell_carrier hC

/-- Forget only the top recursive layer. -/
def toEnrichedSuccessorCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1)) :
    CharbonnelEnrichedSuccessorCell S n :=
  cell.shape.toEnrichedSuccessorCell hC hn

@[simp]
theorem toEnrichedSuccessorCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1)) :
    (cell.toEnrichedSuccessorCell hC hn).carrier = cell.carrier :=
  cell.shape.toEnrichedSuccessorCell_carrier hC hn

/-- The recursively enriched base of a positive-dimensional successor cell. -/
def projectedBase
    {S : EuclideanSetFamily}
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1)) :
    CharbonnelDeepEnrichedCell S n :=
  cell.shape.projectedBase hn

@[simp]
theorem toEnrichedSuccessorCell_base_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1)) :
    (cell.toEnrichedSuccessorCell hC hn).base.carrier =
      (cell.projectedBase hn).carrier :=
  cell.shape.toEnrichedSuccessorCell_base_carrier hC hn

theorem existentialProjection_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1)) :
    realEuclideanExistentialProjection cell.carrier =
      (cell.projectedBase hn).carrier :=
  cell.shape.existentialProjection_carrier hC hn

/-- The retained projected base of a bounded deep cell is bounded.  This is
the bounded-domain fact used at every lower-dimensional invocation in
Wilkie's Section 4 induction. -/
theorem projectedBase_isBounded
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (hcell : Bornology.IsBounded cell.carrier) :
    Bornology.IsBounded (cell.projectedBase hn).carrier := by
  refine Bornology.IsBounded.subset
    ((realEuclideanTakeLeftContinuousLinearMap n 1).lipschitzWith.isBounded_image
      hcell) ?_
  intro x hx
  rw [← cell.existentialProjection_carrier hC hn] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨realEuclideanAppend x y, hy, realEuclideanTakeLeft_append x y⟩

/-- Attach an enriched vertical cell to a recursively enriched version of its
base.  The boundary graph certificates already carried by the vertical cell
are exactly the certificates required by the new top layer. -/
def ofVertical
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (vertical : CharbonnelEnrichedVerticalCell S (base.toCell hC)) :
    CharbonnelDeepEnrichedCell S (n + 1) := by
  cases vertical with
  | graph f hf hgraph =>
      exact ⟨charbonnelRestrictedGraph base.carrier f,
        .graph hn base.shape f hf hgraph⟩
  | band f g hf hg hfg hfgraph hggraph =>
      exact ⟨charbonnelOpenBand base.carrier f g,
        .band hn base.shape f g hf hg hfg hfgraph hggraph⟩
  | lowerRay g hg hgraph =>
      exact ⟨charbonnelLowerRayCell base.carrier g,
        .lowerRay hn base.shape g hg hgraph⟩
  | upperRay f hf hgraph =>
      exact ⟨charbonnelUpperRayCell base.carrier f,
        .upperRay hn base.shape f hf hgraph⟩
  | cylinder =>
      exact ⟨charbonnelCylinderCell base.carrier,
        .cylinder hn base.shape⟩

@[simp]
theorem ofVertical_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (vertical : CharbonnelEnrichedVerticalCell S (base.toCell hC)) :
    (base.ofVertical hC hn vertical).carrier = vertical.carrier := by
  cases vertical <;> rfl

@[simp]
theorem ofVertical_projectedBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (vertical : CharbonnelEnrichedVerticalCell S (base.toCell hC)) :
    (base.ofVertical hC hn vertical).projectedBase hn = base := by
  cases base
  cases vertical <;> rfl

end CharbonnelDeepEnrichedCell

end AbelFormalization
