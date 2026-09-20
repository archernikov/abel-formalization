import AbelFormalization.WilkieSection4CommonRefinement
import AbelFormalization.WilkieSection4LociRefinement
import AbelFormalization.CharbonnelOrderedSelectorMembership
import AbelFormalization.CharbonnelCellBoundaryCompatibility

/-!
# Enriched cells for Wilkie's successor common-refinement step

The original `CharbonnelCell` API remembers the recursive shape of a cell,
but deliberately forgets the projected base and the family-membership
certificates of its boundary graphs.  Those data are exactly what Wilkie uses
in the successor step of `(II)`: projected cells are refined first, then the
equality loci of all boundary functions are refined, and finally the distinct
boundary functions are ordered on each resulting base cell.

This file gives that argument a lossless input API.  An enriched successor
cell records its base cell and each restricted boundary graph.  We prove:

* its carrier is an ordinary recursive Charbonnel cell and projects exactly
  onto the recorded base;
* equality loci of two recorded boundary functions, and their closures, are
  members of the Charbonnel closure;
* lower-dimensional `(I)` and `(II)` produce a base cover compatible with all
  projected bases and all boundary-equality closures;
* on every nonempty refined base cell, the finitely many active boundary
  functions have a strictly ordered list of representatives;
* the ordered-selector construction then gives a common refinement of any
  finite family of enriched successor cells.

Thus the remaining gap in the old weak cell API is isolated precisely: an
arbitrary `CharbonnelCell` (or a family of weak compatible covers) has no
recoverable projected base or boundary-graph membership data, so it cannot be
fed to this theorem without first enriching the decomposition at construction
time.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Enriched vertical cells over a recorded base -/

/-- A graph/band/ray/cylinder cell over a fixed recursive base, retaining
membership of every boundary graph in the Charbonnel closure. -/
inductive CharbonnelEnrichedVerticalCell
    (S : EuclideanSetFamily) {n : ℕ}
    (base : CharbonnelCell (charbonnelClosure S) n) where
  | graph (f : RealEuclidean n → ℝ)
      (continuous : ContinuousOn f base.carrier)
      (graph_mem : charbonnelRestrictedGraph base.carrier f ∈
        charbonnelClosure S (n + 1))
  | band (f g : RealEuclidean n → ℝ)
      (f_continuous : ContinuousOn f base.carrier)
      (g_continuous : ContinuousOn g base.carrier)
      (lt : ∀ x ∈ base.carrier, f x < g x)
      (f_graph_mem : charbonnelRestrictedGraph base.carrier f ∈
        charbonnelClosure S (n + 1))
      (g_graph_mem : charbonnelRestrictedGraph base.carrier g ∈
        charbonnelClosure S (n + 1))
  | lowerRay (g : RealEuclidean n → ℝ)
      (continuous : ContinuousOn g base.carrier)
      (graph_mem : charbonnelRestrictedGraph base.carrier g ∈
        charbonnelClosure S (n + 1))
  | upperRay (f : RealEuclidean n → ℝ)
      (continuous : ContinuousOn f base.carrier)
      (graph_mem : charbonnelRestrictedGraph base.carrier f ∈
        charbonnelClosure S (n + 1))
  | cylinder

namespace CharbonnelEnrichedVerticalCell

/-- The carrier represented by an enriched vertical cell. -/
def carrier
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n} :
    CharbonnelEnrichedVerticalCell S base → Set (RealEuclidean (n + 1))
  | .graph f _ _ => charbonnelRestrictedGraph base.carrier f
  | .band f g _ _ _ _ _ => charbonnelOpenBand base.carrier f g
  | .lowerRay g _ _ => charbonnelLowerRayCell base.carrier g
  | .upperRay f _ _ => charbonnelUpperRayCell base.carrier f
  | .cylinder => charbonnelCylinderCell base.carrier

/-- Number of boundary functions retained by a vertical cell. -/
def boundaryCount
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n} :
    CharbonnelEnrichedVerticalCell S base → ℕ
  | .graph .. => 1
  | .band .. => 2
  | .lowerRay .. => 1
  | .upperRay .. => 1
  | .cylinder => 0

/-- The retained boundary functions. -/
def boundary
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base) :
    Fin cell.boundaryCount → RealEuclidean n → ℝ := by
  cases cell with
  | graph f _ _ => exact fun _ ↦ f
  | band f g _ _ _ _ _ =>
      exact fun i ↦ if i.1 = 0 then f else g
  | lowerRay g _ _ => exact fun _ ↦ g
  | upperRay f _ _ => exact fun _ ↦ f
  | cylinder => exact Fin.elim0

theorem boundary_continuous
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    (i : Fin cell.boundaryCount) :
    ContinuousOn (cell.boundary i) base.carrier := by
  cases cell with
  | graph f hf _ => simpa [boundary] using hf
  | band f g hf hg _ _ _ =>
      fin_cases i
      · simpa [boundary] using hf
      · simpa [boundary] using hg
  | lowerRay g hg _ => simpa [boundary] using hg
  | upperRay f hf _ => simpa [boundary] using hf
  | cylinder => exact Fin.elim0 i

theorem boundary_graph_mem
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    (i : Fin cell.boundaryCount) :
    charbonnelRestrictedGraph base.carrier (cell.boundary i) ∈
      charbonnelClosure S (n + 1) := by
  cases cell with
  | graph f _ hf => simpa [boundary] using hf
  | band f g _ _ _ hf hg =>
      fin_cases i
      · simpa [boundary] using hf
      · simpa [boundary] using hg
  | lowerRay g _ hg => simpa [boundary] using hg
  | upperRay f _ hf => simpa [boundary] using hf
  | cylinder => exact Fin.elim0 i

/-- Forget the enrichment and recover the ordinary recursive cell. -/
def toCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base) :
    CharbonnelCell (charbonnelClosure S) (n + 1) := by
  cases cell with
  | graph f hf hmem =>
      exact
        { carrier := charbonnelRestrictedGraph base.carrier f
          shape := .graph hn base.shape f hf
          carrier_mem := hmem }
  | band f g hf hg hfg hfmem hgmem =>
      exact
        { carrier := charbonnelOpenBand base.carrier f g
          shape := .band hn base.shape f g hf hg hfg
          carrier_mem :=
            charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem
              hC hfmem hgmem }
  | lowerRay g hg hmem =>
      exact
        { carrier := charbonnelLowerRayCell base.carrier g
          shape := .lowerRay hn base.shape g hg
          carrier_mem :=
            charbonnelLowerRayCell_mem_charbonnelClosure_of_graph_mem
              hC hmem }
  | upperRay f hf hmem =>
      exact
        { carrier := charbonnelUpperRayCell base.carrier f
          shape := .upperRay hn base.shape f hf
          carrier_mem :=
            charbonnelUpperRayCell_mem_charbonnelClosure_of_graph_mem
              hC hmem }
  | cylinder =>
      exact
        { carrier := charbonnelCylinderCell base.carrier
          shape := .cylinder hn base.shape
          carrier_mem := charbonnelCylinderCell_mem_charbonnelClosure
            hC hn base.carrier_mem }

@[simp]
theorem toCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base) :
    (cell.toCell hC hn).carrier = cell.carrier := by
  cases cell <;> rfl

/-- Every enriched carrier projects exactly to its recorded base. -/
theorem existentialProjection_carrier
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base) :
    realEuclideanExistentialProjection cell.carrier = base.carrier := by
  ext x
  cases cell with
  | graph f hf hmem =>
      constructor
      · rintro ⟨y, hy⟩
        simpa using hy.1
      · intro hx
        exact ⟨fun _ ↦ f x, by
          simp [carrier, charbonnelRestrictedGraph, hx]⟩
  | band f g hf hg hfg hfmem hgmem =>
      constructor
      · rintro ⟨y, hy⟩
        simpa using hy.1
      · intro hx
        let y : RealEuclidean 1 := fun _ ↦ (f x + g x) / 2
        refine ⟨y, ?_⟩
        have hlt := hfg x hx
        simp only [carrier, charbonnelOpenBand, Set.mem_ofPred_eq,
          realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
        exact ⟨hx, by dsimp [y]; linarith, by dsimp [y]; linarith⟩
  | lowerRay g hg hmem =>
      constructor
      · rintro ⟨y, hy⟩
        simpa using hy.1
      · intro hx
        exact ⟨fun _ ↦ g x - 1, by
          simp [carrier, charbonnelLowerRayCell, hx]⟩
  | upperRay f hf hmem =>
      constructor
      · rintro ⟨y, hy⟩
        simpa using hy.1
      · intro hx
        exact ⟨fun _ ↦ f x + 1, by
          simp [carrier, charbonnelUpperRayCell, hx]⟩
  | cylinder =>
      constructor
      · rintro ⟨y, hy⟩
        simpa [carrier, charbonnelCylinderCell] using hy
      · intro hx
        exact ⟨fun _ ↦ 0, by
          simpa [carrier, charbonnelCylinderCell] using hx⟩

end CharbonnelEnrichedVerticalCell

/-- A successor cell with its projected base retained as data. -/
structure CharbonnelEnrichedSuccessorCell
    (S : EuclideanSetFamily) (n : ℕ) where
  base : CharbonnelCell (charbonnelClosure S) n
  vertical : CharbonnelEnrichedVerticalCell S base

namespace CharbonnelEnrichedSuccessorCell

def carrier
    {S : EuclideanSetFamily} {n : ℕ}
    (cell : CharbonnelEnrichedSuccessorCell S n) :
    Set (RealEuclidean (n + 1)) :=
  cell.vertical.carrier

def boundaryCount
    {S : EuclideanSetFamily} {n : ℕ}
    (cell : CharbonnelEnrichedSuccessorCell S n) : ℕ :=
  cell.vertical.boundaryCount

def boundary
    {S : EuclideanSetFamily} {n : ℕ}
    (cell : CharbonnelEnrichedSuccessorCell S n) :
    Fin cell.boundaryCount → RealEuclidean n → ℝ :=
  cell.vertical.boundary

theorem boundary_continuous
    {S : EuclideanSetFamily} {n : ℕ}
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (i : Fin cell.boundaryCount) :
    ContinuousOn (cell.boundary i) cell.base.carrier :=
  cell.vertical.boundary_continuous i

theorem boundary_graph_mem
    {S : EuclideanSetFamily} {n : ℕ}
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (i : Fin cell.boundaryCount) :
    charbonnelRestrictedGraph cell.base.carrier (cell.boundary i) ∈
      charbonnelClosure S (n + 1) :=
  cell.vertical.boundary_graph_mem i

def toCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n) :
    CharbonnelCell (charbonnelClosure S) (n + 1) :=
  cell.vertical.toCell hC hn

@[simp]
theorem toCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n) :
    (cell.toCell hC hn).carrier = cell.carrier :=
  cell.vertical.toCell_carrier hC hn

theorem existentialProjection_carrier
    {S : EuclideanSetFamily} {n : ℕ}
    (cell : CharbonnelEnrichedSuccessorCell S n) :
    realEuclideanExistentialProjection cell.carrier = cell.base.carrier :=
  cell.vertical.existentialProjection_carrier

end CharbonnelEnrichedSuccessorCell

/-! ## Boundary equality loci -/

/-- The equality locus of two boundary functions, on the intersection of
their recorded projected bases. -/
def charbonnelBoundaryEqualityLocus
    {n : ℕ} (base₁ base₂ : Set (RealEuclidean n))
    (f g : RealEuclidean n → ℝ) : Set (RealEuclidean n) :=
  {x | x ∈ base₁ ∧ x ∈ base₂ ∧ f x = g x}

theorem realEuclideanExistentialProjection_inter_restrictedGraphs
    {n : ℕ} (base₁ base₂ : Set (RealEuclidean n))
    (f g : RealEuclidean n → ℝ) :
    realEuclideanExistentialProjection
        (charbonnelRestrictedGraph base₁ f ∩
          charbonnelRestrictedGraph base₂ g) =
      charbonnelBoundaryEqualityLocus base₁ base₂ f g := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (x ∈ base₁ ∧ y 0 = f x) ∧
        (x ∈ base₂ ∧ y 0 = g x) := by
      simpa [charbonnelRestrictedGraph] using hy
    exact ⟨hy'.1.1, hy'.2.1, hy'.1.2.symm.trans hy'.2.2⟩
  · rintro ⟨hx₁, hx₂, hfg⟩
    refine ⟨fun _ ↦ f x, ?_⟩
    simpa [charbonnelRestrictedGraph] using
      (show (x ∈ base₁ ∧ f x = f x) ∧
          (x ∈ base₂ ∧ f x = g x) from
        ⟨⟨hx₁, rfl⟩, ⟨hx₂, hfg⟩⟩)

/-- Equality loci of retained boundary graphs remain in the Charbonnel
closure, using only intersection and existential projection. -/
theorem charbonnelBoundaryEqualityLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base₁ base₂ : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ}
    (hf : charbonnelRestrictedGraph base₁ f ∈
      charbonnelClosure S (n + 1))
    (hg : charbonnelRestrictedGraph base₂ g ∈
      charbonnelClosure S (n + 1)) :
    charbonnelBoundaryEqualityLocus base₁ base₂ f g ∈
      charbonnelClosure S n := by
  rw [← realEuclideanExistentialProjection_inter_restrictedGraphs]
  exact charbonnelClosure_projection hn
    (hC.ws1_inter (by omega) hf hg)

/-- The closed equality targets used by Wilkie also remain in the closure. -/
theorem closure_charbonnelBoundaryEqualityLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base₁ base₂ : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ}
    (hf : charbonnelRestrictedGraph base₁ f ∈
      charbonnelClosure S (n + 1))
    (hg : charbonnelRestrictedGraph base₂ g ∈
      charbonnelClosure S (n + 1)) :
    closure (charbonnelBoundaryEqualityLocus base₁ base₂ f g) ∈
      charbonnelClosure S n :=
  charbonnelClosure_topologicalClosure
    (charbonnelBoundaryEqualityLocus_mem_charbonnelClosure
      hC hn hf hg)

/-! ## Relative closedness and the common equality-compatible base cover -/

/-- Relative closedness of a boundary equality locus, in the exact form used
after passing to its ambient closure. -/
theorem mem_charbonnelBoundaryEqualityLocus_of_mem_bases_of_mem_closure
    {n : ℕ} {base₁ base₂ : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ}
    (hf : ContinuousOn f base₁) (hg : ContinuousOn g base₂)
    {x : RealEuclidean n} (hx₁ : x ∈ base₁) (hx₂ : x ∈ base₂)
    (hx : x ∈ closure
      (charbonnelBoundaryEqualityLocus base₁ base₂ f g)) :
    x ∈ charbonnelBoundaryEqualityLocus base₁ base₂ f g := by
  let B : Set (RealEuclidean n) := base₁ ∩ base₂
  let d : RealEuclidean n → ℝ := fun y ↦ f y - g y
  have hd : ContinuousOn d B :=
    (hf.mono inter_subset_left).sub (hg.mono inter_subset_right)
  obtain ⟨K, hKclosed, hK⟩ :=
    (continuousOn_iff_isClosed.mp hd) ({0} : Set ℝ) isClosed_singleton
  have hlocus : charbonnelBoundaryEqualityLocus base₁ base₂ f g =
      d ⁻¹' ({0} : Set ℝ) ∩ B := by
    ext y
    simp [charbonnelBoundaryEqualityLocus, B, d, sub_eq_zero,
      and_left_comm, and_assoc]
    aesop
  have hsubsetK :
      charbonnelBoundaryEqualityLocus base₁ base₂ f g ⊆ K := by
    rw [hlocus, hK]
    exact inter_subset_left
  have hxK : x ∈ K := closure_minimal hsubsetK hKclosed hx
  have hxd : x ∈ d ⁻¹' ({0} : Set ℝ) ∩ B := by
    rw [hK]
    exact ⟨hxK, hx₁, hx₂⟩
  rw [hlocus]
  exact hxd

/-- Restrict a retained graph to a smaller family-member base. -/
theorem charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {large small : Set (RealEuclidean n)} (hsmall : small ⊆ large)
    (hsmallMem : small ∈ charbonnelClosure S n)
    {f : RealEuclidean n → ℝ}
    (hgraph : charbonnelRestrictedGraph large f ∈
      charbonnelClosure S (n + 1)) :
    charbonnelRestrictedGraph small f ∈
      charbonnelClosure S (n + 1) := by
  have hpull : realEuclideanTakeLeftLinearMap n 1 ⁻¹' small ∈
      charbonnelClosure S (n + 1) :=
    hC.linear_preimage_mem (by omega) hn hsmallMem
      (realEuclideanTakeLeftLinearMap n 1)
  have heq : charbonnelRestrictedGraph small f =
      charbonnelRestrictedGraph large f ∩
        realEuclideanTakeLeftLinearMap n 1 ⁻¹' small := by
    ext z
    simp only [charbonnelRestrictedGraph, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_preimage,
      realEuclideanTakeLeftLinearMap_apply]
    constructor
    · rintro ⟨hz, hvalue⟩
      exact ⟨⟨hsmall hz, hvalue⟩, hz⟩
    · rintro ⟨⟨_, hvalue⟩, hz⟩
      exact ⟨hz, hvalue⟩
  rw [heq]
  exact hC.ws1_inter (by omega) hgraph hpull

/-- All retained boundaries in a finite family of enriched successor cells. -/
abbrev CharbonnelEnrichedBoundaryIndex
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (input : I → CharbonnelEnrichedSuccessorCell S n) :=
  Σ i : I, Fin (input i).boundaryCount

/-- The closed equality target belonging to a pair of retained boundaries. -/
def charbonnelEnrichedBoundaryEqualityTarget
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (input : I → CharbonnelEnrichedSuccessorCell S n)
    (q r : CharbonnelEnrichedBoundaryIndex input) :
    Set (RealEuclidean n) :=
  closure (charbonnelBoundaryEqualityLocus
    (input q.1).base.carrier (input r.1).base.carrier
    ((input q.1).boundary q.2) ((input r.1).boundary r.2))

/-- A lower-dimensional cover simultaneously compatible with every recorded
projected base and every closed boundary-equality target. -/
structure CharbonnelEnrichedEqualityBaseRefinement
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (input : I → CharbonnelEnrichedSuccessorCell S n) where
  count : ℕ
  cell : Fin count → CharbonnelCell (charbonnelClosure S) n
  covers : ∀ x : RealEuclidean n, ∃ i, x ∈ (cell i).carrier
  base_compatible : ∀ i j,
    (cell i).carrier ⊆ (input j).base.carrier ∨
      Disjoint (cell i).carrier (input j).base.carrier
  equality_compatible : ∀ i q r,
    (cell i).carrier ⊆
        charbonnelEnrichedBoundaryEqualityTarget input q r ∨
      Disjoint (cell i).carrier
        (charbonnelEnrichedBoundaryEqualityTarget input q r)

/-- Lower-dimensional `(I)` and `(II)` construct the simultaneous projected
base refinement used in Wilkie's successor proof. -/
theorem exists_charbonnelEnrichedEqualityBaseRefinement
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty (CharbonnelEnrichedEqualityBaseRefinement input) := by
  classical
  let Boundary := CharbonnelEnrichedBoundaryIndex input
  let target : Boundary × Boundary → Set (RealEuclidean n) :=
    fun qr ↦ charbonnelEnrichedBoundaryEqualityTarget input qr.1 qr.2
  have htarget : ∀ qr, Nonempty
      (CharbonnelFiniteCompatibleCellCover
        (charbonnelClosure S) (target qr)) := by
    intro qr
    apply hI hn isClosed_closure
    exact closure_charbonnelBoundaryEqualityLocus_mem_charbonnelClosure
      hC hn ((input qr.1.1).boundary_graph_mem qr.1.2)
        ((input qr.2.1).boundary_graph_mem qr.2.2)
  obtain ⟨old⟩ :=
    finiteSimultaneouslyCompatibleCellCover_of_individual_fintype
      (finiteCompatibleCoverCommonRefinement_of_cellFamily hII)
      target htarget
  let oldAndBases : (Fin old.count ⊕ I) →
      CharbonnelCell (charbonnelClosure S) n
    | Sum.inl k => old.cell k
    | Sum.inr j => (input j).base
  obtain ⟨fine⟩ := hII oldAndBases
  refine ⟨
    { count := fine.count
      cell := fine.cell
      covers := fine.covers
      base_compatible := ?_
      equality_compatible := ?_ }⟩
  · intro i j
    simpa [oldAndBases] using fine.compatible i (Sum.inr j)
  · intro i q r
    apply compatible_target_of_compatible_cover_cells
      (cover := old.targetCover (q, r))
    intro k
    change (fine.cell i).carrier ⊆ (old.cell k).carrier ∨
      Disjoint (fine.cell i).carrier (old.cell k).carrier
    simpa [oldAndBases] using fine.compatible i (Sum.inl k)

namespace CharbonnelEnrichedEqualityBaseRefinement

/-- On a refined base cell contained in both recorded bases, two boundary
functions are either identical throughout the cell or nowhere equal there. -/
theorem boundary_eqOn_or_neOn
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count)
    (q r : CharbonnelEnrichedBoundaryIndex input)
    (hq : (refinement.cell k).carrier ⊆ (input q.1).base.carrier)
    (hr : (refinement.cell k).carrier ⊆ (input r.1).base.carrier) :
    Set.EqOn ((input q.1).boundary q.2) ((input r.1).boundary r.2)
        (refinement.cell k).carrier ∨
      (∀ x ∈ (refinement.cell k).carrier,
        (input q.1).boundary q.2 x ≠ (input r.1).boundary r.2 x) := by
  rcases refinement.equality_compatible k q r with hsubset | hdisjoint
  · left
    intro x hx
    exact (mem_charbonnelBoundaryEqualityLocus_of_mem_bases_of_mem_closure
      ((input q.1).boundary_continuous q.2)
      ((input r.1).boundary_continuous r.2)
      (hq hx) (hr hx) (hsubset hx)).2.2
  · right
    intro x hx hEq
    exact Set.disjoint_left.mp hdisjoint hx
      (subset_closure ⟨hq hx, hr hx, hEq⟩)

end CharbonnelEnrichedEqualityBaseRefinement

/-! ## Ordering a finite equality-compatible family -/

/-- A strictly ordered list containing, up to equality on `base`, every
function in a finite family.  `origin` makes each chosen representative an
actual member of the original family, which later supplies its graph
membership certificate. -/
structure CharbonnelBoundaryOrdering
    {X : Type} {J : Type}
    (base : Set X) (f : J → X → ℝ) where
  count : ℕ
  origin : Fin count → J
  strictlyOrdered : ∀ x ∈ base, StrictMono (fun i ↦ f (origin i) x)
  represents : ∀ j, ∃ i, Set.EqOn (f j) (f (origin i)) base

/-- Two nowhere-equal continuous functions whose order is known at one point
have the same strict order throughout a preconnected set. -/
theorem ltOn_of_preconnected_of_continuousOn_of_neOn
    {X : Type} [TopologicalSpace X] {base : Set X}
    (hbase : IsPreconnected base)
    {f g : X → ℝ} (hf : ContinuousOn f base)
    (hg : ContinuousOn g base)
    (hne : ∀ x ∈ base, f x ≠ g x)
    {x₀ : X} (hx₀ : x₀ ∈ base) (hlt : f x₀ < g x₀) :
    ∀ x ∈ base, f x < g x := by
  intro x hx
  have hneq := hne x hx
  rcases lt_or_gt_of_ne hneq with hltx | hgtx
  · exact hltx
  · let d : X → ℝ := fun y ↦ f y - g y
    have hd : ContinuousOn d base := hf.sub hg
    have hintermediate : Set.Icc (d x₀) (d x) ⊆ d '' base :=
      hbase.intermediate_value hx₀ hx hd
    have hzero : (0 : ℝ) ∈ Set.Icc (d x₀) (d x) := by
      constructor <;> dsimp [d] <;> linarith
    obtain ⟨z, hz, hdz⟩ := hintermediate hzero
    exact ((hne z hz) (sub_eq_zero.mp hdz)).elim

/-- Pairwise equality compatibility on a nonempty preconnected base gives a
finite strictly ordered list of the distinct function germs on that base. -/
theorem exists_charbonnelBoundaryOrdering
    {X : Type} [TopologicalSpace X] {J : Type} [Fintype J]
    {base : Set X} (hbase : IsPreconnected base) (hbaseNonempty : base.Nonempty)
    (f : J → X → ℝ) (hcontinuous : ∀ j, ContinuousOn (f j) base)
    (hpair : ∀ i j,
      Set.EqOn (f i) (f j) base ∨
        (∀ x ∈ base, f i x ≠ f j x)) :
    Nonempty (CharbonnelBoundaryOrdering base f) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hbaseNonempty
  let values : Finset ℝ := Finset.univ.image (fun j ↦ f j x₀)
  let value : Fin values.card → ℝ :=
    fun i ↦ (values.orderIsoOfFin rfl i).1
  have hvalue_exists : ∀ i, ∃ j, f j x₀ = value i := by
    intro i
    have hi : value i ∈ values := (values.orderIsoOfFin rfl i).2
    simpa [values] using hi
  let origin : Fin values.card → J :=
    fun i ↦ Classical.choose (hvalue_exists i)
  have horigin : ∀ i, f (origin i) x₀ = value i :=
    fun i ↦ Classical.choose_spec (hvalue_exists i)
  refine ⟨
    { count := values.card
      origin := origin
      strictlyOrdered := ?_
      represents := ?_ }⟩
  · intro x hx i j hij
    have hvalueLt : value i < value j := by
      exact (values.orderIsoOfFin rfl).strictMono hij
    have hx₀lt : f (origin i) x₀ < f (origin j) x₀ := by
      simpa [horigin] using hvalueLt
    rcases hpair (origin i) (origin j) with heq | hne
    · have := heq hx₀
      linarith
    · exact ltOn_of_preconnected_of_continuousOn_of_neOn
        hbase (hcontinuous (origin i)) (hcontinuous (origin j))
        hne hx₀ hx₀lt x hx
  · intro j
    have hjmem : f j x₀ ∈ values := by
      simp [values]
    let v : values := ⟨f j x₀, hjmem⟩
    let i : Fin values.card := (values.orderIsoOfFin rfl).symm v
    have hvalueEq : value i = f j x₀ := by
      change ((values.orderIsoOfFin rfl i).1 : ℝ) = f j x₀
      rw [show values.orderIsoOfFin rfl i = v by
        exact (values.orderIsoOfFin rfl).apply_symm_apply v]
    have hEqAt : f j x₀ = f (origin i) x₀ := by
      rw [horigin i, hvalueEq]
    rcases hpair j (origin i) with heq | hne
    · exact ⟨i, heq⟩
    · exact (hne x₀ hx₀ hEqAt).elim

/-! ## Selector regions versus recorded vertical cells -/

/-- Every selector region lies wholly below, on, or above any fixed selector
graph. -/
theorem charbonnelOrderedSelectorRegionCarrier_trichotomy
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (region : CharbonnelOrderedSelectorRegion r) (j : Fin r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelLowerRayCell base (f j) ∨
      charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelRestrictedGraph base (f j) ∨
      charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelUpperRayCell base (f j) := by
  cases region with
  | lower =>
      left
      intro z hz
      have hindex : charbonnelFirstSelectorIndex hr ≤ j := by
        show (charbonnelFirstSelectorIndex hr).1 ≤ j.1
        simp [charbonnelFirstSelectorIndex]
      have hmono := (hordered _ hz.1).monotone hindex
      exact ⟨hz.1, by linarith [hz.2, hmono]⟩
  | upper =>
      right
      right
      intro z hz
      have hindex : j ≤ charbonnelLastSelectorIndex hr := by
        show j.1 ≤ (charbonnelLastSelectorIndex hr).1
        simp [charbonnelLastSelectorIndex]
        omega
      have hmono := (hordered _ hz.1).monotone hindex
      exact ⟨hz.1, by linarith [hz.2, hmono]⟩
  | graph i =>
      rcases lt_trichotomy i j with hij | hij | hij
      · left
        intro z hz
        have hmono := hordered _ hz.1 hij
        exact ⟨hz.1, by linarith [hz.2, hmono]⟩
      · right
        left
        subst j
        exact Subset.rfl
      · right
        right
        intro z hz
        have hmono := hordered _ hz.1 hij
        exact ⟨hz.1, by linarith [hz.2, hmono]⟩
  | band i =>
      by_cases hj : j ≤ charbonnelBandLeftIndex i
      · right
        right
        intro z hz
        have hmono := (hordered _ hz.1).monotone hj
        exact ⟨hz.1, by linarith [hz.2.1, hmono]⟩
      · left
        have hright : charbonnelBandRightIndex i ≤ j := by
          show (charbonnelBandRightIndex i).1 ≤ j.1
          simp [charbonnelBandLeftIndex,
            charbonnelBandRightIndex] at hj ⊢
          omega
        intro z hz
        have hmono := (hordered _ hz.1).monotone hright
        exact ⟨hz.1, by linarith [hz.2.2, hmono]⟩

theorem disjoint_charbonnelLowerRayCell_restrictedGraph
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    Disjoint (charbonnelLowerRayCell base f)
      (charbonnelRestrictedGraph base f) := by
  rw [Set.disjoint_left]
  rintro z ⟨_, hlt⟩ ⟨_, heq⟩
  linarith

theorem disjoint_charbonnelRestrictedGraph_lowerRayCell
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    Disjoint (charbonnelRestrictedGraph base f)
      (charbonnelLowerRayCell base f) :=
  (disjoint_charbonnelLowerRayCell_restrictedGraph base f).symm

theorem disjoint_charbonnelRestrictedGraph_upperRayCell
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    Disjoint (charbonnelRestrictedGraph base f)
      (charbonnelUpperRayCell base f) := by
  rw [Set.disjoint_left]
  rintro z ⟨_, heq⟩ ⟨_, hlt⟩
  linarith

theorem disjoint_charbonnelUpperRayCell_restrictedGraph
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    Disjoint (charbonnelUpperRayCell base f)
      (charbonnelRestrictedGraph base f) :=
  (disjoint_charbonnelRestrictedGraph_upperRayCell base f).symm

theorem disjoint_charbonnelLowerRayCell_upperRayCell
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    Disjoint (charbonnelLowerRayCell base f)
      (charbonnelUpperRayCell base f) := by
  rw [Set.disjoint_left]
  rintro z ⟨_, hbelow⟩ ⟨_, habove⟩
  linarith

theorem disjoint_charbonnelUpperRayCell_lowerRayCell
    {n : ℕ} (base : Set (RealEuclidean n))
    (f : RealEuclidean n → ℝ) :
    Disjoint (charbonnelUpperRayCell base f)
      (charbonnelLowerRayCell base f) :=
  (disjoint_charbonnelLowerRayCell_upperRayCell base f).symm

/-- A selector region is compatible with each selector graph. -/
theorem charbonnelOrderedSelectorRegionCarrier_compatible_graph
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (region : CharbonnelOrderedSelectorRegion r) (j : Fin r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelRestrictedGraph base (f j) ∨
      Disjoint (charbonnelOrderedSelectorRegionCarrier base f hr region)
        (charbonnelRestrictedGraph base (f j)) := by
  rcases charbonnelOrderedSelectorRegionCarrier_trichotomy
      f hr hordered region j with hbelow | hequal | habove
  · right
    exact (disjoint_charbonnelLowerRayCell_restrictedGraph base (f j)).mono
      hbelow Subset.rfl
  · exact Or.inl hequal
  · right
    exact (disjoint_charbonnelUpperRayCell_restrictedGraph base (f j)).mono
      habove Subset.rfl

/-- A selector region is compatible with the lower ray below each selector. -/
theorem charbonnelOrderedSelectorRegionCarrier_compatible_lowerRay
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (region : CharbonnelOrderedSelectorRegion r) (j : Fin r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelLowerRayCell base (f j) ∨
      Disjoint (charbonnelOrderedSelectorRegionCarrier base f hr region)
        (charbonnelLowerRayCell base (f j)) := by
  rcases charbonnelOrderedSelectorRegionCarrier_trichotomy
      f hr hordered region j with hbelow | hequal | habove
  · exact Or.inl hbelow
  · right
    exact (disjoint_charbonnelRestrictedGraph_lowerRayCell base (f j)).mono
      hequal Subset.rfl
  · right
    exact (disjoint_charbonnelUpperRayCell_lowerRayCell base (f j)).mono
      habove Subset.rfl

/-- A selector region is compatible with the upper ray above each selector. -/
theorem charbonnelOrderedSelectorRegionCarrier_compatible_upperRay
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (region : CharbonnelOrderedSelectorRegion r) (j : Fin r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelUpperRayCell base (f j) ∨
      Disjoint (charbonnelOrderedSelectorRegionCarrier base f hr region)
        (charbonnelUpperRayCell base (f j)) := by
  rcases charbonnelOrderedSelectorRegionCarrier_trichotomy
      f hr hordered region j with hbelow | hequal | habove
  · right
    exact (disjoint_charbonnelLowerRayCell_upperRayCell base (f j)).mono
      hbelow Subset.rfl
  · right
    exact (disjoint_charbonnelRestrictedGraph_upperRayCell base (f j)).mono
      hequal Subset.rfl
  · exact Or.inl habove

/-- A selector region is compatible with every band whose two boundary
functions occur in the selector list. -/
theorem charbonnelOrderedSelectorRegionCarrier_compatible_band
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (region : CharbonnelOrderedSelectorRegion r) (left right : Fin r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        charbonnelOpenBand base (f left) (f right) ∨
      Disjoint (charbonnelOrderedSelectorRegionCarrier base f hr region)
        (charbonnelOpenBand base (f left) (f right)) := by
  have hband : charbonnelOpenBand base (f left) (f right) =
      charbonnelUpperRayCell base (f left) ∩
        charbonnelLowerRayCell base (f right) := by
    ext z
    simp [charbonnelOpenBand, charbonnelUpperRayCell,
      charbonnelLowerRayCell, and_assoc, and_left_comm, and_comm]
  rw [hband]
  rcases charbonnelOrderedSelectorRegionCarrier_trichotomy
      f hr hordered region left with hbelow | hequal | habove
  · right
    exact (disjoint_charbonnelLowerRayCell_upperRayCell base (f left)).mono
      hbelow inter_subset_left
  · right
    exact (disjoint_charbonnelRestrictedGraph_upperRayCell base (f left)).mono
      hequal inter_subset_left
  · rcases charbonnelOrderedSelectorRegionCarrier_trichotomy
        f hr hordered region right with hbelow | hequal | habove'
    · left
      exact fun z hz ↦ ⟨habove hz, hbelow hz⟩
    · right
      exact (disjoint_charbonnelRestrictedGraph_lowerRayCell base (f right)).mono
        hequal inter_subset_right
    · right
      exact (disjoint_charbonnelUpperRayCell_lowerRayCell base (f right)).mono
        habove' inter_subset_right

theorem charbonnelOrderedSelectorRegionCarrier_subset_cylinder
    {n r : ℕ} (base : Set (RealEuclidean n))
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (region : CharbonnelOrderedSelectorRegion r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
      charbonnelCylinderCell base := by
  intro z hz
  cases region <;> exact hz.1

/-! ### Restricting the semantic carrier to a refined base -/

def CharbonnelEnrichedVerticalCell.carrierOn
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    (small : Set (RealEuclidean n)) : Set (RealEuclidean (n + 1)) :=
  match cell with
  | .graph f _ _ => charbonnelRestrictedGraph small f
  | .band f g _ _ _ _ _ => charbonnelOpenBand small f g
  | .lowerRay g _ _ => charbonnelLowerRayCell small g
  | .upperRay f _ _ => charbonnelUpperRayCell small f
  | .cylinder => charbonnelCylinderCell small

theorem CharbonnelEnrichedVerticalCell.carrierOn_eq_inter_cylinder
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    (small : Set (RealEuclidean n)) (hsmall : small ⊆ base.carrier) :
    cell.carrierOn small =
      cell.carrier ∩ charbonnelCylinderCell small := by
  cases cell <;>
    ext z <;>
    simp [CharbonnelEnrichedVerticalCell.carrierOn,
      CharbonnelEnrichedVerticalCell.carrier,
      charbonnelRestrictedGraph, charbonnelOpenBand,
      charbonnelLowerRayCell, charbonnelUpperRayCell,
      charbonnelCylinderCell, and_assoc, and_left_comm, and_comm] <;>
    aesop

theorem charbonnelRestrictedGraph_eq_of_eqOn
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ} (hfg : Set.EqOn f g base) :
    charbonnelRestrictedGraph base f = charbonnelRestrictedGraph base g := by
  ext z
  constructor <;> rintro ⟨hz, hvalue⟩
  · exact ⟨hz, hvalue.trans (hfg hz)⟩
  · exact ⟨hz, hvalue.trans (hfg hz).symm⟩

theorem charbonnelLowerRayCell_eq_of_eqOn
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ} (hfg : Set.EqOn f g base) :
    charbonnelLowerRayCell base f = charbonnelLowerRayCell base g := by
  ext z
  simp only [charbonnelLowerRayCell, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hz, hvalue⟩
  · exact ⟨hz, by simpa [hfg hz] using hvalue⟩
  · exact ⟨hz, by simpa [hfg hz] using hvalue⟩

theorem charbonnelUpperRayCell_eq_of_eqOn
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ} (hfg : Set.EqOn f g base) :
    charbonnelUpperRayCell base f = charbonnelUpperRayCell base g := by
  ext z
  simp only [charbonnelUpperRayCell, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hz, hvalue⟩
  · exact ⟨hz, by simpa [hfg hz] using hvalue⟩
  · exact ⟨hz, by simpa [hfg hz] using hvalue⟩

theorem charbonnelOpenBand_eq_of_eqOn
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f f' g g' : RealEuclidean n → ℝ}
    (hf : Set.EqOn f f' base) (hg : Set.EqOn g g' base) :
    charbonnelOpenBand base f g = charbonnelOpenBand base f' g' := by
  ext z
  simp only [charbonnelOpenBand, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hz, hlower, hupper⟩
  · exact ⟨hz, by simpa [hf hz] using hlower,
      by simpa [hg hz] using hupper⟩
  · exact ⟨hz, by simpa [hf hz] using hlower,
      by simpa [hg hz] using hupper⟩

/-- Ordered selector regions are compatible with any enriched vertical cell
over the same base once every recorded boundary is represented by a selector. -/
theorem charbonnelOrderedSelectorRegionCarrier_compatible_enriched
    {S : EuclideanSetFamily} {n r : ℕ}
    {baseCell : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S baseCell)
    {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (hrep : ∀ b : Fin cell.boundaryCount,
      ∃ j, Set.EqOn (cell.boundary b) (f j) base)
    (region : CharbonnelOrderedSelectorRegion r) :
    charbonnelOrderedSelectorRegionCarrier base f hr region ⊆
        cell.carrierOn base ∨
      Disjoint (charbonnelOrderedSelectorRegionCarrier base f hr region)
        (cell.carrierOn base) := by
  cases cell with
  | graph g hg hgraph =>
      obtain ⟨j, hj⟩ := hrep (0 : Fin 1)
      have heq : charbonnelRestrictedGraph base g =
          charbonnelRestrictedGraph base (f j) :=
        charbonnelRestrictedGraph_eq_of_eqOn (by
          simpa [CharbonnelEnrichedVerticalCell.boundary] using hj)
      simpa [CharbonnelEnrichedVerticalCell.carrierOn, heq] using
        charbonnelOrderedSelectorRegionCarrier_compatible_graph
          f hr hordered region j
  | band g h hg hh hgh hgg hhh =>
      obtain ⟨j, hj⟩ := hrep (0 : Fin 2)
      obtain ⟨k, hk⟩ := hrep (1 : Fin 2)
      have heq : charbonnelOpenBand base g h =
          charbonnelOpenBand base (f j) (f k) :=
        charbonnelOpenBand_eq_of_eqOn
          (by simpa [CharbonnelEnrichedVerticalCell.boundary] using hj)
          (by simpa [CharbonnelEnrichedVerticalCell.boundary] using hk)
      simpa [CharbonnelEnrichedVerticalCell.carrierOn, heq] using
        charbonnelOrderedSelectorRegionCarrier_compatible_band
          f hr hordered region j k
  | lowerRay g hg hgraph =>
      obtain ⟨j, hj⟩ := hrep (0 : Fin 1)
      have heq : charbonnelLowerRayCell base g =
          charbonnelLowerRayCell base (f j) :=
        charbonnelLowerRayCell_eq_of_eqOn (by
          simpa [CharbonnelEnrichedVerticalCell.boundary] using hj)
      simpa [CharbonnelEnrichedVerticalCell.carrierOn, heq] using
        charbonnelOrderedSelectorRegionCarrier_compatible_lowerRay
          f hr hordered region j
  | upperRay g hg hgraph =>
      obtain ⟨j, hj⟩ := hrep (0 : Fin 1)
      have heq : charbonnelUpperRayCell base g =
          charbonnelUpperRayCell base (f j) :=
        charbonnelUpperRayCell_eq_of_eqOn (by
          simpa [CharbonnelEnrichedVerticalCell.boundary] using hj)
      simpa [CharbonnelEnrichedVerticalCell.carrierOn, heq] using
        charbonnelOrderedSelectorRegionCarrier_compatible_upperRay
          f hr hordered region j
  | cylinder =>
      left
      simpa [CharbonnelEnrichedVerticalCell.carrierOn] using
        charbonnelOrderedSelectorRegionCarrier_subset_cylinder
          base f hr region

theorem CharbonnelEnrichedVerticalCell.carrier_subset_cylinder
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base) :
    cell.carrier ⊆ charbonnelCylinderCell base.carrier := by
  intro z hz
  cases cell with
  | graph => exact hz.1
  | band => exact hz.1
  | lowerRay => exact hz.1
  | upperRay => exact hz.1
  | cylinder => exact hz

/-- Compatibility on a restricted base transfers back to the original
enriched carrier. -/
theorem compatible_enriched_of_compatible_carrierOn
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    {small : Set (RealEuclidean n)} (hsmall : small ⊆ base.carrier)
    {region : Set (RealEuclidean (n + 1))}
    (hregion : region ⊆ charbonnelCylinderCell small)
    (hcompat : region ⊆ cell.carrierOn small ∨
      Disjoint region (cell.carrierOn small)) :
    region ⊆ cell.carrier ∨ Disjoint region cell.carrier := by
  rw [cell.carrierOn_eq_inter_cylinder small hsmall] at hcompat
  rcases hcompat with hsubset | hdisjoint
  · exact Or.inl (hsubset.trans inter_subset_left)
  · right
    rw [Set.disjoint_left]
    intro z hzRegion hzCell
    exact Set.disjoint_left.mp hdisjoint hzRegion
      ⟨hzCell, hregion hzRegion⟩

/-- If the refined base misses the recorded projected base, every cell over
the refined base misses the enriched successor cell. -/
theorem disjoint_enriched_of_disjoint_bases
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    {small : Set (RealEuclidean n)}
    (hdisjoint : Disjoint small base.carrier)
    {region : Set (RealEuclidean (n + 1))}
    (hregion : region ⊆ charbonnelCylinderCell small) :
    Disjoint region cell.carrier := by
  rw [Set.disjoint_left]
  intro z hzRegion hzCell
  exact Set.disjoint_left.mp hdisjoint (hregion hzRegion)
    (cell.carrier_subset_cylinder hzCell)

/-! ## Local simultaneous selector covers -/

/-- A finite family of recursive cells covering `domain` and compatible with
every member of a target family. -/
structure CharbonnelFiniteSimultaneouslyCompatibleRelativeCellCover
    (C : EuclideanSetFamily) {n : ℕ} {I : Type}
    (domain : Set (RealEuclidean n))
    (target : I → Set (RealEuclidean n)) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelCell C n
  contained : ∀ i, (cell i).carrier ⊆ domain
  covers : ∀ x ∈ domain, ∃ i, x ∈ (cell i).carrier
  compatible : ∀ i j,
    (cell i).carrier ⊆ target j ∨ Disjoint (cell i).carrier (target j)

/-- Boundary indices whose recorded base contains one refined base cell. -/
abbrev CharbonnelActiveEnrichedBoundary
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count) :=
  {q : CharbonnelEnrichedBoundaryIndex input //
    (refinement.cell k).carrier ⊆ (input q.1).base.carrier}

def charbonnelActiveEnrichedBoundaryFunction
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count)
    (q : CharbonnelActiveEnrichedBoundary refinement k) :
    RealEuclidean n → ℝ :=
  (input q.1.1).boundary q.1.2

theorem exists_charbonnelActiveBoundaryOrdering
    {S : EuclideanSetFamily} {n : ℕ} {I : Type} [Fintype I]
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count) :
    Nonempty (CharbonnelBoundaryOrdering
      (refinement.cell k).carrier
      (charbonnelActiveEnrichedBoundaryFunction refinement k)) := by
  classical
  let J := CharbonnelActiveEnrichedBoundary refinement k
  letI : Fintype J := Fintype.ofFinite J
  let D := (refinement.cell k).carrier
  let f : J → RealEuclidean n → ℝ :=
    charbonnelActiveEnrichedBoundaryFunction refinement k
  by_cases hD : D.Nonempty
  · apply exists_charbonnelBoundaryOrdering
      (refinement.cell k).shape.isPreconnected hD f
    · intro q
      exact ((input q.1.1).boundary_continuous q.1.2).mono q.2
    · intro q r
      exact refinement.boundary_eqOn_or_neOn k q.1 r.1 q.2 r.2
  · let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    exact ⟨
      { count := Fintype.card J
        origin := e
        strictlyOrdered := by
          intro x hx
          exact (hD ⟨x, hx⟩).elim
        represents := by
          intro q
          refine ⟨e.symm q, ?_⟩
          intro x hx
          exact (hD ⟨x, hx⟩).elim }⟩

theorem CharbonnelEnrichedVerticalCell.carrier_eq_cylinder_of_boundaryCount_eq_zero
    {S : EuclideanSetFamily} {n : ℕ}
    {base : CharbonnelCell (charbonnelClosure S) n}
    (cell : CharbonnelEnrichedVerticalCell S base)
    (hzero : cell.boundaryCount = 0) :
    cell.carrier = charbonnelCylinderCell base.carrier := by
  cases cell <;> simp_all [CharbonnelEnrichedVerticalCell.boundaryCount,
    CharbonnelEnrichedVerticalCell.carrier]

/-- Over one equality-compatible refined base cell, the active boundary
functions cut the cylinder into recursive cells compatible with every
enriched input cell. -/
theorem exists_charbonnelEnrichedLocalSelectorCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (refinement.cell k).carrier)
        (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨ordering⟩ := exists_charbonnelActiveBoundaryOrdering refinement k
  let J := CharbonnelActiveEnrichedBoundary refinement k
  let active : J → RealEuclidean n → ℝ :=
    charbonnelActiveEnrichedBoundaryFunction refinement k
  let selector : Fin ordering.count → RealEuclidean n → ℝ :=
    fun i ↦ active (ordering.origin i)
  have hcontinuous : ∀ i,
      ContinuousOn (selector i) (refinement.cell k).carrier := by
    intro i
    exact ((input (ordering.origin i).1.1).boundary_continuous
      (ordering.origin i).1.2).mono (ordering.origin i).2
  have hordered : ∀ x ∈ (refinement.cell k).carrier,
      StrictMono (fun i ↦ selector i x) := by
    simpa [selector, active] using ordering.strictlyOrdered
  have hgraph : ∀ i,
      charbonnelRestrictedGraph (refinement.cell k).carrier (selector i) ∈
        charbonnelClosure S (n + 1) := by
    intro i
    apply charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
      hC hn (ordering.origin i).2 (refinement.cell k).carrier_mem
    exact (input (ordering.origin i).1.1).boundary_graph_mem
      (ordering.origin i).1.2
  by_cases hr : 0 < ordering.count
  · have hmem : ∀ region,
        charbonnelOrderedSelectorRegionCarrier
            (refinement.cell k).carrier selector hr region ∈
          charbonnelClosure S (n + 1) :=
      fun region ↦
        charbonnelOrderedSelectorRegionCarrier_mem_charbonnelClosure
          hC selector hgraph hr region
    let cell : CharbonnelOrderedSelectorRegion ordering.count →
        CharbonnelCell (charbonnelClosure S) (n + 1) :=
      charbonnelOrderedSelectorCell hn (refinement.cell k).shape
        selector hr hcontinuous hordered hmem
    refine ⟨
      { Index := CharbonnelOrderedSelectorRegion ordering.count
        indexFinite := inferInstance
        cell := cell
        contained := ?_
        covers := ?_
        compatible := ?_ }⟩
    · intro region z hz
      exact charbonnelOrderedSelectorRegionCarrier_subset_cylinder
        (refinement.cell k).carrier selector hr region hz
    · intro z hz
      obtain ⟨region, hregion⟩ :=
        exists_charbonnelOrderedSelectorRegion_contains hr
          (fun i ↦ selector i (realEuclideanTakeLeft z))
          (realEuclideanTakeRight z 0)
      refine ⟨region, ?_⟩
      cases region <;> exact ⟨hz, hregion⟩
    · intro region i
      change charbonnelOrderedSelectorRegionCarrier
          (refinement.cell k).carrier selector hr region ⊆
            (input i).carrier ∨
        Disjoint (charbonnelOrderedSelectorRegionCarrier
          (refinement.cell k).carrier selector hr region) (input i).carrier
      have hregion :
          charbonnelOrderedSelectorRegionCarrier
              (refinement.cell k).carrier selector hr region ⊆
            charbonnelCylinderCell (refinement.cell k).carrier :=
        charbonnelOrderedSelectorRegionCarrier_subset_cylinder
          (refinement.cell k).carrier selector hr region
      rcases refinement.base_compatible k i with hsubset | hdisjoint
      · have hrep : ∀ b : Fin (input i).boundaryCount,
            ∃ j, Set.EqOn ((input i).boundary b) (selector j)
              (refinement.cell k).carrier := by
          intro b
          let q : J := ⟨⟨i, b⟩, hsubset⟩
          obtain ⟨j, hj⟩ := ordering.represents q
          exact ⟨j, by simpa [q, active, selector,
            charbonnelActiveEnrichedBoundaryFunction] using hj⟩
        have hlocal :=
          charbonnelOrderedSelectorRegionCarrier_compatible_enriched
            (input i).vertical selector hr hordered hrep region
        simpa [CharbonnelEnrichedSuccessorCell.carrier] using
          compatible_enriched_of_compatible_carrierOn
            (input i).vertical hsubset hregion hlocal
      · right
        simpa [CharbonnelEnrichedSuccessorCell.carrier] using
          disjoint_enriched_of_disjoint_bases
            (input i).vertical hdisjoint hregion
  · have hrzero : ordering.count = 0 := Nat.eq_zero_of_not_pos hr
    let cylinder : CharbonnelCell (charbonnelClosure S) (n + 1) :=
      { carrier := charbonnelCylinderCell (refinement.cell k).carrier
        shape := .cylinder hn (refinement.cell k).shape
        carrier_mem := charbonnelCylinderCell_mem_charbonnelClosure
          hC hn (refinement.cell k).carrier_mem }
    refine ⟨
      { Index := Unit
        indexFinite := inferInstance
        cell := fun _ ↦ cylinder
        contained := fun _ ↦ Subset.rfl
        covers := fun z hz ↦ ⟨(), hz⟩
        compatible := ?_ }⟩
    intro _ i
    change charbonnelCylinderCell (refinement.cell k).carrier ⊆
          (input i).carrier ∨
      Disjoint (charbonnelCylinderCell (refinement.cell k).carrier)
        (input i).carrier
    rcases refinement.base_compatible k i with hsubset | hdisjoint
    · by_cases hD : (refinement.cell k).carrier.Nonempty
      · have hboundaryZero : (input i).boundaryCount = 0 := by
          by_contra hne
          have hpos : 0 < (input i).boundaryCount :=
            Nat.pos_of_ne_zero hne
          let b : Fin (input i).boundaryCount := ⟨0, hpos⟩
          let q : J := ⟨⟨i, b⟩, hsubset⟩
          obtain ⟨j, _hj⟩ := ordering.represents q
          exact (hr (Nat.zero_lt_of_lt j.isLt)).elim
        have hcarrier :=
          (input i).vertical.carrier_eq_cylinder_of_boundaryCount_eq_zero
            hboundaryZero
        left
        intro z hz
        change z ∈ (input i).vertical.carrier
        rw [hcarrier]
        exact hsubset hz
      · right
        rw [Set.disjoint_left]
        intro z hz _hzTarget
        exact hD ⟨realEuclideanTakeLeft z, hz⟩
    · right
      simpa [CharbonnelEnrichedSuccessorCell.carrier] using
        disjoint_enriched_of_disjoint_bases
          (input i).vertical hdisjoint (Subset.rfl :
            charbonnelCylinderCell (refinement.cell k).carrier ⊆
              charbonnelCylinderCell (refinement.cell k).carrier)

/-! ## The enriched successor common-refinement theorem -/

/-- Source-shaped sound fragment of Wilkie's successor step `(II)_{n+1}`.

For a finite family of successor cells carrying their projected bases and
boundary-graph membership certificates, the lower-dimensional instances of
`(I)` and `(II)` suffice to construct one finite recursive-cell cover in the
successor dimension compatible with every input carrier. -/
theorem charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover
        (charbonnelClosure S) (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨refinement⟩ :=
    exists_charbonnelEnrichedEqualityBaseRefinement hC hI hII hn input
  let lift : ∀ k,
      CharbonnelFiniteSimultaneouslyCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (refinement.cell k).carrier)
        (fun i ↦ (input i).carrier) :=
    fun k ↦ Classical.choice
      (exists_charbonnelEnrichedLocalSelectorCover hC hn refinement k)
  letI : ∀ k, Finite (lift k).Index := fun k ↦ (lift k).indexFinite
  let Index := Σ k, (lift k).Index
  letI : Fintype Index := Fintype.ofFinite Index
  let e : Fin (Fintype.card Index) ≃ Index :=
    (Fintype.equivFin Index).symm
  refine ⟨
    { count := Fintype.card Index
      cell := fun q ↦ (lift (e q).1).cell (e q).2
      covers := ?_
      compatible := ?_ }⟩
  · intro z
    obtain ⟨k, hk⟩ := refinement.covers (realEuclideanTakeLeft z)
    have hzCylinder : z ∈
        charbonnelCylinderCell (refinement.cell k).carrier := hk
    obtain ⟨j, hj⟩ := (lift k).covers z hzCylinder
    refine ⟨e.symm ⟨k, j⟩, ?_⟩
    rw [e.apply_symm_apply]
    exact hj
  · intro q i
    exact (lift (e q).1).compatible (e q).2 i

/-- The same theorem stated using the ordinary cells obtained by forgetting
the enrichment. -/
theorem charbonnelFiniteEnrichedOrdinaryCellFamilyCommonRefinement_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover
        (charbonnelClosure S)
        (fun i ↦ ((input i).toCell hC hn).carrier)) := by
  simpa using
    charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ
      hC hI hII hn input

end AbelFormalization
