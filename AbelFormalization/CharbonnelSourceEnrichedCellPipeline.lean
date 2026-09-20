import AbelFormalization.WilkieSection4EnrichedCells
import AbelFormalization.CharbonnelSourceComplementPipeline
import AbelFormalization.WilkieBoundedComplementAssembly

/-!
# Enriched cells in the source complement pipeline

`WilkieSection4EnrichedCells` proves the geometric successor construction
when the lower-dimensional common-refinement hypothesis is packaged for all
arities at once.  The source induction is dimension-by-dimension.  This file
provides the corresponding local API and records exactly what is still needed
to feed the enriched construction into the complement endpoint.

The main structural result is that the unary common-refinement theorem and
the enriched successor theorem prove `(II)` in every positive dimension as
soon as ordinary successor cells retain their projected bases and boundary
graph membership certificates.  A finite enriched decomposition of each
projected closed lift then gives the compatible cover required by the source
complement pipeline.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Dimension-local common refinement -/

/-- Wilkie's finite-cell common-refinement assertion `(II)ₙ`, at one fixed
positive dimension.  The dimension-local form is the one used by induction. -/
def CharbonnelFiniteCellFamilyCommonRefinementAt
    (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι],
    ∀ cells : ι → CharbonnelCell C n,
      Nonempty
        (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
          (fun i ↦ (cells i).carrier))

/-- The family-wide property implies its fixed-dimensional instance. -/
theorem charbonnelFiniteCellFamilyCommonRefinementAt_of_global
    {C : EuclideanSetFamily}
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty C)
    (n : ℕ) :
    CharbonnelFiniteCellFamilyCommonRefinementAt C n :=
  fun cells ↦ hII cells

/-- A fixed-dimensional common-refinement theorem combines arbitrary finite
families of individual compatible covers. -/
theorem finiteSimultaneouslyCompatibleCellCover_of_individual_at
    {C : EuclideanSetFamily} {n : ℕ}
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt C n)
    {ι : Type} [Fintype ι]
    (target : ι → Set (RealEuclidean n))
    (hcover : ∀ i,
      Nonempty (CharbonnelFiniteCompatibleCellCover C (target i))) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C target) := by
  classical
  let cover : ∀ i, CharbonnelFiniteCompatibleCellCover C (target i) :=
    fun i ↦ Classical.choice (hcover i)
  let cells : (Σ i, Fin (cover i).count) → CharbonnelCell C n :=
    fun q ↦ (cover q.1).cell q.2
  obtain ⟨fine⟩ := hII cells
  refine ⟨
    { count := fine.count
      cell := fine.cell
      covers := fine.covers
      compatible := ?_ }⟩
  intro i j
  apply compatible_target_of_compatible_cover_cells (cover := cover j)
  intro k
  exact fine.compatible i ⟨j, k⟩

/-- Dimension-local form of the equality-compatible base refinement used in
the enriched successor construction. -/
theorem exists_charbonnelEnrichedEqualityBaseRefinement_at
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) n)
    {I : Type} [Fintype I]
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
    finiteSimultaneouslyCompatibleCellCover_of_individual_at
      hII target htarget
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

/-- Dimension-local enriched successor theorem.  It uses `(I)ₙ` and
`(II)ₙ` only at the base dimension and constructs `(II)_{n+1}` for an
arbitrary finite enriched input family. -/
theorem charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ_at
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) n)
    {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover
        (charbonnelClosure S) (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨refinement⟩ :=
    exists_charbonnelEnrichedEqualityBaseRefinement_at
      hC hI hn hII input
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

/-! ## Retaining enrichment through the source construction -/

/-- Every ordinary successor cell constructed at a given stage has an
enriched representative with the same carrier.  This is the precise datum
lost by the older `CharbonnelCell` API: the projected base and the membership
certificates for each boundary graph. -/
def CharbonnelSuccessorCellEnrichmentAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ cell : CharbonnelCell (charbonnelClosure S) (n + 1),
    ∃ enriched : CharbonnelEnrichedSuccessorCell S n,
      enriched.carrier = cell.carrier

/-- Enrichment retention at every positive base dimension. -/
def CharbonnelPositiveDimensionalSuccessorCellEnrichment
    (S : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → CharbonnelSuccessorCellEnrichmentAt S n

/-- If all ordinary successor cells retain their enrichment, the local
enriched theorem upgrades `(II)ₙ` to ordinary `(II)_{n+1}`. -/
theorem charbonnelFiniteCellFamilyCommonRefinement_succ_at_of_enrichment
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) n)
    (henrich : CharbonnelSuccessorCellEnrichmentAt S n) :
    CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) (n + 1) := by
  classical
  intro I inst input
  let enriched : I → CharbonnelEnrichedSuccessorCell S n :=
    fun i ↦ Classical.choose (henrich (input i))
  have hcarrier : ∀ i, (enriched i).carrier = (input i).carrier :=
    fun i ↦ Classical.choose_spec (henrich (input i))
  obtain ⟨cover⟩ :=
    charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ_at
      hC hI hn hII enriched
  refine ⟨
    { count := cover.count
      cell := cover.cell
      covers := cover.covers
      compatible := ?_ }⟩
  intro i j
  simpa [hcarrier j] using cover.compatible i j

/-- The unary theorem and enrichment retention prove Wilkie's finite common
refinement assertion in every positive dimension. -/
theorem charbonnelPositiveDimensionalCellFamilyCommonRefinement_of_enrichment
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (henrich : CharbonnelPositiveDimensionalSuccessorCellEnrichment S) :
    ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteCellFamilyCommonRefinementAt
        (charbonnelClosure S) n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hone : n = 1
      · subst n
        exact charbonnelFiniteCellFamilyCommonRefinement_one hC
      · obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        have hp : 0 < p := by omega
        exact charbonnelFiniteCellFamilyCommonRefinement_succ_at_of_enrichment
          hC.toPositiveArityWeakSetStructure hI hp
          (ih p (by omega) hp) (henrich hp)

/-! ## Enriched decompositions of projected closed lifts -/

/-- A finite decomposition of a target into enriched successor cells.  No
pairwise-disjointness is needed for the complement endpoint. -/
structure CharbonnelFiniteEnrichedSuccessorDecomposition
    (S : EuclideanSetFamily) (n : ℕ)
    (A : Set (RealEuclidean (n + 1))) where
  count : ℕ
  cell : Fin count → CharbonnelEnrichedSuccessorCell S n
  union_eq : A = ⋃ i, (cell i).carrier

/-- A set compatible with every member of a family is compatible with their
union.  This set-theoretic lemma does not require the index type to be finite. -/
theorem subset_iUnion_or_disjoint_iUnion_of_compatible
    {X I : Type} {s : Set X} {target : I → Set X}
    (hcompatible : ∀ i, s ⊆ target i ∨ Disjoint s (target i)) :
    s ⊆ ⋃ i, target i ∨ Disjoint s (⋃ i, target i) := by
  classical
  by_cases hhit : ∃ i, ¬ Disjoint s (target i)
  · obtain ⟨i, hi⟩ := hhit
    rcases hcompatible i with hsubset | hdisjoint
    · exact Or.inl (hsubset.trans (Set.subset_iUnion target i))
    · exact (hi hdisjoint).elim
  · right
    rw [Set.disjoint_left]
    intro x hxs hxUnion
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxUnion
    exact hhit ⟨i, fun hdisjoint ↦
      Set.disjoint_left.mp hdisjoint hxs hxi⟩

/-- A finite enriched decomposition of a target, together with the
lower-dimensional `(I)` and `(II)` statements, constructs a full compatible
cell cover of that target. -/
theorem exists_charbonnelFiniteCompatibleCellCover_of_enrichedDecomposition
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) n)
    {A : Set (RealEuclidean (n + 1))}
    (decomposition : CharbonnelFiniteEnrichedSuccessorDecomposition S n A) :
    Nonempty
      (CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A) := by
  obtain ⟨cover⟩ :=
    charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ_at
      hC hI hn hII decomposition.cell
  refine ⟨
    { count := cover.count
      cell := cover.cell
      covers := cover.covers
      compatible := ?_ }⟩
  intro i
  rcases subset_iUnion_or_disjoint_iUnion_of_compatible
      (cover.compatible i) with hsubset | hdisjoint
  · left
    exact hsubset.trans decomposition.union_eq.symm.subset
  · right
    exact hdisjoint.mono Subset.rfl decomposition.union_eq.subset

/-- Source-shaped enriched residual for projected closed lifts.  In visible
dimension `n + 1 > 1`, the projection of every closed lift must be a finite
union of enriched successor cells. -/
def CharbonnelEnrichedProjectedClosedLiftDecompositionProperty
    (S : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 0 < n →
    ∀ {B : Set (RealEuclidean ((n + 1) + q))},
      IsClosed B → B ∈ charbonnelClosure S ((n + 1) + q) →
        Nonempty (CharbonnelFiniteEnrichedSuccessorDecomposition S n
          (realEuclideanExistentialProjection B))

/-- Retained enrichment turns enriched projected-lift decompositions into the
higher-dimensional compatible covers consumed by the existing complement
pipeline. -/
theorem
    charbonnelHigherDimensionalClosedLiftCellCoverProperty_of_enrichedDecompositions
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (henrich : CharbonnelPositiveDimensionalSuccessorCellEnrichment S)
    (hdecomposition :
      CharbonnelEnrichedProjectedClosedLiftDecompositionProperty S) :
    CharbonnelHigherDimensionalClosedLiftCellCoverProperty
      (charbonnelClosure S) := by
  intro d q hd B hBclosed hBmem
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hn : 0 < n := by omega
  obtain ⟨decomposition⟩ := hdecomposition hn hBclosed hBmem
  exact exists_charbonnelFiniteCompatibleCellCover_of_enrichedDecomposition
    hC.toPositiveArityWeakSetStructure hI hn
      (charbonnelPositiveDimensionalCellFamilyCommonRefinement_of_enrichment
        hC hI henrich hn)
      decomposition

/-! ## Source-pipeline bridge -/

/-- The three enriched pieces still required from Wilkie's Section 4
induction after the unary base and the enriched common-refinement successor
have been formalized. -/
structure CharbonnelEnrichedCellInductionData
    (S : EuclideanSetFamily) : Prop where
  closedMemberCovers :
    CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S)
  successorEnrichment :
    CharbonnelPositiveDimensionalSuccessorCellEnrichment S
  projectedClosedLiftDecompositions :
    CharbonnelEnrichedProjectedClosedLiftDecompositionProperty S

/-- Source-facing assembly statement: the proved boundary-carrier theorem may
be used to construct the three remaining enriched induction data. -/
def CharbonnelEnrichedClosedBoundaryCellCoverAssembly
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  CharbonnelClosedBoundaryCarrierProperty G →
    CharbonnelEnrichedCellInductionData (literalZeroSetFamily G)

/-- The enriched Section 4 assembly discharges the older abstract
higher-dimensional closed-lift cover premise. -/
theorem charbonnelClosedBoundaryCellCoverAssembly_of_enrichedCells
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (henriched : CharbonnelEnrichedClosedBoundaryCellCoverAssembly G) :
    CharbonnelClosedBoundaryCellCoverAssembly G := by
  intro hboundary
  let data := henriched hboundary
  apply
    charbonnelHigherDimensionalClosedLiftCellCoverProperty_of_enrichedDecompositions
  · exact
      literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
        hG hsmooth hUFF
  · exact data.closedMemberCovers
  · exact data.successorEnrichment
  · exact data.projectedClosedLiftDecompositions

/-- Pointwise Abel endpoint with the remaining cell premise expressed by the
enriched Section 4 induction data. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_enrichedCells
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (henriched : CharbonnelEnrichedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_cellCovers
    hUFF hselection hanalytic
    (charbonnelClosedBoundaryCellCoverAssembly_of_enrichedCells
      hG hsmooth hUFF henriched)

/-- Family-wide main-theorem reduction with the Section 4 residual stated in
the enriched form. -/
theorem mainTheorem_of_charbonnelSourceSteps_automaticProjection_and_enrichedCells
    (hUFF : ∀ (A : ℝ → ℝ), IsAbel A →
      HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : ∀ (A : ℝ → ℝ), IsAbel A →
      HasMaxwellMeagreClosureComponentSelection
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSection5AnalyticStep
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (henriched : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelEnrichedClosedBoundaryCellCoverAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_enrichedCells
    (hUFF A hA) (hselection A hA) (hanalytic A hA) (henriched A hA)

/-! ## Bounded-coordinate enriched relative covers -/

/-- A finite relative compatible cover whose cells retain the projected base
and all boundary-graph membership certificates.  Forgetting that extra data
gives `CharbonnelFiniteCompatibleRelativeCellCover`. -/
structure CharbonnelFiniteEnrichedCompatibleRelativeCellCover
    (S : EuclideanSetFamily) (n : ℕ)
    (domain target : Set (RealEuclidean (n + 1))) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelEnrichedSuccessorCell S n
  contained : ∀ i, (cell i).carrier ⊆ domain
  covers : ∀ x ∈ domain, ∃ i, x ∈ (cell i).carrier
  compatible : ∀ i,
    (cell i).carrier ⊆ target ∨ Disjoint (cell i).carrier target

namespace CharbonnelFiniteEnrichedCompatibleRelativeCellCover

/-- Forget the retained bases and boundary certificates in an enriched
relative cover. -/
def toRelativeCellCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {domain target : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteEnrichedCompatibleRelativeCellCover
      S n domain target) :
    CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) domain target :=
  { Index := cover.Index
    indexFinite := cover.indexFinite
    cell := fun i ↦ (cover.cell i).toCell hC hn
    contained := by
      intro i
      simpa using cover.contained i
    covers := by
      intro x hx
      obtain ⟨i, hi⟩ := cover.covers x hx
      exact ⟨i, by simpa using hi⟩
    compatible := by
      intro i
      simpa using cover.compatible i }

end CharbonnelFiniteEnrichedCompatibleRelativeCellCover

/-- Enriched bounded-coordinate form of the remaining closed-lift cell
construction.  Unlike the ordinary bounded premise, every output cell keeps
the source data consumed by the enriched successor theorem. -/
def WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty
    (S : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 0 < n →
    ∀ {B : Set (RealEuclidean ((n + 1) + q))},
      IsClosed B → B ∈ charbonnelClosure S ((n + 1) + q) →
        Nonempty (CharbonnelFiniteEnrichedCompatibleRelativeCellCover S n
          (wilkieOpenCube (n + 1))
          (wilkieBoundedImage (realEuclideanExistentialProjection B)))

/-- Forgetting enrichment in each cube-relative cell yields the exact bounded
cover property used by the compactification complement theorem. -/
theorem wilkieBoundedProjectedClosedLiftCellCoverProperty_of_enriched
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (henriched :
      WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty S) :
    WilkieBoundedProjectedClosedLiftCellCoverProperty
      (charbonnelClosure S) := by
  intro d q hd B hBclosed hBmem
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hn : 0 < n := by omega
  obtain ⟨cover⟩ := henriched hn hBclosed hBmem
  exact ⟨cover.toRelativeCellCover hC hn⟩

/-- Source-facing bounded enriched assembly.  The established boundary
carrier theorem may be used when constructing the enriched relative covers. -/
def CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  CharbonnelClosedBoundaryCarrierProperty G →
    WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty
      (literalZeroSetFamily G)

/-- The bounded enriched assembly forgets to the bounded ordinary assembly
consumed by `WilkieBoundedComplementAssembly`. -/
theorem charbonnelBoundedClosedBoundaryCellCoverAssembly_of_enrichedCells
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (henriched :
      CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly G) :
    CharbonnelBoundedClosedBoundaryCellCoverAssembly G := by
  intro hboundary
  exact wilkieBoundedProjectedClosedLiftCellCoverProperty_of_enriched
    (literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
      hG hsmooth)
    (henriched hboundary)

/-- Pointwise Abel endpoint using enriched relative covers inside Wilkie's
bounded-coordinate cube. -/
theorem
    IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedEnrichedCells
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (henriched : CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection
    hUFF hselection hanalytic
    (charbonnelClosedBoundaryComplementAssembly_of_boundedCellCovers
      hG hsmooth hUFF
      (charbonnelBoundedClosedBoundaryCellCoverAssembly_of_enrichedCells
        hG hsmooth henriched))

/-- Family-wide main-theorem reduction whose Section 4 input is an enriched
relative decomposition of the bounded open cube. -/
theorem
    mainTheorem_of_charbonnelSourceSteps_automaticProjection_and_boundedEnrichedCells
    (hUFF : ∀ (A : ℝ → ℝ), IsAbel A →
      HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : ∀ (A : ℝ → ℝ), IsAbel A →
      HasMaxwellMeagreClosureComponentSelection
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelSection5AnalyticStep
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))))
    (henriched : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedEnrichedCells
      (hUFF A hA) (hselection A hA) (hanalytic A hA) (henriched A hA)

end AbelFormalization
