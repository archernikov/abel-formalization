import AbelFormalization.WilkieProjectionCoherentCellCover
import AbelFormalization.CharbonnelSourceEnrichedCellPipeline
import AbelFormalization.WilkieSection4EnrichedSelectorOutput

/-!
# Towers of projection-coherent enriched cell covers

`WilkieProjectionCoherentCellCover` proves the one-coordinate projection
step.  Iterating that step requires more data than one top-dimensional cover:
after projection its cells are ordinary `CharbonnelCell`s, so their own
projected bases and boundary-graph membership certificates are no longer
available.  This module records the exact lossless input for repetition: a
coherent enriched cover at every positive-dimensional stage.

From such a tower we obtain, without any further hypothesis, a tower of
relative compatible covers of all successive projections.  The established
positive-dimensional common-refinement property upgrades those relative
covers to global compatible covers.  Finally, the top coherent cover forgets
to the enriched bounded relative cover already consumed by the bounded
complement pipeline.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Iterated projection down to one coordinate -/

/-- Project away the last coordinate repeatedly, stopping in dimension one.
For an input in dimension `n + 1`, this performs exactly `n` successive
one-coordinate existential projections. -/
def realEuclideanIteratedExistentialProjectionToOne :
    (n : ℕ) → Set (RealEuclidean (n + 1)) → Set (RealEuclidean 1)
  | 0, A => A
  | n + 1, A =>
      realEuclideanIteratedExistentialProjectionToOne n
        (realEuclideanExistentialProjection A)

/-! ## Coherent input towers and their relative projections -/

/-- A coherent enriched relative cover at every stage from dimension
`n + 1` down through dimension two.  The lower stage has exactly the
existential projections of the preceding domain and target, so the data form
an actual projection tower rather than an unrelated family of covers.

There is deliberately no zero-dimensional constructor.  The final coherent
cover is two-dimensional and its one-step projection is the compatible cover
in dimension one where Wilkie's induction stops. -/
inductive CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
    (S : EuclideanSetFamily) :
    (n : ℕ) → Set (RealEuclidean (n + 1)) →
      Set (RealEuclidean (n + 1)) → Type 2
  | one {D A : Set (RealEuclidean (1 + 1))}
      (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A) :
      CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower S 1 D A
  | succ {n : ℕ}
      {D A : Set (RealEuclidean ((n + 1) + 1))}
      (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A)
      (lower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower S n
        (realEuclideanExistentialProjection D)
        (realEuclideanExistentialProjection A)) :
      CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower S (n + 1) D A

namespace CharbonnelFiniteProjectionCoherentEnrichedCellCover

/-- Forget projection coherence while retaining the enriched cells. -/
def toEnrichedRelativeCellCover
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A) :
    CharbonnelFiniteEnrichedCompatibleRelativeCellCover S n D A where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell := cover.cell
  contained := cover.contained
  covers := cover.covers
  compatible := cover.compatible

/-- Forget both projection coherence and enrichment. -/
def toRelativeCellCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A) :
    CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) D A :=
  cover.toEnrichedRelativeCellCover.toRelativeCellCover hC hn

end CharbonnelFiniteProjectionCoherentEnrichedCellCover

namespace CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover

/-- The retained selector output is a projection-coherent cover as soon as
its recorded refined base cells are pairwise equal or disjoint.  This is the
precise bridge from `WilkieSection4EnrichedSelectorOutput`: all other fields
are already supplied by that module's flattened enriched cover. -/
def targetProjectionCoherentCover
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {domain : Set (RealEuclidean (n + 1))}
    {target : I → Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
      S domain target)
    (j : I) (htarget : target j ⊆ domain)
    (hbases : ∀ i k,
      (cover.cell i).base.carrier = (cover.cell k).base.carrier ∨
        Disjoint (cover.cell i).base.carrier
          (cover.cell k).base.carrier) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCover
      S domain (target j) where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell := cover.cell
  target_subset_domain := htarget
  contained := cover.contained
  covers := cover.covers
  compatible := fun i ↦ cover.compatible i j
  bases_eq_or_disjoint := hbases

/-- Global retained selector output needs only pairwise equality-or-
disjointness of its recorded bases to become projection coherent. -/
def targetProjectionCoherentCover_univ
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {target : I → Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
      S Set.univ target)
    (j : I)
    (hbases : ∀ i k,
      (cover.cell i).base.carrier = (cover.cell k).base.carrier ∨
        Disjoint (cover.cell i).base.carrier
          (cover.cell k).base.carrier) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCover
      S Set.univ (target j) :=
  cover.targetProjectionCoherentCover j (Set.subset_univ _) hbases

end CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover

namespace CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower

/-- The coherent cover at the top stage of a tower. -/
def top
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
      S n D A) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A := by
  cases tower with
  | one cover => exact cover
  | succ cover lower => exact cover

/-- The tail after one projection.  An inhabitant at a successor height can
only have been built by the successor constructor. -/
def lower
    {S : EuclideanSetFamily} {n : ℕ}
    (hn : 0 < n)
    {D A : Set (RealEuclidean ((n + 1) + 1))}
    (tower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
      S (n + 1) D A) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower S n
      (realEuclideanExistentialProjection D)
      (realEuclideanExistentialProjection A) := by
  cases tower with
  | one cover => omega
  | succ cover lower => exact lower

end CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower

/-- The compatible relative covers obtained at every successive projection
of a coherent enriched tower. -/
inductive CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower
    (C : EuclideanSetFamily) :
    (n : ℕ) → Set (RealEuclidean (n + 1)) →
      Set (RealEuclidean (n + 1)) → Type 2
  | one {D A : Set (RealEuclidean (1 + 1))}
      (projected : CharbonnelFiniteCompatibleRelativeCellCover C
        (realEuclideanExistentialProjection D)
        (realEuclideanExistentialProjection A)) :
      CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower C 1 D A
  | succ {n : ℕ}
      {D A : Set (RealEuclidean ((n + 1) + 1))}
      (projected : CharbonnelFiniteCompatibleRelativeCellCover C
        (realEuclideanExistentialProjection D)
        (realEuclideanExistentialProjection A))
      (lower : CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower C n
        (realEuclideanExistentialProjection D)
        (realEuclideanExistentialProjection A)) :
      CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower C (n + 1) D A

namespace CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower

/-- The compatible relative cover produced by the first projection. -/
def top
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower
      C n D A) :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (realEuclideanExistentialProjection D)
      (realEuclideanExistentialProjection A) := by
  cases tower with
  | one projected => exact projected
  | succ projected lower => exact projected

/-- The last cover in the tower is a relative compatible cover of the full
iterated projections in dimension one. -/
def bottom
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower
      C n D A) :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (realEuclideanIteratedExistentialProjectionToOne n D)
      (realEuclideanIteratedExistentialProjectionToOne n A) := by
  induction tower with
  | one projected => exact projected
  | succ projected lower ih => exact ih

end CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower

/-- Repeated projection coherence gives compatible relative covers at every
lower positive dimension, with no set-structure or common-refinement premise. -/
def CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower.project
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
      S n D A) :
    CharbonnelFiniteProjectionCompatibleRelativeCellCoverTower
      (charbonnelClosure S) n D A := by
  induction tower with
  | one cover => exact .one cover.project
  | succ cover lower ih => exact .succ cover.project ih

/-- In particular, a coherent enriched tower supplies a compatible relative
cover after all repeated projections down to dimension one. -/
def CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower.bottomProjectedCover
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
      S n D A) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (realEuclideanIteratedExistentialProjectionToOne n D)
      (realEuclideanIteratedExistentialProjectionToOne n A) :=
  tower.project.bottom

/-! ## Common refinement upgrades the projected covers to global covers -/

/-- Compatibility with all cells of a relative cover transfers to its target
provided the target is contained in the covered domain. -/
theorem compatible_target_of_compatible_relative_cover_cells
    {C : EuclideanSetFamily} {n : ℕ}
    {D A s : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C D A)
    (hAD : A ⊆ D)
    (hs : ∀ j,
      s ⊆ (cover.cell j).carrier ∨
        Disjoint s (cover.cell j).carrier) :
    s ⊆ A ∨ Disjoint s A := by
  classical
  by_cases hhit : ∃ x, x ∈ s ∧ x ∈ A
  · obtain ⟨x, hxs, hxA⟩ := hhit
    obtain ⟨j, hxj⟩ := cover.covers x (hAD hxA)
    rcases hs j with hsubset | hdisjoint
    · rcases cover.compatible j with htarget | htarget
      · exact Or.inl (hsubset.trans htarget)
      · exact False.elim (Set.disjoint_left.mp htarget
          (hsubset hxs) hxA)
    · exact False.elim (Set.disjoint_left.mp hdisjoint hxs hxj)
  · right
    rw [Set.disjoint_left]
    intro x hxs hxA
    exact hhit ⟨x, hxs, hxA⟩

/-- A coherent enriched cover, followed by one lower-dimensional common
refinement, gives a global compatible cover of the projected target. -/
theorem
    exists_charbonnelFiniteCompatibleCellCover_projection_of_coherentCover
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) n) :
    Nonempty (CharbonnelFiniteCompatibleCellCover (charbonnelClosure S)
      (realEuclideanExistentialProjection A)) := by
  classical
  let projected := cover.project
  let _ : Finite projected.Index := projected.indexFinite
  let _ : Fintype projected.Index := Fintype.ofFinite projected.Index
  obtain ⟨fine⟩ := hII projected.cell
  have hprojectedTarget :
      realEuclideanExistentialProjection A ⊆
        realEuclideanExistentialProjection D := by
    rintro x ⟨y, hy⟩
    exact ⟨y, cover.target_subset_domain hy⟩
  refine ⟨
    { count := fine.count
      cell := fine.cell
      covers := fine.covers
      compatible := ?_ }⟩
  intro i
  exact compatible_target_of_compatible_relative_cover_cells
    projected hprojectedTarget (fine.compatible i)

/-- Global compatible covers of every successive projected target.  The
domain indices are retained so that the lower stage still records the exact
projection relation, even though each stored cover is global. -/
inductive CharbonnelFiniteProjectionCompatibleCellCoverTower
    (C : EuclideanSetFamily) :
    (n : ℕ) → Set (RealEuclidean (n + 1)) →
      Set (RealEuclidean (n + 1)) → Type 2
  | one {D A : Set (RealEuclidean (1 + 1))}
      (projected : CharbonnelFiniteCompatibleCellCover C
        (realEuclideanExistentialProjection A)) :
      CharbonnelFiniteProjectionCompatibleCellCoverTower C 1 D A
  | succ {n : ℕ}
      {D A : Set (RealEuclidean ((n + 1) + 1))}
      (projected : CharbonnelFiniteCompatibleCellCover C
        (realEuclideanExistentialProjection A))
      (lower : CharbonnelFiniteProjectionCompatibleCellCoverTower C n
        (realEuclideanExistentialProjection D)
        (realEuclideanExistentialProjection A)) :
      CharbonnelFiniteProjectionCompatibleCellCoverTower C (n + 1) D A

namespace CharbonnelFiniteProjectionCompatibleCellCoverTower

/-- The first lower-dimensional global compatible cover. -/
def top
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCompatibleCellCoverTower C n D A) :
    CharbonnelFiniteCompatibleCellCover C
      (realEuclideanExistentialProjection A) := by
  cases tower with
  | one projected => exact projected
  | succ projected lower => exact projected

/-- The final global cover is compatible with the full iterated projection
of the original target to dimension one. -/
def bottom
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCompatibleCellCoverTower C n D A) :
    CharbonnelFiniteCompatibleCellCover C
      (realEuclideanIteratedExistentialProjectionToOne n A) := by
  induction tower with
  | one projected => exact projected
  | succ projected lower ih => exact ih

end CharbonnelFiniteProjectionCompatibleCellCoverTower

/-- Positive-dimensional common refinement upgrades every relative cover in
a coherent projection tower to a global compatible cover. -/
theorem exists_charbonnelFiniteProjectionCompatibleCellCoverTower
    {S : EuclideanSetFamily}
    (hII : ∀ {k : ℕ}, 0 < k →
      CharbonnelFiniteCellFamilyCommonRefinementAt
        (charbonnelClosure S) k)
    {n : ℕ} {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
      S n D A) :
    Nonempty (CharbonnelFiniteProjectionCompatibleCellCoverTower
      (charbonnelClosure S) n D A) := by
  induction tower with
  | one cover =>
      obtain ⟨projected⟩ :=
        exists_charbonnelFiniteCompatibleCellCover_projection_of_coherentCover
          cover (hII (by omega))
      exact ⟨.one projected⟩
  | @succ n D A cover lower ih =>
      obtain ⟨projected⟩ :=
        exists_charbonnelFiniteCompatibleCellCover_projection_of_coherentCover
          cover (hII (by omega))
      obtain ⟨lowerTower⟩ := ih
      exact ⟨.succ projected lowerTower⟩

/-- Existing closed-member covers and retained successor enrichment prove the
common-refinement input needed to globalize an entire coherent tower. -/
theorem
    exists_charbonnelFiniteProjectionCompatibleCellCoverTower_of_enrichment
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (henrich : CharbonnelPositiveDimensionalSuccessorCellEnrichment S)
    {n : ℕ} {D A : Set (RealEuclidean (n + 1))}
    (tower : CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower
      S n D A) :
    Nonempty (CharbonnelFiniteProjectionCompatibleCellCoverTower
      (charbonnelClosure S) n D A) :=
  exists_charbonnelFiniteProjectionCompatibleCellCoverTower
    (charbonnelPositiveDimensionalCellFamilyCommonRefinement_of_enrichment
      hC hI henrich) tower

/-! ## Bounded-coordinate assembly -/

/-- Repeatedly coherent bounded covers for every closed projected lift.  The
top stage is exactly the enriched relative cover needed by the bounded
complement argument; the tail retains all lower projection stages. -/
def WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty
    (S : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 0 < n →
    ∀ {B : Set (RealEuclidean ((n + 1) + q))},
      IsClosed B → B ∈ charbonnelClosure S ((n + 1) + q) →
        Nonempty
          (CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower S n
            (wilkieOpenCube (n + 1))
            (wilkieBoundedImage (realEuclideanExistentialProjection B)))

/-- A bounded coherent tower supplies the enriched top cover consumed by the
existing bounded source pipeline. -/
theorem
    wilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty_of_projectionCoherentTowers
    {S : EuclideanSetFamily}
    (htowers :
      WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty S) :
    WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty S := by
  intro n q hn B hBclosed hBmem
  obtain ⟨tower⟩ := htowers hn hBclosed hBmem
  exact ⟨tower.top.toEnrichedRelativeCellCover⟩

/-- Consequently, bounded coherent towers give the ordinary relative covers
used directly by `WilkieBoundedComplementAssembly`. -/
theorem
    wilkieBoundedProjectedClosedLiftCellCoverProperty_of_projectionCoherentTowers
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (htowers :
      WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty S) :
    WilkieBoundedProjectedClosedLiftCellCoverProperty
      (charbonnelClosure S) :=
  wilkieBoundedProjectedClosedLiftCellCoverProperty_of_enriched hC
    (wilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty_of_projectionCoherentTowers
      htowers)

/-- Source-facing bounded assembly whose remaining Section 4 datum is an
actual projection-coherent tower. -/
def CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  CharbonnelClosedBoundaryCarrierProperty G →
    WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty
      (literalZeroSetFamily G)

/-- Projection-coherent tower assembly implies the enriched bounded assembly
already used by the source endpoint. -/
theorem
    charbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly_of_projectionCoherentTowers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G) :
    CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly G := by
  intro hboundary
  exact
    wilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty_of_projectionCoherentTowers
      (htowers hboundary)

/-- Projection-coherent tower assembly reaches the exact bounded ordinary
cell-cover assembly consumed by the complement theorem. -/
theorem
    charbonnelBoundedClosedBoundaryCellCoverAssembly_of_projectionCoherentTowers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G) :
    CharbonnelBoundedClosedBoundaryCellCoverAssembly G :=
  charbonnelBoundedClosedBoundaryCellCoverAssembly_of_enrichedCells hG hsmooth
    (charbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly_of_projectionCoherentTowers
      htowers)

/-- The coherent tower assembly therefore discharges the Section 4 premise
of the bounded complement pipeline. -/
theorem
    charbonnelClosedBoundaryComplementAssembly_of_boundedProjectionCoherentTowers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G) :
    CharbonnelClosedBoundaryComplementAssembly G :=
  charbonnelClosedBoundaryComplementAssembly_of_boundedCellCovers
    hG hsmooth hUFF
      (charbonnelBoundedClosedBoundaryCellCoverAssembly_of_projectionCoherentTowers
        hG hsmooth htowers)

/-- Pointwise Abel endpoint with repeated projection coherence as the exact
remaining bounded Section 4 input. -/
theorem
    IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedProjectionCoherentTowers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (htowers :
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    OMinimal A := by
  exact hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedEnrichedCells
    hUFF hselection hanalytic
      (charbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly_of_projectionCoherentTowers
        htowers)

/-- Family-wide main-theorem reduction with the bounded Section 4 residual
stated as projection-coherent enriched towers. -/
theorem
    mainTheorem_of_charbonnelSourceSteps_automaticProjection_and_boundedProjectionCoherentTowers
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
    (htowers : ∀ (A : ℝ → ℝ), IsAbel A →
      CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly
        (abelGeometricFamily A)) :
    MainTheorem := by
  intro A hA
  refine ⟨?_, hA.exponentialDefinable,
    hA.positiveInverseDefinable, hA.isTransexponential⟩
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedProjectionCoherentTowers
      (hUFF A hA) (hselection A hA) (hanalytic A hA) (htowers A hA)

end AbelFormalization
