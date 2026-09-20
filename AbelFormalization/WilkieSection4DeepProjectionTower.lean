import AbelFormalization.WilkieSection4DeepCoverCore
import AbelFormalization.WilkieProjectionCoherentCellCoverTower

/-!
# A single hereditary Section 4 cover generates the projection tower

Wilkie's projection induction does not choose unrelated decompositions after
each projection.  A cell retains its projected cell, and that projected cell
retains its own projected cell.  This file states that source-shaped datum and
proves that one finite hereditary cover generates the complete
`CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower` already consumed
by the complement pipeline.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelFiniteDeepProjectionCoherentCellCover

/-- The top layer of a hereditary deep cover is an ordinary one-step
projection-coherent enriched cover. -/
def toProjectionCoherentEnrichedCellCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteDeepProjectionCoherentCellCover S D A) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell i := (cover.cell i).toEnrichedSuccessorCell hC hn
  target_subset_domain := cover.target_subset_domain
  contained := by
    intro i
    rw [(cover.cell i).toEnrichedSuccessorCell_carrier hC hn]
    exact cover.contained i
  covers := by
    intro z hz
    obtain ⟨i, hi⟩ := cover.covers z hz
    exact ⟨i, by
      rwa [(cover.cell i).toEnrichedSuccessorCell_carrier hC hn]⟩
  compatible := by
    intro i
    simpa only [(cover.cell i).toEnrichedSuccessorCell_carrier hC hn] using
      cover.compatible i
  bases_eq_or_disjoint := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    intro i j
    simpa only [CharbonnelDeepEnrichedCell.toEnrichedSuccessorCell_base_carrier]
      using cover.hereditary_projection_coherent.1 i j

/-- Project a hereditary deep cover by one coordinate.  All cover and target
compatibility fields follow from the one-step coherent cover; hereditary
coherence supplies the tail condition. -/
def project
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    {D A : Set (RealEuclidean ((n + 1) + 1))}
    (cover : CharbonnelFiniteDeepProjectionCoherentCellCover S D A) :
    CharbonnelFiniteDeepProjectionCoherentCellCover S
      (realEuclideanExistentialProjection D)
      (realEuclideanExistentialProjection A) := by
  let hn : 0 < n + 1 := by omega
  let shallow := cover.toProjectionCoherentEnrichedCellCover hC hn
  let projected := shallow.project
  have hbaseCarrier (i : cover.Index) :
      (projected.cell i).carrier =
        ((cover.cell i).projectedBase hn).carrier := by
    change ((cover.cell i).toEnrichedSuccessorCell hC hn).base.carrier = _
    exact (cover.cell i).toEnrichedSuccessorCell_base_carrier hC hn
  exact
    { Index := cover.Index
      indexFinite := cover.indexFinite
      cell := fun i ↦ (cover.cell i).projectedBase hn
      target_subset_domain := by
        rintro x ⟨y, hy⟩
        exact ⟨y, cover.target_subset_domain hy⟩
      contained := by
        intro i
        rw [← hbaseCarrier i]
        exact projected.contained i
      covers := by
        intro x hx
        obtain ⟨i, hi⟩ := projected.covers x hx
        exact ⟨i, by rwa [← hbaseCarrier i]⟩
      compatible := by
        intro i
        rw [← hbaseCarrier i]
        exact projected.compatible i
      hereditary_projection_coherent :=
        cover.hereditary_projection_coherent.2 }

/-- A single hereditary deep cover generates the complete coherent tower of
all its successive existential projections. -/
def toProjectionCoherentEnrichedCellCoverTower
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S)) :
    {n : ℕ} → (hn : 0 < n) →
    {D A : Set (RealEuclidean (n + 1))} →
    CharbonnelFiniteDeepProjectionCoherentCellCover S D A →
      CharbonnelFiniteProjectionCoherentEnrichedCellCoverTower S n D A
  | 0, hn, _, _, _ => False.elim (by omega)
  | 1, _hn, _, _, cover =>
      .one (cover.toProjectionCoherentEnrichedCellCover hC (by omega))
  | n + 2, _hn, _, _, cover =>
      .succ (cover.toProjectionCoherentEnrichedCellCover hC (by omega))
        ((cover.project hC).toProjectionCoherentEnrichedCellCoverTower
          hC (by omega))
termination_by n => n

end CharbonnelFiniteDeepProjectionCoherentCellCover

/-! ## Source-facing bounded reduction -/

/-- The source-shaped Section 4 output: one hereditary recursively enriched
cover of each bounded projected closed lift. -/
def WilkieBoundedDeepProjectionCoherentCellCoverProperty
    (S : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 0 < n →
    ∀ {B : Set (RealEuclidean ((n + 1) + q))},
      IsClosed B → B ∈ charbonnelClosure S ((n + 1) + q) →
        Nonempty
          (CharbonnelFiniteDeepProjectionCoherentCellCover S
            (wilkieOpenCube (n + 1))
            (wilkieBoundedImage (realEuclideanExistentialProjection B)))

/-- One hereditary Section 4 cover is sufficient for the tower premise used
by the complement pipeline. -/
theorem
    wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_deep
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hdeep : WilkieBoundedDeepProjectionCoherentCellCoverProperty S) :
    WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty S := by
  intro n q hn B hBclosed hBmem
  obtain ⟨cover⟩ := hdeep hn hBclosed hBmem
  exact ⟨cover.toProjectionCoherentEnrichedCellCoverTower hC hn⟩

end AbelFormalization
