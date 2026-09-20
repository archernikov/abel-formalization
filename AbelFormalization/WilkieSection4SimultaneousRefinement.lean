import AbelFormalization.CharbonnelBoundarySelectorAssembly

/-!
# Wilkie Section 4: simultaneous refinement of finitely many covers

Wilkie derives the simultaneous form of `(I)ₙ` from `(I)ₙ` and `(II)ₙ`.
For each closed target, `(I)ₙ` supplies a compatible cell decomposition;
then `(II)ₙ` supplies one cell decomposition compatible with every cell in
all of those decompositions.

The existing `CharbonnelFiniteCompatibleCellCover` deliberately records only
the data needed by the complement argument: finite recursive cells, coverage,
and compatibility with one target.  In particular, it has no common-refinement
operation.  This file isolates the exact extra property needed from `(II)ₙ`
and proves that it upgrades individual compatible covers to one cover
simultaneously compatible with a finite family of targets.

No disjointness of the individual covers is needed for this transfer.  The
essential observation is that a nonempty new cell compatible with every cell
of an old cover is contained in an old cell, because the old cells cover the
whole space.  It therefore inherits compatibility with the old target.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite recursive-cell cover of the whole coordinate space which is
compatible with every target in an indexed family. -/
structure CharbonnelFiniteSimultaneouslyCompatibleCellCover
    (C : EuclideanSetFamily) {n : ℕ} {ι : Type}
    (target : ι → Set (RealEuclidean n)) where
  count : ℕ
  cell : Fin count → CharbonnelCell C n
  covers : ∀ x : RealEuclidean n, ∃ i, x ∈ (cell i).carrier
  compatible : ∀ i j,
    (cell i).carrier ⊆ target j ∨ Disjoint (cell i).carrier (target j)

namespace CharbonnelFiniteSimultaneouslyCompatibleCellCover

/-- Forget all but one target of a simultaneous cover. -/
def targetCover
    {C : EuclideanSetFamily} {n : ℕ} {ι : Type}
    {target : ι → Set (RealEuclidean n)}
    (cover : CharbonnelFiniteSimultaneouslyCompatibleCellCover C target)
    (j : ι) : CharbonnelFiniteCompatibleCellCover C (target j) :=
  { count := cover.count
    cell := cover.cell
    covers := cover.covers
    compatible := fun i ↦ cover.compatible i j }

end CharbonnelFiniteSimultaneouslyCompatibleCellCover

/-- The finite-family consequence of Wilkie's `(II)ₙ` needed for the first
simultaneous refinement on page 418: every finite family of already-built
recursive cells admits one finite recursive-cell cover compatible with all
their carriers.

This is deliberately a separate premise.  Pairwise intersections of the
input carriers give a set-theoretic refinement, but an intersection of two
`CharbonnelCellShape`s is not supplied with a `CharbonnelCellShape` by the
current API. -/
def CharbonnelFiniteCellFamilyCommonRefinementProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ} {ι : Type} [Fintype ι],
    ∀ cells : ι → CharbonnelCell C n,
      Nonempty
        (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
          (fun i ↦ (cells i).carrier))

/-- The precise special case of Wilkie's `(II)ₙ` used to derive simultaneous
`(I)ₙ`: given finitely many compatible covers of the same ambient space,
produce one cover compatible with every cell occurring in every old cover.

Unlike the conclusion below, this premise mentions only compatibility with
the *old cells*, not compatibility with their targets. -/
def CharbonnelFiniteCompatibleCoverCommonRefinementProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n r : ℕ} {target : Fin r → Set (RealEuclidean n)},
    ∀ cover : (j : Fin r) →
        CharbonnelFiniteCompatibleCellCover C (target j),
      Nonempty
        (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
          (fun q : Σ j : Fin r, Fin (cover j).count ↦
            ((cover q.1).cell q.2).carrier))

/-- The stronger arbitrary-cell formulation implies the exact cover-indexed
common-refinement property. -/
theorem finiteCompatibleCoverCommonRefinement_of_cellFamily
    {C : EuclideanSetFamily}
    (hrefine : CharbonnelFiniteCellFamilyCommonRefinementProperty C) :
    CharbonnelFiniteCompatibleCoverCommonRefinementProperty C := by
  intro n r target cover
  let cells : (Σ j : Fin r, Fin (cover j).count) → CharbonnelCell C n :=
    fun q ↦ (cover q.1).cell q.2
  exact hrefine cells

/-- Compatibility with every cell of a covering transfers compatibility with
the target of that covering.  This is the set-theoretic core of the passage
from `(I)ₙ + (II)ₙ` to simultaneous `(I)ₙ`. -/
theorem compatible_target_of_compatible_cover_cells
    {C : EuclideanSetFamily} {n : ℕ}
    {A s : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleCellCover C A)
    (hs : ∀ j,
      s ⊆ (cover.cell j).carrier ∨ Disjoint s (cover.cell j).carrier) :
    s ⊆ A ∨ Disjoint s A := by
  by_cases hsNonempty : s.Nonempty
  · obtain ⟨x, hxs⟩ := hsNonempty
    obtain ⟨j, hxj⟩ := cover.covers x
    rcases hs j with hsubset | hdisjoint
    · rcases cover.compatible j with htarget | htarget
      · exact Or.inl (hsubset.trans htarget)
      · exact Or.inr (htarget.mono hsubset Subset.rfl)
    · exact (Set.disjoint_left.mp hdisjoint hxs hxj).elim
  · left
    intro x hx
    exact (hsNonempty ⟨x, hx⟩).elim

/-- Individual finite compatible covers together with the finite common-cell
refinement property produce one finite cover simultaneously compatible with
all targets. -/
theorem finiteSimultaneouslyCompatibleCellCover_of_individual
    {C : EuclideanSetFamily}
    (hrefine : CharbonnelFiniteCompatibleCoverCommonRefinementProperty C)
    {n r : ℕ} (target : Fin r → Set (RealEuclidean n))
    (hcover : ∀ j,
      Nonempty (CharbonnelFiniteCompatibleCellCover C (target j))) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C target) := by
  classical
  let cover : ∀ j,
      CharbonnelFiniteCompatibleCellCover C (target j) :=
    fun j ↦ Classical.choice (hcover j)
  obtain ⟨fine⟩ := hrefine cover
  refine ⟨
    { count := fine.count
      cell := fine.cell
      covers := fine.covers
      compatible := ?_ }⟩
  intro i j
  apply compatible_target_of_compatible_cover_cells (cover := cover j)
  intro k
  exact fine.compatible i ⟨j, k⟩

/-- Source-facing closed-set form.  In dimensions above one, the existing
closed-member compatible-cover property is Wilkie's `(I)ₙ`; the separate
common-refinement property is the finite-family fragment of `(II)ₙ`.  Together
they give one cover simultaneously compatible with any finite family of
closed family members. -/
theorem finiteSimultaneouslyCompatibleCellCover_of_closedMembers
    {C : EuclideanSetFamily}
    (hI : CharbonnelHigherDimensionalClosedMemberCellCoverProperty C)
    (hII : CharbonnelFiniteCompatibleCoverCommonRefinementProperty C)
    {n r : ℕ} (hn : 1 < n)
    (target : Fin r → Set (RealEuclidean n))
    (hclosed : ∀ j, IsClosed (target j))
    (hmem : ∀ j, target j ∈ C n) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C target) := by
  apply finiteSimultaneouslyCompatibleCellCover_of_individual hII target
  intro j
  exact hI hn (hclosed j) (hmem j)

end AbelFormalization
