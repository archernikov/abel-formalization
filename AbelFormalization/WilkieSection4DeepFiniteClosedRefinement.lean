import AbelFormalization.WilkieSection4DeepSimultaneousInduction

/-!
# Finite simultaneous refinement of relatively closed targets

The two halves of Wilkie's retained lower-dimensional induction combine into
one partition of a deep domain compatible with any finite family of relatively
closed Charbonnel targets.  Each target is first decomposed separately; the
common-refinement half is then applied to all cells in all those decompositions.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

private theorem compatible_target_of_refining_deep_cover
    {S : EuclideanSetFamily} {n : ℕ}
    {D A s : Set (RealEuclidean (n + 1))}
    (cover :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D (fun _ : Unit ↦ A))
    (hsD : s ⊆ D)
    (hs : ∀ k,
      s ⊆ (cover.cell k).carrier ∨
        Disjoint s (cover.cell k).carrier) :
    s ⊆ A ∨ Disjoint s A := by
  by_cases hsNonempty : s.Nonempty
  · obtain ⟨x, hxs⟩ := hsNonempty
    obtain ⟨k, hxk⟩ := cover.covers x (hsD hxs)
    rcases hs k with hsubset | hdisjoint
    · rcases cover.compatible k () with htarget | htarget
      · exact Or.inl (hsubset.trans htarget)
      · exact Or.inr (htarget.mono hsubset Subset.rfl)
    · exact (Set.disjoint_left.mp hdisjoint hxs hxk).elim
  · left
    intro x hx
    exact (hsNonempty ⟨x, hx⟩).elim

/-- Lower-dimensional relative closed decomposition and common refinement give
one retained partition compatible with a finite family of relatively closed
targets in the same deep domain. -/
theorem exists_charbonnelFinitePartitionedDeepSimultaneousClosedRefinement
    {S : EuclideanSetFamily} {n : ℕ}
    (hI : CharbonnelDeepRelativeClosedDecompositionAt S n)
    (hII : CharbonnelDeepRelativeCommonRefinementAt S n)
    (D : CharbonnelDeepEnrichedCell S (n + 1))
    {J : Type} [Fintype J]
    (target : J → Set (RealEuclidean (n + 1)))
    (htargetSub : ∀ j, target j ⊆ D.carrier)
    (htargetMem : ∀ j, target j ∈ charbonnelClosure S (n + 1))
    (htargetClosed : ∀ j,
      IsClosed (Subtype.val ⁻¹' target j : Set D.carrier)) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier target) := by
  classical
  have hindividual : ∀ j,
      Nonempty
        (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
          S D.carrier (fun _ : Unit ↦ target j)) := by
    intro j
    exact hI D (htargetSub j) (htargetMem j) (htargetClosed j)
  let individual : (j : J) →
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier (fun _ : Unit ↦ target j) :=
    fun j ↦ Classical.choice (hindividual j)
  letI : ∀ j, Finite (individual j).Index :=
    fun j ↦ (individual j).indexFinite
  let Input := Σ j : J, (individual j).Index
  letI : Fintype Input := Fintype.ofFinite Input
  let input : Input → CharbonnelDeepEnrichedCell S (n + 1) :=
    fun q ↦ (individual q.1).cell q.2
  obtain ⟨fine⟩ := hII D input
  refine ⟨
    { Index := fine.Index
      indexFinite := fine.indexFinite
      cell := fine.cell
      contained := fine.contained
      covers := fine.covers
      compatible := ?_
      cells_eq_or_disjoint := fine.cells_eq_or_disjoint
      hereditary_projection_coherent :=
        fine.hereditary_projection_coherent }⟩
  intro i j
  apply compatible_target_of_refining_deep_cover
    (cover := individual j) (fine.contained i)
  intro k
  have hcompat := fine.compatible i (⟨j, k⟩ : Input)
  simpa only [input] using hcompat

/-- Bounded-domain form of the finite closed-target refinement used in
Wilkie's actual Section 4 induction. -/
theorem exists_charbonnelFinitePartitionedBoundedDeepSimultaneousClosedRefinement
    {S : EuclideanSetFamily} {n : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S n)
    (D : CharbonnelDeepEnrichedCell S (n + 1))
    (hDbounded : Bornology.IsBounded D.carrier)
    {J : Type} [Fintype J]
    (target : J → Set (RealEuclidean (n + 1)))
    (htargetSub : ∀ j, target j ⊆ D.carrier)
    (htargetMem : ∀ j, target j ∈ charbonnelClosure S (n + 1))
    (htargetClosed : ∀ j,
      IsClosed (Subtype.val ⁻¹' target j : Set D.carrier)) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier target) := by
  classical
  have hindividual : ∀ j,
      Nonempty
        (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
          S D.carrier (fun _ : Unit ↦ target j)) := by
    intro j
    exact hI D hDbounded (htargetSub j) (htargetMem j) (htargetClosed j)
  let individual : (j : J) →
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier (fun _ : Unit ↦ target j) :=
    fun j ↦ Classical.choice (hindividual j)
  letI : ∀ j, Finite (individual j).Index :=
    fun j ↦ (individual j).indexFinite
  let Input := Σ j : J, (individual j).Index
  letI : Fintype Input := Fintype.ofFinite Input
  let input : Input → CharbonnelDeepEnrichedCell S (n + 1) :=
    fun q ↦ (individual q.1).cell q.2
  obtain ⟨fine⟩ := hII D hDbounded input
  refine ⟨
    { Index := fine.Index
      indexFinite := fine.indexFinite
      cell := fine.cell
      contained := fine.contained
      covers := fine.covers
      compatible := ?_
      cells_eq_or_disjoint := fine.cells_eq_or_disjoint
      hereditary_projection_coherent :=
        fine.hereditary_projection_coherent }⟩
  intro i j
  apply compatible_target_of_refining_deep_cover
    (cover := individual j) (fine.contained i)
  intro k
  have hcompat := fine.compatible i (⟨j, k⟩ : Input)
  simpa only [input] using hcompat

end AbelFormalization
