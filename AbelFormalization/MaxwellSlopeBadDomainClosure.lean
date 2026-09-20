import AbelFormalization.MaxwellResidualOneSidedClusterData

/-!
# Domain control for Maxwell's slope-bad locus

The zero-step trace may acquire fibers over boundary points of the open
domain.  This file proves that it acquires no fibers farther away: its
domain, and hence every finite or infinite slope-bad base, lies in the
closure of the original domain.  Inside the domain, the residual
one-sided classification is now unconditional.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Every base point of the closed zero-step quotient trace lies in the
closure of the original domain. -/
theorem maxwellDifferenceQuotientZeroTrace_domain_subset_closure
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellRelationDomain (maxwellDifferenceQuotientZeroTrace U R i) ⊆
      closure U := by
  rintro x ⟨y, hy⟩
  have hyClosure :=
    (realEuclideanAppend_mem_maxwellDifferenceQuotientZeroTrace_iff
      U R i x y).mp hy
  obtain ⟨w, hw, hwLimit⟩ := mem_closure_iff_seq_limit.mp hyClosure
  let xseq : ℕ → RealEuclidean p := fun n ↦
    realEuclideanTakeLeft (realEuclideanTakeLeft (w n))
  have hxseqU : ∀ n, xseq n ∈ U := by
    intro n
    have hn := hw n
    let epsilon : ℕ → ℝ := fun k ↦
      realEuclideanTakeRight (realEuclideanTakeLeft (w k)) 0
    let value : ℕ → ℝ := fun k ↦ realEuclideanTakeRight (w k) 0
    have hwSplit : w n =
        realEuclideanAppend
          (realEuclideanAppend (xseq n)
            (fun _ : Fin 1 ↦ epsilon n))
          (fun _ : Fin 1 ↦ value n) := by
      calc
        w n = realEuclideanAppend
            (realEuclideanTakeLeft (w n))
            (realEuclideanTakeRight (w n)) :=
          (realEuclideanAppend_takeLeft_takeRight (w n)).symm
        _ = realEuclideanAppend
            (realEuclideanAppend
              (realEuclideanTakeLeft (realEuclideanTakeLeft (w n)))
              (realEuclideanTakeRight (realEuclideanTakeLeft (w n))))
            (realEuclideanTakeRight (w n)) := by
          congr 1
          exact
            (realEuclideanAppend_takeLeft_takeRight
              (realEuclideanTakeLeft (w n))).symm
        _ = realEuclideanAppend
            (realEuclideanAppend (xseq n)
              (fun _ : Fin 1 ↦ epsilon n))
            (fun _ : Fin 1 ↦ value n) := by
          congr 1
          · congr 1
            funext j
            have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
            subst j
            rfl
          · funext j
            have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
            subst j
            rfl
    rw [hwSplit,
      realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff]
      at hn
    exact hn.1
  have hxseqLimit : Tendsto xseq atTop (nhds x) := by
    let outer : RealEuclidean ((p + 1) + 1) →L[ℝ]
        RealEuclidean (p + 1) :=
      (realEuclideanTakeLeftLinearMap (p + 1) 1).toContinuousLinearMap
    let inner : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
      (realEuclideanTakeLeftLinearMap p 1).toContinuousLinearMap
    have houter := (outer.continuous.tendsto _).comp hwLimit
    have hinner := (inner.continuous.tendsto _).comp houter
    simpa [outer, inner, xseq, Function.comp_def] using hinner
  exact mem_closure_iff_seq_limit.mpr ⟨xseq, hxseqU, hxseqLimit⟩

/-- Reciprocal infinity bases cannot leave a closed set containing the
domain of the underlying finite relation. -/
theorem maxwellPositiveInfinityBase_subset_of_domain_subset_closed
    {p : ℕ} {G : MaxwellRelation p 1} {C : Set (RealEuclidean p)}
    (hC : IsClosed C) (hdom : maxwellRelationDomain G ⊆ C) :
    maxwellPositiveInfinityBase G ⊆ C := by
  intro x hx
  let L : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
    (realEuclideanTakeLeftLinearMap p 1).toContinuousLinearMap
  have hsub : maxwellPositiveReciprocalRelation G ⊆ L ⁻¹' C := by
    intro w hw
    rcases hw with ⟨y, hy, _hyr, _hr⟩
    exact hdom ⟨fun _ : Fin 1 ↦ y, hy⟩
  have hclosed : IsClosed (L ⁻¹' C) := hC.preimage L.continuous
  have hpoint : realEuclideanAppend x (0 : RealEuclidean 1) ∈ L ⁻¹' C :=
    closure_minimal hsub hclosed hx
  simpa [L] using hpoint

theorem maxwellNegativeInfinityBase_subset_of_domain_subset_closed
    {p : ℕ} {G : MaxwellRelation p 1} {C : Set (RealEuclidean p)}
    (hC : IsClosed C) (hdom : maxwellRelationDomain G ⊆ C) :
    maxwellNegativeInfinityBase G ⊆ C := by
  intro x hx
  let L : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
    (realEuclideanTakeLeftLinearMap p 1).toContinuousLinearMap
  have hsub : maxwellNegativeReciprocalRelation G ⊆ L ⁻¹' C := by
    intro w hw
    rcases hw with ⟨y, hy, _hyr, _hr⟩
    exact hdom ⟨fun _ : Fin 1 ↦ y, hy⟩
  have hclosed : IsClosed (L ⁻¹' C) := hC.preimage L.continuous
  have hpoint : realEuclideanAppend x (0 : RealEuclidean 1) ∈ L ⁻¹' C :=
    closure_minimal hsub hclosed hx
  simpa [L] using hpoint

/-- All three pieces of the coordinate slope-bad locus are based in
`closure U`. -/
theorem maxwellCoordinateSlopeBadLocus_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellCoordinateSlopeBadLocus U R i ⊆ closure U := by
  let G := maxwellDifferenceQuotientZeroTrace U R i
  have hdom : maxwellRelationDomain G ⊆ closure U :=
    maxwellDifferenceQuotientZeroTrace_domain_subset_closure U R i
  intro x hx
  simp only [maxwellCoordinateSlopeBadLocus, Set.mem_union] at hx
  rcases hx with hinfinity | hfinite
  · rcases hinfinity with hpositive | hnegative
    · exact maxwellPositiveInfinityBase_subset_of_domain_subset_closed
        isClosed_closure hdom hpositive
    · exact maxwellNegativeInfinityBase_subset_of_domain_subset_closed
        isClosed_closure hdom hnegative
  · exact hdom (maxwellMultivaluedLocus_subset_domain G hfinite)

/-- The two one-sided bad loci and the three hard cases cover the slope-bad
locus at every point of the actual open domain, with no residual
cluster-classification premise. -/
theorem maxwellCoordinateSlopeBadLocus_inter_domain_subset_oneSidedBad_union_threeHard
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) :
    maxwellCoordinateSlopeBadLocus U R i ∩ U ⊆
      (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
        maxwellNegativeStepExtendedMultivaluedLocus U R i) ∪
      maxwellThreeHardSlopeCasesLocus U R i := by
  intro x hx
  by_cases hpositive :
      x ∈ maxwellPositiveStepExtendedMultivaluedLocus U R i
  · exact Or.inl (Or.inl hpositive)
  by_cases hnegative :
      x ∈ maxwellNegativeStepExtendedMultivaluedLocus U R i
  · exact Or.inl (Or.inr hnegative)
  apply Or.inr
  have hdata :=
    hR.nondifferentiableOneSidedClusterData_residual_inter hU i
  apply hdata.subset_threeHardCases
  have hnot : x ∉
      maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
        maxwellNegativeStepExtendedMultivaluedLocus U R i := by
    simpa only [Set.mem_union, not_or] using
      (And.intro hpositive hnegative)
  exact ⟨⟨hx.1, hnot⟩, hx.2⟩

end AbelFormalization
