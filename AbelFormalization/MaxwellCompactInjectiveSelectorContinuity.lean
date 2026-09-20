import AbelFormalization.Wilkie28WeakSelectionCompactComponentReduction

/-!
# Continuity of compact single-valued Maxwell selectors

On a compact relation whose visible projection is injective, projection onto
the visible coordinate is a homeomorphism onto its image.  Consequently the
choice selector used by the weak-selection reduction is continuous on that
image.  Any graph contained in the same compact relation agrees with this
selector and is continuous as well.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The scalar form of the visible projection of a one-parameter relation. -/
def maxwellScalarProjection {n : ℕ}
    (P : Set (RealEuclidean (1 + n))) : Set ℝ :=
  {t | (fun _ : Fin 1 ↦ t) ∈ realEuclideanExistentialProjection P}

/-- An injective one-parameter relation is set-theoretically equivalent to
its scalar visible projection. -/
noncomputable def maxwellProjectionEquiv
    {n : ℕ} (P : Set (RealEuclidean (1 + n)))
    (hinjective : Set.InjOn realEuclideanTakeLeft P) :
    P ≃ maxwellScalarProjection P where
  toFun z := ⟨realEuclideanTakeLeft (z : RealEuclidean (1 + n)) 0, by
    change (fun _ : Fin 1 ↦
      realEuclideanTakeLeft (z : RealEuclidean (1 + n)) 0) ∈
        realEuclideanExistentialProjection P
    refine ⟨realEuclideanTakeRight (z : RealEuclidean (1 + n)), ?_⟩
    have hvis : (fun _ : Fin 1 ↦
        realEuclideanTakeLeft (z : RealEuclidean (1 + n)) 0) =
        realEuclideanTakeLeft (z : RealEuclidean (1 + n)) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    rw [hvis, realEuclideanAppend_takeLeft_takeRight]
    exact z.property⟩
  invFun t :=
    ⟨realEuclideanAppend (fun _ : Fin 1 ↦ (t : ℝ))
        (maxwellOneParameterSelector P t),
      maxwell_append_oneParameterSelector_mem t.property⟩
  left_inv z := by
    apply Subtype.ext
    apply hinjective
    · apply maxwell_append_oneParameterSelector_mem
      change (fun _ : Fin 1 ↦
        realEuclideanTakeLeft (z : RealEuclidean (1 + n)) 0) ∈
          realEuclideanExistentialProjection P
      refine ⟨realEuclideanTakeRight (z : RealEuclidean (1 + n)), ?_⟩
      have hvis : (fun _ : Fin 1 ↦
          realEuclideanTakeLeft (z : RealEuclidean (1 + n)) 0) =
          realEuclideanTakeLeft (z : RealEuclidean (1 + n)) := by
        funext i
        exact Fin.eq_zero i ▸ rfl
      rw [hvis, realEuclideanAppend_takeLeft_takeRight]
      exact z.property
    · exact z.property
    simp only [realEuclideanTakeLeft_append]
    funext i
    exact Fin.eq_zero i ▸ rfl
  right_inv t := by
    apply Subtype.ext
    simp only [realEuclideanTakeLeft_append]

/-- For a compact injective relation, the preceding equivalence is a
homeomorphism. -/
noncomputable def maxwellProjectionHomeomorph
    {n : ℕ} {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hinjective : Set.InjOn realEuclideanTakeLeft P) :
    P ≃ₜ maxwellScalarProjection P := by
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hPcompact
  apply Continuous.homeoOfEquivCompactToT2
    (f := maxwellProjectionEquiv P hinjective)
  apply Continuous.subtype_mk
  change Continuous (fun z : P ↦
    (z : RealEuclidean (1 + n)) (Fin.castAdd n (0 : Fin 1)))
  exact (continuous_apply _).comp continuous_subtype_val

/-- The canonical choice selector is continuous on the scalar projection of
a compact relation with injective visible projection. -/
theorem continuousOn_maxwellOneParameterSelector_of_compact_of_injective
    {n : ℕ} {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hinjective : Set.InjOn realEuclideanTakeLeft P) :
    ContinuousOn (maxwellOneParameterSelector P)
      (maxwellScalarProjection P) := by
  rw [continuousOn_iff_continuous_domRestrict]
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hPcompact
  let e : P ≃ maxwellScalarProjection P :=
    maxwellProjectionEquiv P hinjective
  have heContinuous : Continuous (e : P → maxwellScalarProjection P) := by
    apply Continuous.subtype_mk
    change Continuous (fun z : P ↦
      (z : RealEuclidean (1 + n)) (Fin.castAdd n (0 : Fin 1)))
    exact (continuous_apply _).comp continuous_subtype_val
  have heSymmContinuous : Continuous
      (e.symm : maxwellScalarProjection P → P) :=
    heContinuous.continuous_symm_of_equiv_compact_to_t2
  have hcontinuous : Continuous (fun t : maxwellScalarProjection P ↦
      realEuclideanTakeRight
        ((e.symm t : P) : RealEuclidean (1 + n))) := by
    apply continuous_pi
    intro i
    change Continuous (fun t : maxwellScalarProjection P ↦
      ((e.symm t : P) : RealEuclidean (1 + n)) (Fin.natAdd 1 i))
    exact (continuous_apply _).comp
      (continuous_subtype_val.comp heSymmContinuous)
  convert hcontinuous using 1
  funext t
  change maxwellOneParameterSelector P (t : ℝ) =
    realEuclideanTakeRight
      (realEuclideanAppend (fun _ : Fin 1 ↦ (t : ℝ))
        (maxwellOneParameterSelector P t))
  exact (realEuclideanTakeRight_append
    (fun _ : Fin 1 ↦ (t : ℝ)) (maxwellOneParameterSelector P t)).symm

/-- Any selected graph contained in the compact injective relation agrees
with the canonical inverse of projection, and is therefore continuous on its
domain. -/
theorem continuousOn_of_selectedWitnessGraph_subset_compact_injective
    {n : ℕ} {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hinjective : Set.InjOn realEuclideanTakeLeft P)
    {U : Set ℝ} {phi : ℝ → RealEuclidean n}
    (hgraphSubset : wilkie28SelectedWitnessGraph U phi ⊆ P) :
    ContinuousOn phi U := by
  have hUsubset : U ⊆ maxwellScalarProjection P := by
    intro t ht
    change (fun _ : Fin 1 ↦ t) ∈ realEuclideanExistentialProjection P
    exact ⟨phi t, hgraphSubset ⟨t, ht, rfl⟩⟩
  have hcanonical :=
    (continuousOn_maxwellOneParameterSelector_of_compact_of_injective
      hPcompact hinjective).mono hUsubset
  apply hcanonical.congr
  intro t ht
  have hphiP :
      realEuclideanAppend (fun _ : Fin 1 ↦ t) (phi t) ∈ P :=
    hgraphSubset ⟨t, ht, rfl⟩
  have hcanonicalP :
      realEuclideanAppend (fun _ : Fin 1 ↦ t)
        (maxwellOneParameterSelector P t) ∈ P :=
    maxwell_append_oneParameterSelector_mem (hUsubset ht)
  have happendEq := hinjective hcanonicalP hphiP (by simp)
  have hright := congrArg realEuclideanTakeRight happendEq
  simpa only [realEuclideanTakeRight_append] using hright.symm

end AbelFormalization
