import AbelFormalization.CharbonnelSection57OpenLocalizationRelativeBridge

/-!
# Converting relative stability on an open base to ambient stability

Section 5.7 starts inside an open part of the positive zero trace.  On such
an open base, a sufficiently small relative ball is an ordinary closed ball.
This file converts the relative stable-interval output of Section 5.3 into
the ambient witness used by the Section 5.7 graph extraction.

The conversion also removes the artificial full-space base from the earlier
bridge: strict refinement is needed only on the prescribed open trace region,
where full vertical projection is available.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Functoriality of the component inclusion map -/

/-- Inclusion of vertical-image components is functorial under a chain of
base inclusions. -/
theorem charbonnelVerticalComponentInclusionMap_trans
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    {A B C : Set (RealEuclidean n)}
    (hAB : A ⊆ B) (hBC : B ⊆ C) :
    charbonnelVerticalComponentInclusionMap S (hAB.trans hBC) =
      charbonnelVerticalComponentInclusionMap S hBC ∘
        charbonnelVerticalComponentInclusionMap S hAB := by
  funext c
  rw [← connectedComponentRepresentative_mk
    (charbonnelVerticalImageOver S A) c]
  simp only [charbonnelVerticalComponentInclusionMap_mk]
  apply congrArg ConnectedComponents.mk
  apply Subtype.ext
  rfl

/-- Bijectivity of a component inclusion map is unchanged when its source
and target base sets are replaced by equal sets. -/
theorem charbonnelVerticalComponentInclusionMap_bijective_congr
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    {A B A' B' : Set (RealEuclidean n)}
    (hAB : A ⊆ B) (hA'B' : A' ⊆ B')
    (hA : A = A') (hB : B = B')
    (hbijective : Function.Bijective
      (charbonnelVerticalComponentInclusionMap S hAB)) :
    Function.Bijective
      (charbonnelVerticalComponentInclusionMap S hA'B') := by
  subst A'
  subst B'
  exact hbijective

/-! ## Shrinking an open-base relative witness -/

/-- Relative stable interval separation on an open base contains an ordinary
ambient stable witness whose inner ball remains in that base. -/
theorem
    exists_stableLocalVerticalIntervalWitness_inside_open_of_relativeSeparation
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U)
    (hstable : CharbonnelRelativeStableLocalVerticalIntervalSeparation U S) :
    ∃ w : CharbonnelStableLocalVerticalIntervalWitness S,
      w.innerBall ⊆ U := by
  obtain ⟨candidate, hcandidate⟩ := hstable
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hUopen candidate.center candidate.center_mem
  let ρ : ℝ := min (candidate.radius / 2) (ε / 2)
  have hρ : 0 < ρ := lt_min (half_pos candidate.radius_pos) (half_pos hε)
  have hρradius : ρ ≤ candidate.radius := by
    exact (min_le_left _ _).trans (by linarith [candidate.radius_pos])
  have hρepsilon : ρ < ε :=
    (min_le_right _ _).trans_lt (half_lt_self hε)
  have hclosedU : Metric.closedBall candidate.center ρ ⊆ U :=
    (Metric.closedBall_subset_ball hρepsilon).trans hball
  have hrelativeρ : charbonnelRelativeClosedBall U candidate.center ρ =
      Metric.closedBall candidate.center ρ := by
    rw [charbonnelRelativeClosedBall, Set.inter_eq_right]
    exact hclosedU
  have hρsub : charbonnelRelativeClosedBall U candidate.center ρ ⊆
      charbonnelRelativeClosedBall U candidate.center candidate.radius := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    exact Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp hy.2).trans hρradius)
  have hmid := hcandidate candidate.center candidate.center_mem ρ hρ hρsub
  have hmidCount : charbonnelLocalVerticalComponentCount S
      candidate.center ρ = (candidate.count : ℕ∞) := by
    change ENat.card (ConnectedComponents
      (charbonnelVerticalImageOver S
        (Metric.closedBall candidate.center ρ) : Set ℝ)) =
          (candidate.count : ℕ∞)
    rw [← hrelativeρ]
    exact hmid.1
  obtain ⟨label⟩ :=
    exists_fin_equiv_connectedComponents_of_enatCard_eq hmidCount
  let w : CharbonnelStableLocalVerticalIntervalWitness S := {
    count := candidate.count
    center := candidate.center
    radius := ρ
    radius_pos := hρ
    label := label
    stable := by
      intro y s hs hsub
      have hyMid : y ∈ Metric.closedBall candidate.center ρ :=
        hsub (Metric.mem_closedBall_self hs.le)
      have hyU : y ∈ U := hclosedU hyMid
      have hsmallU : Metric.closedBall y s ⊆ U := hsub.trans hclosedU
      have hrelativeSmall : charbonnelRelativeClosedBall U y s =
          Metric.closedBall y s := by
        rw [charbonnelRelativeClosedBall, Set.inter_eq_right]
        exact hsmallU
      have hsmallMid : charbonnelRelativeClosedBall U y s ⊆
          charbonnelRelativeClosedBall U candidate.center ρ := by
        rw [hrelativeSmall, hrelativeρ]
        exact hsub
      have hsmallCandidate : charbonnelRelativeClosedBall U y s ⊆
          charbonnelRelativeClosedBall U
            candidate.center candidate.radius :=
        hsmallMid.trans hρsub
      have hsmall := hcandidate y hyU s hs hsmallCandidate
      have hcount : charbonnelLocalVerticalComponentCount S y s =
          (candidate.count : ℕ∞) := by
        change ENat.card (ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall y s) : Set ℝ)) =
            (candidate.count : ℕ∞)
        rw [← hrelativeSmall]
        exact hsmall.1
      refine ⟨hcount, ?_⟩
      have hcomp :
          charbonnelVerticalComponentInclusionMap S hsmallCandidate =
            charbonnelVerticalComponentInclusionMap S hρsub ∘
              charbonnelVerticalComponentInclusionMap S hsmallMid := by
        exact charbonnelVerticalComponentInclusionMap_trans S _ _
      have hsmallBijective : Function.Bijective
          (charbonnelVerticalComponentInclusionMap S hsmallCandidate) :=
        hsmall.2
      have hmidBijective : Function.Bijective
          (charbonnelVerticalComponentInclusionMap S hρsub) := hmid.2
      have hrelativeMap : Function.Bijective
          (charbonnelVerticalComponentInclusionMap S hsmallMid) := by
        apply (Function.Bijective.of_comp_iff' hmidBijective _).mp
        rw [← hcomp]
        exact hsmallBijective
      exact charbonnelVerticalComponentInclusionMap_bijective_congr S
        hsmallMid hsub hrelativeSmall hrelativeρ hrelativeMap }
  refine ⟨w, ?_⟩
  intro y hy
  apply hclosedU
  change y ∈ Metric.closedBall candidate.center (ρ / 2) at hy
  rw [Metric.mem_closedBall] at hy ⊢
  linarith [hρ]

/-! ## Localized strict refinement on the actual trace region -/

/-- A relative incidence bound and strict refinement on an open base produce
an ambient stable witness in that same base. -/
theorem
    exists_stableLocalVerticalIntervalWitness_inside_open_of_openBaseBound_of_strictLexRefinement
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound U S)
    (hrefine : CharbonnelSection53StrictLexRefinement U S) :
    ∃ w : CharbonnelStableLocalVerticalIntervalWitness S,
      w.innerBall ⊆ U := by
  have hstarting : Nonempty (CharbonnelRelativeLocalMaxCandidate U S) :=
    exists_charbonnelRelativeLocalMaxCandidate hUnonempty hbound
  obtain ⟨candidate, hzero⟩ :=
    exists_fullSupport_relativeLocalMaxCandidate_of_strictLexRefinement
      hstarting hrefine
  exact exists_stableLocalVerticalIntervalWitness_inside_open_of_relativeSeparation
    hUopen (candidate.stableIntervalSeparation_of_defect_zero hzero)

end AbelFormalization
