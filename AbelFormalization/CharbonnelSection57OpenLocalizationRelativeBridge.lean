import AbelFormalization.CharbonnelSection53GlobalDichotomy
import AbelFormalization.CharbonnelSection57InfiniteFiberBridge

/-!
# Relative descent localized in a prescribed open set

The relative `(M, δ)` descent in section 5.3 previously produced a
full-support ball without retaining the region in which the starting ball
was chosen.  Section 5.7 needs exactly this extra control: its stable ball
must lie in an arbitrarily prescribed nonempty open part of the positive
zero trace.

This file proves the missing localization algebra.  A lexicographically
minimal candidate is chosen only among candidates whose relative ball lies
in the prescribed set.  Since strict refinements are contained in their
parent ball, the subtype is closed under refinement, and its minimum has
zero defect.  On the full base `Set.univ`, relative balls are ordinary
closed balls, so the resulting candidate gives an explicit
`CharbonnelStableLocalVerticalIntervalWitness` whose half-radius ball stays
inside the prescribed open set.

The final literal-zero theorem therefore reduces open localization to the
already isolated `CharbonnelSection53StrictLexRefinement` statement for
`closure S`; it introduces no further geometric predicate.
-/

noncomputable section

open Set Function
open scoped Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## A compact closed ball inside an open set -/

/-- Every nonempty open Euclidean set contains a positive-radius closed
ball.  The factor `1 / 2` leaves the closed ball strictly inside the open
ball supplied by openness. -/
theorem exists_positive_closedBall_subset_of_open
    {n : ℕ} {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty) :
    ∃ (x : RealEuclidean n) (r : ℝ),
      0 < r ∧ Metric.closedBall x r ⊆ U := by
  obtain ⟨x, hxU⟩ := hUnonempty
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  refine ⟨x, ε / 2, half_pos hε, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hball

/-! ## Well-founded descent while retaining the prescribed region -/

/-- The strict lexicographic refinement argument can be run in the subtype
of candidates whose relative balls lie in a fixed set `U`.  Containment of
each refinement in its parent is exactly what keeps that subtype closed
under the descent. -/
theorem
    exists_fullSupport_relativeLocalMaxCandidate_inside_of_strictLexRefinement
    {n : ℕ} {ω U : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hstarting : ∃ candidate : CharbonnelRelativeLocalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω candidate.center candidate.radius ⊆ U)
    (hrefine : CharbonnelSection53StrictLexRefinement ω S) :
    ∃ candidate : CharbonnelRelativeLocalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω candidate.center candidate.radius ⊆ U ∧
      candidate.defectCount = 0 := by
  let Inside := {candidate : CharbonnelRelativeLocalMaxCandidate ω S //
    charbonnelRelativeClosedBall ω candidate.center candidate.radius ⊆ U}
  let rank : Inside → ℕ × ℕ := fun candidate ↦ candidate.1.lexRank
  have hwf : WellFounded
      (Prod.Lex (· < ·) (· < ·) on rank) :=
    (wellFounded_lt.prod_lex wellFounded_lt).onFun
  obtain ⟨starting, hstartingInside⟩ := hstarting
  let first : Inside := ⟨starting, hstartingInside⟩
  obtain ⟨minimum, _hmem, hminimal⟩ :=
    hwf.has_min (Set.univ : Set Inside)
      ⟨first, Set.mem_univ first⟩
  refine ⟨minimum.1, minimum.2, ?_⟩
  by_contra hdefect
  obtain ⟨next, hnextSub, hnextRank⟩ := hrefine minimum.1 hdefect
  let nextInside : Inside :=
    ⟨next, hnextSub.trans minimum.2⟩
  exact hminimal nextInside (Set.mem_univ nextInside) hnextRank

/-! ## The zero-defect candidate's stability, without losing its center -/

/-- This is the pointwise content of
`stableIntervalSeparation_of_defect_zero`, stated for the original candidate
rather than behind an existential.  Retaining that candidate is needed to
retain its already proved containment in the prescribed open set. -/
theorem CharbonnelRelativeLocalMaxCandidate.stableAtSelf_of_defect_zero
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    (hzero : candidate.defectCount = 0) :
    ∀ (y : RealEuclidean n), y ∈ ω →
      ∀ (s : ℝ), 0 < s →
        ∀ hsub : charbonnelRelativeClosedBall ω y s ⊆
            charbonnelRelativeClosedBall ω candidate.center candidate.radius,
          charbonnelRelativeLocalVerticalComponentCount ω S y s =
              (candidate.count : ℕ∞) ∧
            Function.Bijective
              (charbonnelVerticalComponentInclusionMap S hsub) := by
  let B := charbonnelRelativeClosedBall ω
    candidate.center candidate.radius
  have hfull := candidate.fullSupport_of_defect_zero hzero
  intro y hy s hs hsub
  have hnonempty :
      (charbonnelRelativeClosedBall ω y s).Nonempty :=
    charbonnelRelativeClosedBall_nonempty hy hs.le
  have hlargeLeSmall :=
    enatCard_verticalComponents_le_of_fullSupport S hsub hnonempty hfull
  have hsmallLeLarge := candidate.locally_maximal y hy s hs hsub
  have hcount :
      charbonnelRelativeLocalVerticalComponentCount ω S y s =
        (candidate.count : ℕ∞) :=
    le_antisymm hsmallLeLarge (by
      rw [← candidate.count_eq]
      exact hlargeLeSmall)
  refine ⟨hcount, ?_⟩
  have hsurj :=
    surjective_charbonnelVerticalComponentInclusionMap_of_fullSupport
      S hsub hnonempty hfull
  letI : Finite (ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω y s) : Set ℝ)) :=
    ENat.card_lt_top.mp (hcount.trans_lt (by simp))
  letI : Finite (ConnectedComponents
      (charbonnelVerticalImageOver S B : Set ℝ)) :=
    ENat.card_lt_top.mp (candidate.count_eq.trans_lt (by simp))
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨hsurj, ?_⟩
  have hcard := congrArg ENat.toNat
    (hcount.trans candidate.count_eq.symm)
  simpa only [charbonnelRelativeLocalVerticalComponentCount,
    ENat.card_eq_coe_natCard, ENat.toNat_natCast] using hcard

/-! ## From relative descent on `univ` to a localized ambient witness -/

/-- A relative incidence bound and strict refinement on the full base give
an ambient stable-interval witness inside any prescribed nonempty open set.
The starting candidate is first maximized only among closed balls in `U`;
the localized well-founded descent above then preserves this containment. -/
theorem
    exists_stableLocalVerticalIntervalWitness_inside_open_of_relativeBound_of_strictLexRefinement
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound
      (Set.univ : Set (RealEuclidean n)) S)
    (hrefine : CharbonnelSection53StrictLexRefinement
      (Set.univ : Set (RealEuclidean n)) S) :
    ∃ w : CharbonnelStableLocalVerticalIntervalWitness S,
      w.innerBall ⊆ U := by
  obtain ⟨x, r, hr, hclosedBall⟩ :=
    exists_positive_closedBall_subset_of_open hUopen hUnonempty
  have hrelativeBall : charbonnelRelativeClosedBall
      (Set.univ : Set (RealEuclidean n)) x r ⊆ U := by
    simpa only [charbonnelRelativeClosedBall, Set.univ_inter] using
      hclosedBall
  obtain ⟨starting, hstartingInside, _hmaxInside⟩ :=
    exists_localMax_relativeBall_inside hbound
      ⟨x, r, Set.mem_univ x, hr, hrelativeBall⟩
  obtain ⟨candidate, hcandidateInside, hzero⟩ :=
    exists_fullSupport_relativeLocalMaxCandidate_inside_of_strictLexRefinement
      ⟨starting, hstartingInside⟩ hrefine
  have hcandidateBall : charbonnelRelativeClosedBall
      (Set.univ : Set (RealEuclidean n)) candidate.center candidate.radius =
        Metric.closedBall candidate.center candidate.radius := by
    exact Set.univ_inter _
  have hcount : charbonnelLocalVerticalComponentCount S
      candidate.center candidate.radius = (candidate.count : ℕ∞) := by
    change ENat.card (ConnectedComponents
      (charbonnelVerticalImageOver S
        (Metric.closedBall candidate.center candidate.radius) : Set ℝ)) =
          (candidate.count : ℕ∞)
    rw [← hcandidateBall]
    exact candidate.count_eq
  obtain ⟨label⟩ :=
    exists_fin_equiv_connectedComponents_of_enatCard_eq hcount
  let w : CharbonnelStableLocalVerticalIntervalWitness S := {
    count := candidate.count
    center := candidate.center
    radius := candidate.radius
    radius_pos := candidate.radius_pos
    label := label
    stable := by
      intro y s hs hsub
      have hyBall : charbonnelRelativeClosedBall
          (Set.univ : Set (RealEuclidean n)) y s =
            Metric.closedBall y s := by
        exact Set.univ_inter _
      have hsubRelative : charbonnelRelativeClosedBall
          (Set.univ : Set (RealEuclidean n)) y s ⊆
            charbonnelRelativeClosedBall
              (Set.univ : Set (RealEuclidean n))
                candidate.center candidate.radius := by
        rw [hyBall, hcandidateBall]
        exact hsub
      have hstableRelative := candidate.stableAtSelf_of_defect_zero hzero
        y (Set.mem_univ y) s hs hsubRelative
      have hsmallCount : ENat.card (ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall y s) : Set ℝ)) =
            (candidate.count : ℕ∞) := by
        rw [← hyBall]
        exact hstableRelative.1
      have hfullRelative := candidate.fullSupport_of_defect_zero hzero
      have hfull : ∀ c : ConnectedComponents
          (charbonnelVerticalImageOver S
            (Metric.closedBall candidate.center candidate.radius) : Set ℝ),
          charbonnelVerticalComponentBaseSupport S
              (Metric.closedBall candidate.center candidate.radius) c =
            Metric.closedBall candidate.center candidate.radius := by
        rw [← hcandidateBall]
        exact hfullRelative
      have hnonempty : (Metric.closedBall y s).Nonempty :=
        ⟨y, Metric.mem_closedBall_self hs.le⟩
      refine ⟨hsmallCount, ?_⟩
      have hsurj :=
        surjective_charbonnelVerticalComponentInclusionMap_of_fullSupport
          S hsub hnonempty hfull
      letI : Finite (ConnectedComponents
          (charbonnelVerticalImageOver S
            (Metric.closedBall y s) : Set ℝ)) :=
        ENat.card_lt_top.mp (hsmallCount.trans_lt (by simp))
      letI : Finite (ConnectedComponents
          (charbonnelVerticalImageOver S
            (Metric.closedBall candidate.center candidate.radius) : Set ℝ)) :=
        ENat.card_lt_top.mp (hcount.trans_lt (by simp))
      apply (Nat.bijective_iff_surjective_and_card _).2
      refine ⟨hsurj, ?_⟩
      have hcard := congrArg ENat.toNat (hsmallCount.trans hcount.symm)
      simpa only [charbonnelLocalVerticalComponentCount,
        ENat.card_eq_coe_natCard, ENat.toNat_natCast] using hcard }
  refine ⟨w, ?_⟩
  intro y hy
  apply hcandidateInside
  refine ⟨Set.mem_univ y, ?_⟩
  change y ∈ Metric.closedBall candidate.center
    (candidate.radius / 2) at hy
  rw [Metric.mem_closedBall] at hy ⊢
  linarith [candidate.radius_pos]

/-! ## Literal-zero specialization -/

/-- For a literal-zero Charbonnel member, UFF supplies every numerical
incidence bound needed for localized stability.  Thus, for one source set
and one prescribed open set, the only remaining input is the existing
strict-refinement statement for the topological closure on the full base. -/
theorem
    literalZeroSet_charbonnelClosure_exists_stableClosureWitness_inside_open_of_strictLexRefinement
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hrefine : CharbonnelSection53StrictLexRefinement
      (Set.univ : Set (RealEuclidean n)) (closure S)) :
    ∃ w : CharbonnelStableLocalVerticalIntervalWitness (closure S),
      w.innerBall ⊆ U := by
  have hclosure : closure S ∈
      charbonnelClosure (literalZeroSetFamily G) (n + 1) :=
    charbonnelClosure_topologicalClosure hS
  have hambient : CharbonnelUniformLocalVerticalComponentBound (closure S) :=
    literalZeroSet_charbonnelClosure_uniformLocalVerticalComponentBound
      hG hsmooth hUFF hclosure
  have hrelative : CharbonnelRelativeUniformLocalVerticalComponentBound
      (Set.univ : Set (RealEuclidean n)) (closure S) :=
    hambient.relative_of_baseSupported (by
      intro z _hz
      exact Set.mem_univ (charbonnelVerticalBaseCoordinate z))
  exact
    exists_stableLocalVerticalIntervalWitness_inside_open_of_relativeBound_of_strictLexRefinement
      hUopen hUnonempty hrelative hrefine

end AbelFormalization
