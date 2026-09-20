import AbelFormalization.CharbonnelSection53GlobalDichotomy

/-!
# The rank-one base case in Charbonnel 5.3(c)

Charbonnel starts the lexicographic induction in 5.3(c) by observing that
the assertion is immediate when the maximal vertical component count is
one.  Full base projection makes that observation precise: if a relative
ball has only one vertical-image component, every base point of the ball
meets that component, so its defect is zero.

This removes both positive-defect obstructions at rank one.  In particular,
the no-descent successor choice holds vacuously there, and a stationary
positive-defect chain cannot have global component count one.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Full base projection makes the vertical image over every relative
candidate ball nonempty, so its component count is positive. -/
theorem CharbonnelRelativeLocalMaxCandidate.count_ne_zero_of_fullProjection
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hprojection : CharbonnelFullBaseProjection ω S)
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S) :
    candidate.count ≠ 0 := by
  let B : Set (RealEuclidean n) :=
    charbonnelRelativeClosedBall ω candidate.center candidate.radius
  let V : Set ℝ := charbonnelVerticalImageOver S B
  have hcenterB : candidate.center ∈ B := by
    exact ⟨candidate.center_mem,
      Metric.mem_closedBall_self candidate.radius_pos.le⟩
  obtain ⟨t, hctS⟩ :=
    hprojection.2 candidate.center candidate.center_mem
  have htV : t ∈ V := ⟨candidate.center, hcenterB, hctS⟩
  letI : Nonempty (ConnectedComponents V) :=
    ⟨ConnectedComponents.mk (⟨t, htV⟩ : V)⟩
  intro hzero
  apply ENat.card_ne_zero (α := ConnectedComponents V)
  calc
    ENat.card (ConnectedComponents V) = (candidate.count : ℕ∞) := by
      simpa only [V, B, charbonnelRelativeLocalVerticalComponentCount]
        using candidate.count_eq
    _ = 0 := by simp [hzero]

/-- A full-projection relative candidate with one vertical component has
full support for that component and hence zero defect.  This is the
`M = 1` base case stated at the start of Charbonnel 5.3(c). -/
theorem CharbonnelRelativeLocalMaxCandidate.defectCount_eq_zero_of_count_eq_one
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hprojection : CharbonnelFullBaseProjection ω S)
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    (hcount : candidate.count = 1) :
    candidate.defectCount = 0 := by
  let B : Set (RealEuclidean n) :=
    charbonnelRelativeClosedBall ω candidate.center candidate.radius
  let V : Set ℝ := charbonnelVerticalImageOver S B
  have hcomponentCard : ENat.card (ConnectedComponents V) ≤ 1 := by
    change charbonnelRelativeLocalVerticalComponentCount ω S
      candidate.center candidate.radius ≤ 1
    rw [candidate.count_eq, hcount]
    simp
  have hcomponentsSubsingleton : Subsingleton (ConnectedComponents V) :=
    (ENat.card_le_one_iff_subsingleton (ConnectedComponents V)).mp
      hcomponentCard
  have hfull : ∀ c : ConnectedComponents V,
      charbonnelVerticalComponentBaseSupport S B c = B := by
    intro c
    apply Set.Subset.antisymm
    · exact charbonnelVerticalComponentBaseSupport_subset S B c
    · intro y hyB
      obtain ⟨t, hytS⟩ := hprojection.2 y hyB.1
      have htV : t ∈ V := ⟨y, hyB, hytS⟩
      have htCover : t ∈ ⋃ d : ConnectedComponents V,
          realConnectedComponentCarrier V d := by
        rw [iUnion_realConnectedComponentCarrier V]
        exact htV
      obtain ⟨d, htd⟩ := Set.mem_iUnion.mp htCover
      have hdc : d = c := hcomponentsSubsingleton.elim d c
      exact ⟨hyB, t, hdc ▸ htd, hytS⟩
  let Bad := {c : ConnectedComponents V //
    charbonnelVerticalComponentBaseSupport S B c ≠ B}
  have hBadEmpty : IsEmpty Bad :=
    ⟨fun bad ↦ bad.2 (hfull bad.1)⟩
  change Nat.card Bad = 0
  exact (Nat.card_eq_zero (α := Bad)).mpr (Or.inl hBadEmpty)

/-- Positive defect can therefore begin only at component count at least
two.  This is the exact numerical reduction left after the source's
rank-one base case. -/
theorem CharbonnelRelativeLocalMaxCandidate.two_le_count_of_defectCount_ne_zero
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hprojection : CharbonnelFullBaseProjection ω S)
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    (hpositive : candidate.defectCount ≠ 0) :
    2 ≤ candidate.count := by
  have hzeroNe : candidate.count ≠ 0 :=
    candidate.count_ne_zero_of_fullProjection hprojection
  have honeNe : candidate.count ≠ 1 := by
    intro hone
    exact hpositive
      (candidate.defectCount_eq_zero_of_count_eq_one hprojection hone)
  omega

/-- At global component count one the rank-preserving successor condition
from 5.3(c) is automatic, because its positive-defect antecedent is
impossible. -/
theorem charbonnelSection53_noDescentSuccessorChoice_of_globalCount_one
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hprojection : CharbonnelFullBaseProjection ω S)
    (rankOne : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hcount : rankOne.1.1.count = 1) :
    CharbonnelSection53NoDescentSuccessorChoice ω S := by
  intro candidate hpositive _hnoDescent
  have hcountENat := charbonnelRelativeGlobalMaxCandidates_count_eq
    candidate.1 rankOne.1
  have hcandidateCount : candidate.1.1.count = 1 := by
    apply ENat.natCast_inj.mp
    simpa only [hcount] using hcountENat
  have hzero : candidate.1.1.defectCount = 0 :=
    candidate.1.1.defectCount_eq_zero_of_count_eq_one
      hprojection hcandidateCount
  exact (hpositive hzero).elim

/-- Consequently, no positive-defect stationary chain can occur in the
global `M = 1` stratum. -/
theorem charbonnelSection53_noStationary_of_globalCount_one
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hprojection : CharbonnelFullBaseProjection ω S)
    (rankOne : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hcount : rankOne.1.1.count = 1) :
    CharbonnelSection53NoStationaryNestedSequence ω S := by
  rintro ⟨sequence, hpositive, _hdelete, _hradius⟩
  have hcountENat := charbonnelRelativeGlobalMaxCandidates_count_eq
    (sequence 0).1 rankOne.1
  have hsequenceCount : (sequence 0).1.1.count = 1 := by
    apply ENat.natCast_inj.mp
    simpa only [hcount] using hcountENat
  exact hpositive
    ((sequence 0).1.1.defectCount_eq_zero_of_count_eq_one
      hprojection hsequenceCount)

end AbelFormalization
