import AbelFormalization.CharbonnelSection53GlobalStratum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The local choice and stationary-chain construction in Charbonnel 5.3(c)

The printed source works in the globally maximal `M` stratum with minimum
defect `δ`.  If the induction does not pass to a smaller lexicographic rank,
it constructs balls of that same rank inside `B_m \ β_m`, with radii tending
to zero.  This module proves the available topology and finite maximization
behind that choice, and constructs the infinite chain from one explicit
local successor property.  It does not assert that successor property from
compactness or WS5: that component/defect preservation is the remaining
sublemma of the source's induction.
-/

noncomputable section

open Set Function Filter
open scoped Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Positive relative subballs avoiding a closed defective union -/

/-- An interior base point outside a closed set `β` has a positive relative
closed subball contained in the current relative ball minus `β`. -/
theorem exists_relativeClosedBall_subset_diff_of_open_point
    {n : ℕ} {ω β : Set (RealEuclidean n)}
    {center x : RealEuclidean n} {radius : ℝ}
    (hβ : IsClosed β) (_hxω : x ∈ ω)
    (hxinner : x ∈ Metric.ball center radius)
    (hxβ : x ∉ β) :
    ∃ r : ℝ, 0 < r ∧
      charbonnelRelativeClosedBall ω x r ⊆
        charbonnelRelativeClosedBall ω center radius \ β := by
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.mp hβ.isOpen_compl x hxβ
  have hgap : 0 < radius - dist x center :=
    sub_pos.mpr (by simpa only [Metric.mem_ball] using hxinner)
  let r : ℝ := min (ε / 2) ((radius - dist x center) / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hgap)
  have hrε : r < ε := by
    have := min_le_left (ε / 2) ((radius - dist x center) / 2)
    dsimp [r]
    linarith
  have hrOriginal : r + dist x center < radius := by
    have := min_le_right (ε / 2) ((radius - dist x center) / 2)
    dsimp [r]
    linarith
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hyβc : y ∈ βᶜ :=
    hεsub (Metric.closedBall_subset_ball hrε hy.2)
  have hyOriginal : y ∈ Metric.closedBall center radius :=
    Metric.ball_subset_closedBall
      (Metric.closedBall_subset_ball' hrOriginal hy.2)
  exact ⟨⟨hy.1, hyOriginal⟩, hyβc⟩

/-! ## Maximize the count in the surviving relative open region -/

/-- A nonempty collection of positive relative balls inside `U` contains
one maximizing the vertical component count within that collection. -/
theorem exists_localMax_relativeBall_inside
    {n : ℕ} {ω U : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S)
    (hball : ∃ (x : RealEuclidean n) (r : ℝ),
      x ∈ ω ∧ 0 < r ∧
        charbonnelRelativeClosedBall ω x r ⊆ U) :
    ∃ candidate : CharbonnelRelativeLocalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω candidate.center candidate.radius ⊆ U ∧
      ∀ (y : RealEuclidean n), y ∈ ω →
        ∀ (s : ℝ), 0 < s →
          charbonnelRelativeClosedBall ω y s ⊆ U →
            charbonnelRelativeLocalVerticalComponentCount ω S y s ≤
              (candidate.count : ℕ∞) := by
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨x₀, r₀, hx₀, hr₀, hsub₀⟩ := hball
  let Parameter := {p : RealEuclidean n × ℝ //
    p.1 ∈ ω ∧ 0 < p.2 ∧
      charbonnelRelativeClosedBall ω p.1 p.2 ⊆ U}
  let : Nonempty Parameter :=
    ⟨⟨(x₀, r₀), ⟨hx₀, hr₀, hsub₀⟩⟩⟩
  let f : Parameter → ℕ∞ := fun p ↦
    charbonnelRelativeLocalVerticalComponentCount ω S p.1.1 p.1.2
  have hf : ∀ p : Parameter, f p ≤ (N : ℕ∞) := by
    intro p
    exact hN p.1.1 p.2.1 p.1.2 p.2.2.1
  obtain ⟨M, p, hp, hmax⟩ :=
    exists_maximal_enat_value_of_bounded f N hf
  let candidate : CharbonnelRelativeLocalMaxCandidate ω S := {
    center := p.1.1
    center_mem := p.2.1
    radius := p.1.2
    radius_pos := p.2.2.1
    count := M
    count_eq := hp
    locally_maximal := by
      intro y hy s hs hsub
      exact hmax ⟨(y, s), ⟨hy, hs, hsub.trans p.2.2.2⟩⟩ }
  refine ⟨candidate, p.2.2.2, ?_⟩
  intro y hy s hs hsub
  exact hmax ⟨(y, s), ⟨hy, hs, hsub⟩⟩

/-- Once a point of the relative interior survives deletion of `β`, the
proved compactness of `β` and the uniform incidence bound choose a
bad-support-avoiding local maximum.  Its count cannot exceed the original
locally maximal count. -/
theorem exists_badAvoiding_localMax_count_le
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω) (hS : IsCompact S)
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S)
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    {x : RealEuclidean n} (hxω : x ∈ ω)
    (hxinner : x ∈ Metric.ball candidate.center candidate.radius)
    (hxβ : x ∉ charbonnelRelativeDefectiveSupportUnion candidate) :
    ∃ next : CharbonnelRelativeLocalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω next.center next.radius ⊆
        charbonnelRelativeClosedBall ω candidate.center candidate.radius \
          charbonnelRelativeDefectiveSupportUnion candidate ∧
      (next.count : ℕ∞) ≤ (candidate.count : ℕ∞) := by
  obtain ⟨r, hr, hsub⟩ :=
    exists_relativeClosedBall_subset_diff_of_open_point
      (charbonnelRelativeDefectiveSupportUnion_isClosed hω hS candidate)
      hxω hxinner hxβ
  obtain ⟨next, hnext, _hmax⟩ :=
    exists_localMax_relativeBall_inside hbound
      ⟨x, r, hxω, hr, hsub⟩
  refine ⟨next, hnext, ?_⟩
  rw [← next.count_eq]
  exact candidate.locally_maximal next.center next.center_mem
    next.radius next.radius_pos (hnext.trans Set.sdiff_subset)

/-! ## The sole missing rank-preserving local choice -/

/-- A direct local descent from a globally minimal-defect candidate to a
contained positive relative ball with a smaller `(M, δ)` rank.  If its count
drops, this is the smaller-`M` branch of the paper's induction. -/
def CharbonnelSection53LocalLexDescentFrom
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S) : Prop :=
  ∃ next : CharbonnelRelativeLocalMaxCandidate ω S,
    charbonnelRelativeClosedBall ω next.center next.radius ⊆
      charbonnelRelativeClosedBall ω
        candidate.1.1.center candidate.1.1.radius ∧
    Prod.Lex (· < ·) (· < ·)
      next.lexRank candidate.1.1.lexRank

/-- If no minimal global candidate admits a direct local rank descent,
the source's induction must choose a new minimum-defect global candidate
inside `B \ β`, with at most half the old radius.  The topology and finite
maximization above provide a local maximum when the complement has an
interior point; upgrading its rank to the same global `(M, δ)` is precisely
the unfinished component-stabilization choice.  This single property is
left as a theorem premise. -/
def CharbonnelSection53NoDescentSuccessorChoice
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∀ candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
    candidate.1.1.defectCount ≠ 0 →
    ¬ CharbonnelSection53LocalLexDescentFrom candidate →
    ∃ next : CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      charbonnelRelativeClosedBall ω
          next.1.1.center next.1.1.radius ⊆
        charbonnelRelativeClosedBall ω
            candidate.1.1.center candidate.1.1.radius \
          charbonnelRelativeDefectiveSupportUnion candidate.1.1 ∧
      next.1.1.radius ≤ candidate.1.1.radius / 2

/-- All globally minimal defect balls have positive defect `δ`, so
candidatewise successor choice and failure of every direct descent produce
the exact stationary sequence of the source.  Halving the radius at each
step yields convergence to zero by a geometric bound and the squeeze
theorem. -/
theorem charbonnelSection53_stationaryChain_of_noDescentSuccessorChoice
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hstarting : Nonempty
      (CharbonnelRelativeMinimalDefectGlobalCandidate ω S))
    (hpositive : ∀ candidate :
      CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      candidate.1.1.defectCount ≠ 0)
    (hnoDescent : ¬ ∃ candidate :
      CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      CharbonnelSection53LocalLexDescentFrom candidate)
    (hchoice : CharbonnelSection53NoDescentSuccessorChoice ω S) :
    CharbonnelSection53StationaryNestedSequence ω S := by
  let Candidate := CharbonnelRelativeMinimalDefectGlobalCandidate ω S
  let first : Candidate := Classical.choice hstarting
  let step (candidate : Candidate) : Candidate :=
    Classical.choose (hchoice candidate (hpositive candidate)
      (by intro hdesc; exact hnoDescent ⟨candidate, hdesc⟩))
  have hstep (candidate : Candidate) :
      charbonnelRelativeClosedBall ω
          (step candidate).1.1.center
          (step candidate).1.1.radius ⊆
        charbonnelRelativeClosedBall ω
            candidate.1.1.center candidate.1.1.radius \
          charbonnelRelativeDefectiveSupportUnion candidate.1.1 ∧
      (step candidate).1.1.radius ≤ candidate.1.1.radius / 2 := by
    exact Classical.choose_spec (hchoice candidate (hpositive candidate)
      (by intro hdesc; exact hnoDescent ⟨candidate, hdesc⟩))
  let sequence : ℕ → Candidate :=
    fun k ↦ Nat.rec first (fun _j candidate ↦ step candidate) k
  have hseq_succ (k : ℕ) :
      sequence (k + 1) = step (sequence k) := rfl
  have hsub (k : ℕ) :
      charbonnelRelativeClosedBall ω
          (sequence (k + 1)).1.1.center
          (sequence (k + 1)).1.1.radius ⊆
        charbonnelRelativeClosedBall ω
            (sequence k).1.1.center (sequence k).1.1.radius \
          charbonnelRelativeDefectiveSupportUnion (sequence k).1.1 := by
    rw [hseq_succ]
    exact (hstep (sequence k)).1
  let geometric : ℕ → ℝ :=
    fun k ↦ first.1.1.radius * (1 / 2 : ℝ) ^ k
  have hradius (k : ℕ) :
      (sequence k).1.1.radius ≤ geometric k := by
    induction k with
    | zero =>
        simp [sequence, geometric]
    | succ k ih =>
        rw [hseq_succ]
        calc
          (step (sequence k)).1.1.radius ≤
              (sequence k).1.1.radius / 2 := (hstep (sequence k)).2
          _ = (sequence k).1.1.radius * (1 / 2 : ℝ) := by ring
          _ ≤ geometric k * (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right ih (by norm_num)
          _ = geometric (k + 1) := by
            simp only [geometric, pow_succ]
            ring
  have hgeometric : Tendsto geometric atTop (nhds 0) := by
    have hpow : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k)
        atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [geometric, mul_zero] using hpow.const_mul first.1.1.radius
  have htendsto :
      Tendsto (fun k : ℕ ↦ (sequence k).1.1.radius)
        atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ ↦ (0 : ℝ)) (h := geometric)
    · exact tendsto_const_nhds
    · exact hgeometric
    · intro k
      exact (sequence k).1.1.radius_pos.le
    · exact hradius
  exact ⟨sequence, hpositive (sequence 0), hsub, htendsto⟩

/-- With the single local rank-preserving choice isolated above, the
global minimal-defect stratum has the paper's `δ > 0` dichotomy: a direct
lexicographic descent or a stationary nested sequence.  Positivity of `δ`
is supplied by one minimum-defect candidate and transported to all others
by the proved equality of their defects. -/
theorem charbonnelSection53_globalDichotomy_of_successorChoice
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hstarting : Nonempty
      (CharbonnelRelativeMinimalDefectGlobalCandidate ω S))
    (hpositive : ∃ candidate :
      CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      candidate.1.1.defectCount ≠ 0)
    (hchoice : CharbonnelSection53NoDescentSuccessorChoice ω S) :
    (∃ candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      CharbonnelSection53LocalLexDescentFrom candidate) ∨
      CharbonnelSection53StationaryNestedSequence ω S := by
  obtain ⟨positiveCandidate, hδpos⟩ := hpositive
  have hpositiveAll : ∀ candidate :
      CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      candidate.1.1.defectCount ≠ 0 := by
    intro candidate hzero
    have heq :=
      charbonnelRelativeMinimalDefectGlobalCandidates_defect_eq
        candidate positiveCandidate
    exact hδpos (heq.symm.trans hzero)
  by_cases hdescent : ∃ candidate :
      CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      CharbonnelSection53LocalLexDescentFrom candidate
  · exact Or.inl hdescent
  · exact Or.inr
      (charbonnelSection53_stationaryChain_of_noDescentSuccessorChoice
        hstarting hpositiveAll hdescent hchoice)

/-- The proved moving-ball incidence bound supplies the global `M` and
minimum `δ` strata for a literal-zero closure member.  At positive `δ`,
the only remaining input to this source-shaped dichotomy is the explicitly
named rank-preserving successor choice. -/
theorem literalZeroSet_charbonnelClosure_section53_globalDichotomy
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hω : ω.Nonempty)
    (hprojection : CharbonnelFullBaseProjection ω S)
    (hpositive : ∃ candidate :
      CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      candidate.1.1.defectCount ≠ 0)
    (hchoice : CharbonnelSection53NoDescentSuccessorChoice ω S) :
    (∃ candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
      CharbonnelSection53LocalLexDescentFrom candidate) ∨
      CharbonnelSection53StationaryNestedSequence ω S := by
  have hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S :=
    literalZeroSet_charbonnelClosure_relativeUniformLocalVerticalComponentBound
      hG hsmooth hUFF hS hprojection.1
  have hglobal : Nonempty (CharbonnelRelativeGlobalMaxCandidate ω S) :=
    exists_charbonnelRelativeGlobalMaxCandidate hω hbound
  have hminimum : Nonempty
      (CharbonnelRelativeMinimalDefectGlobalCandidate ω S) :=
    exists_charbonnelRelativeMinimalDefectGlobalCandidate hglobal
  exact charbonnelSection53_globalDichotomy_of_successorChoice
    hminimum hpositive hchoice

end AbelFormalization
