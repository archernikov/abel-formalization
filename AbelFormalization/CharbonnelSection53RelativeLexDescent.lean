import AbelFormalization.CharbonnelSection5LocalVerticalStability
import Mathlib.Data.Prod.Lex
import Mathlib.Order.RelClasses

/-!
# The relative-ball and lexicographic form of Charbonnel 5.3(c)

Charbonnel equips the compact base `ω` with its restricted Euclidean metric.
His `B(x, ε)` is therefore `ω ∩ Metric.closedBall x ε`, with `x ∈ ω`.
The ambient-ball formulation in `CharbonnelSection5LocalVerticalStability`
is a valid conditional assembly lemma, but its full-support selection premise
is stronger than the source and fails for compact semialgebraic examples.

Even with `ω = [-1,1]` and full base projection, take the zero graph over
`ω` and add the isolated point `(0,1)`.  A ball meeting `0` sees two vertical
components, but the upper component is supported only at `0`.  Charbonnel's
lexicographic descent may discard it and finish with `M = 1` on a smaller
ball.  Thus the selection rule below allows `M` to decrease.

This file formalizes a sufficient order-theoretic assembly: a positive relative
ball with a locally maximal component count is a candidate; its defect `δ`
counts components whose base support is not the whole relative ball.  A
strict `(M, δ)` refinement for each defective candidate, together with the
well-foundedness of lexicographic order on `ℕ × ℕ`, gives a zero-defect
candidate.  The remaining strict-refinement premise is stronger than the
global-stratum `(M, δ)` induction stated in 5.3(c).  It is an explicit
sufficient interface for a future source-level nested-ball argument and is
not claimed to follow from compactness, full base projection, and the
pointwise vertical component bound alone.  A compact counterexample can
place nested two-component vertical sets over a dense sequence of base
points, with component scales tending to zero.  Every positive relative
ball then has rank `(2,1)` even though the limiting fiber has one component.
That example violates the weak structure's uniform affine-section bound;
the source uses tameness beyond the numerical local vertical bound.
-/

noncomputable section

open Set Function
open scoped Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Relative balls and the uniform bound from 5.3(a) -/

/-- A closed ball in the metric restricted to `ω`. -/
def charbonnelRelativeClosedBall {n : ℕ}
    (ω : Set (RealEuclidean n)) (x : RealEuclidean n) (r : ℝ) :
    Set (RealEuclidean n) :=
  ω ∩ Metric.closedBall x r

theorem charbonnelRelativeClosedBall_nonempty {n : ℕ}
    {ω : Set (RealEuclidean n)} {x : RealEuclidean n} {r : ℝ}
    (hx : x ∈ ω) (hr : 0 ≤ r) :
    (charbonnelRelativeClosedBall ω x r).Nonempty :=
  ⟨x, hx, Metric.mem_closedBall_self hr⟩

theorem charbonnelRelativeClosedBall_isClosed {n : ℕ}
    {ω : Set (RealEuclidean n)} (hω : IsClosed ω)
    (x : RealEuclidean n) (r : ℝ) :
    IsClosed (charbonnelRelativeClosedBall ω x r) :=
  hω.inter Metric.isClosed_closedBall

/-- A relative closed ball is compact when the source base is compact. -/
theorem charbonnelRelativeClosedBall_isCompact {n : ℕ}
    {ω : Set (RealEuclidean n)} (hω : IsCompact ω)
    (x : RealEuclidean n) (r : ℝ) :
    IsCompact (charbonnelRelativeClosedBall ω x r) :=
  hω.inter_right Metric.isClosed_closedBall

theorem charbonnelRelativeClosedBall_subset_base {n : ℕ}
    (ω : Set (RealEuclidean n)) (x : RealEuclidean n) (r : ℝ) :
    charbonnelRelativeClosedBall ω x r ⊆ ω :=
  inter_subset_left

/-- `S` projects into `ω` in its first `n` coordinates.  Full base
projection is added separately where the source needs it. -/
def CharbonnelBaseSupportedOn {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∀ z ∈ S, charbonnelVerticalBaseCoordinate z ∈ ω

/-- The source hypothesis `p_n(S) = ω`. -/
def CharbonnelFullBaseProjection {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  CharbonnelBaseSupportedOn ω S ∧
    ∀ x ∈ ω, ∃ t : ℝ, charbonnelAppendLastCoordinate x t ∈ S

/-- For a set supported over `ω`, intersecting an ambient ball with `ω`
does not change its vertical image. -/
theorem charbonnelVerticalImageOver_relativeBall_eq_ambient
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbase : CharbonnelBaseSupportedOn ω S)
    (x : RealEuclidean n) (r : ℝ) :
    charbonnelVerticalImageOver S (charbonnelRelativeClosedBall ω x r) =
      charbonnelVerticalImageOver S (Metric.closedBall x r) := by
  ext t
  constructor
  · rintro ⟨y, ⟨_hyω, hyball⟩, hyt⟩
    exact ⟨y, hyball, hyt⟩
  · rintro ⟨y, hyball, hyt⟩
    have hyω : y ∈ ω := by
      have := hbase (charbonnelAppendLastCoordinate y t) hyt
      simpa only [charbonnelVerticalBaseCoordinate,
        charbonnelAppendLastCoordinate,
        realEuclideanTakeLeft_append] using this
    exact ⟨y, ⟨hyω, hyball⟩, hyt⟩

/-- The interval labels over a relative ball have a compact carrier under
the paper's compactness assumption on `S`. -/
theorem charbonnelVerticalImageOver_relativeBall_isCompact
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω) (hS : IsCompact S)
    (x : RealEuclidean n) (r : ℝ) :
    IsCompact (charbonnelVerticalImageOver S
      (charbonnelRelativeClosedBall ω x r)) :=
  charbonnelVerticalImageOver_isCompact hS
    (charbonnelRelativeClosedBall_isClosed hω.isClosed x r)

/-- The local vertical count using the restricted metric on `ω`. -/
def charbonnelRelativeLocalVerticalComponentCount {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) (r : ℝ) : ℕ∞ :=
  ENat.card (ConnectedComponents
    (charbonnelVerticalImageOver S
      (charbonnelRelativeClosedBall ω x r) : Set ℝ))

/-- The uniform finite bound for all positive relative balls centered in
`ω`, the exact numerical conclusion of 5.3(a). -/
def CharbonnelRelativeUniformLocalVerticalComponentBound {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∃ N : ℕ, ∀ (x : RealEuclidean n), x ∈ ω →
    ∀ (r : ℝ), 0 < r →
      charbonnelRelativeLocalVerticalComponentCount ω S x r ≤
        (N : ℕ∞)

/-- The ambient incidence theorem already supplies Charbonnel's relative
5.3(a) bound when `S` is supported on `ω`. -/
theorem CharbonnelUniformLocalVerticalComponentBound.relative_of_baseSupported
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hbound : CharbonnelUniformLocalVerticalComponentBound S)
    (hbase : CharbonnelBaseSupportedOn ω S) :
    CharbonnelRelativeUniformLocalVerticalComponentBound ω S := by
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N, ?_⟩
  intro x _hx r hr
  rw [charbonnelRelativeLocalVerticalComponentCount,
    charbonnelVerticalImageOver_relativeBall_eq_ambient hbase x r]
  exact hN x r hr

/-- Literal-zero specialization of the relative incidence bound. -/
theorem literalZeroSet_charbonnelClosure_relativeUniformLocalVerticalComponentBound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hbase : CharbonnelBaseSupportedOn ω S) :
    CharbonnelRelativeUniformLocalVerticalComponentBound ω S :=
  (literalZeroSet_charbonnelClosure_uniformLocalVerticalComponentBound
    hG hsmooth hUFF hS).relative_of_baseSupported hbase

/-! ## Candidates and their lexicographic rank -/

/-- A ball with count `M` such that no positive relative subball has more
than `M` components.  The count need only be locally maximal. -/
structure CharbonnelRelativeLocalMaxCandidate {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) where
  center : RealEuclidean n
  center_mem : center ∈ ω
  radius : ℝ
  radius_pos : 0 < radius
  count : ℕ
  count_eq : charbonnelRelativeLocalVerticalComponentCount
    ω S center radius = (count : ℕ∞)
  locally_maximal : ∀ (y : RealEuclidean n), y ∈ ω →
    ∀ (s : ℝ), 0 < s →
      charbonnelRelativeClosedBall ω y s ⊆
        charbonnelRelativeClosedBall ω center radius →
      charbonnelRelativeLocalVerticalComponentCount ω S y s ≤
        (count : ℕ∞)

/-- The number of the local vertical components whose base support is
not the whole relative ball.  Under `count_eq` the component type, and
therefore this defective subtype, is finite. -/
def CharbonnelRelativeLocalMaxCandidate.defectCount
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S) : ℕ :=
  Nat.card {c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ) //
      charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c ≠
          charbonnelRelativeClosedBall ω candidate.center candidate.radius}

/-- The source's lexicographic `(M, δ)` induction rank. -/
def CharbonnelRelativeLocalMaxCandidate.lexRank
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S) : ℕ × ℕ :=
  (candidate.count, candidate.defectCount)

/-- Zero defect is equivalent to full base support of every component. -/
theorem CharbonnelRelativeLocalMaxCandidate.fullSupport_of_defect_zero
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    (hzero : candidate.defectCount = 0) :
    ∀ c : ConnectedComponents
        (charbonnelVerticalImageOver S
          (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ),
      charbonnelVerticalComponentBaseSupport S
          (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c =
        charbonnelRelativeClosedBall ω candidate.center candidate.radius := by
  letI : Finite (ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ)) :=
    ENat.card_lt_top.mp (candidate.count_eq.trans_lt (by simp))
  let Bad := {c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ) //
      charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c ≠
          charbonnelRelativeClosedBall ω candidate.center candidate.radius}
  letI : Finite Bad := Finite.of_injective Subtype.val Subtype.val_injective
  have hBadCard : Nat.card Bad = 0 := by
    simpa only [Bad, CharbonnelRelativeLocalMaxCandidate.defectCount]
      using hzero
  have hBadEmpty : IsEmpty Bad := by
    apply Finite.card_eq_zero_iff.mp
    exact hBadCard
  letI : IsEmpty Bad := hBadEmpty
  intro c
  by_contra hbad
  exact isEmptyElim (⟨c, hbad⟩ : Bad)

/-- A relative uniform bound and a nonempty base provide a starting
candidate: maximize the component count among all positive relative balls. -/
theorem exists_charbonnelRelativeLocalMaxCandidate
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : ω.Nonempty)
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S) :
    Nonempty (CharbonnelRelativeLocalMaxCandidate ω S) := by
  obtain ⟨N, hN⟩ := hbound
  let Parameter := {p : RealEuclidean n × ℝ // p.1 ∈ ω ∧ 0 < p.2}
  obtain ⟨x₀, hx₀⟩ := hω
  letI : Nonempty Parameter :=
    ⟨⟨(x₀, 1), ⟨hx₀, zero_lt_one⟩⟩⟩
  let f : Parameter → ℕ∞ := fun p ↦
    charbonnelRelativeLocalVerticalComponentCount ω S p.1.1 p.1.2
  have hf : ∀ p : Parameter, f p ≤ (N : ℕ∞) := by
    intro p
    exact hN p.1.1 p.2.1 p.1.2 p.2.2
  obtain ⟨M, p, hp, hmax⟩ :=
    exists_maximal_enat_value_of_bounded f N hf
  refine ⟨{
    center := p.1.1
    center_mem := p.2.1
    radius := p.1.2
    radius_pos := p.2.2
    count := M
    count_eq := hp
    locally_maximal := ?_ }⟩
  intro y hy s hs _hsub
  exact hmax ⟨(y, s), ⟨hy, hs⟩⟩

/-! ## The one remaining geometric descent, and its well-founded assembly -/

/-- A sufficient *stronger* refinement interface for the lexicographic
proof: every defective locally maximal relative ball contains a new locally
maximal relative ball of smaller `(M, δ)` rank.  The count `M` may fall.

Charbonnel instead fixes the global maximum `M`, minimizes `δ` in that
stratum, and excludes a stationary nested sequence at that rank.  His text
does not directly state this per-candidate implication.  Its status under
the source hypotheses remains to be proved; it is never inferred here from
the uniform count alone. -/
def CharbonnelSection53StrictLexRefinement
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∀ candidate : CharbonnelRelativeLocalMaxCandidate ω S,
    candidate.defectCount ≠ 0 →
      ∃ next : CharbonnelRelativeLocalMaxCandidate ω S,
        charbonnelRelativeClosedBall ω next.center next.radius ⊆
          charbonnelRelativeClosedBall ω candidate.center candidate.radius ∧
        Prod.Lex (· < ·) (· < ·) next.lexRank candidate.lexRank

/-- Lexicographic minimality turns the stronger strict-refinement premise
into a full-support relative ball, with no fixed global `M`. -/
theorem exists_fullSupport_relativeLocalMaxCandidate_of_strictLexRefinement
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hstarting : Nonempty (CharbonnelRelativeLocalMaxCandidate ω S))
    (hrefine : CharbonnelSection53StrictLexRefinement ω S) :
    ∃ candidate : CharbonnelRelativeLocalMaxCandidate ω S,
      candidate.defectCount = 0 := by
  let Candidate := CharbonnelRelativeLocalMaxCandidate ω S
  let rank : Candidate → ℕ × ℕ := fun c ↦ c.lexRank
  have hwf : WellFounded
      (Prod.Lex (· < ·) (· < ·) on rank) :=
    (wellFounded_lt.prod_lex wellFounded_lt).onFun
  obtain ⟨minimum, _hmem, hminimal⟩ :=
    hwf.has_min (Set.univ : Set Candidate)
      ⟨Classical.choice hstarting, Set.mem_univ _⟩
  refine ⟨minimum, ?_⟩
  by_contra hdefect
  obtain ⟨next, _hsub, hless⟩ := hrefine minimum hdefect
  exact hminimal next (Set.mem_univ _) hless

/-! ## Relative stability and literal-zero assembly -/

/-- The relative interval-separation output of 5.3(b,c) for balls in `ω`:
one relative ball has `M` vertical components, and every contained
positive relative ball has exactly `M` components, mapped bijectively onto
the components of the larger vertical image. -/
def CharbonnelRelativeStableLocalVerticalIntervalSeparation
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∃ candidate : CharbonnelRelativeLocalMaxCandidate ω S,
    ∀ (y : RealEuclidean n), y ∈ ω →
      ∀ (s : ℝ), 0 < s →
        ∀ hsub : charbonnelRelativeClosedBall ω y s ⊆
            charbonnelRelativeClosedBall ω candidate.center candidate.radius,
          charbonnelRelativeLocalVerticalComponentCount ω S y s =
            (candidate.count : ℕ∞) ∧
          Function.Bijective
            (charbonnelVerticalComponentInclusionMap S hsub)

/-- Zero defect and local maximality prove all relative-ball component
and interval consequences. -/
theorem CharbonnelRelativeLocalMaxCandidate.stableIntervalSeparation_of_defect_zero
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S)
    (hzero : candidate.defectCount = 0) :
    CharbonnelRelativeStableLocalVerticalIntervalSeparation ω S := by
  let B := charbonnelRelativeClosedBall ω candidate.center candidate.radius
  have hfull := candidate.fullSupport_of_defect_zero hzero
  refine ⟨candidate, ?_⟩
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

/-- The proved relative incidence bound and only the corrected strict
lexicographic refinement give the relative local stability theorem. -/
theorem literalZeroSet_charbonnelClosure_relativeStableLocalVerticalIntervalSeparation
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hω : ω.Nonempty)
    (hprojection : CharbonnelFullBaseProjection ω S)
    (hrefine : CharbonnelSection53StrictLexRefinement ω S) :
    CharbonnelRelativeStableLocalVerticalIntervalSeparation ω S := by
  have hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S :=
    literalZeroSet_charbonnelClosure_relativeUniformLocalVerticalComponentBound
      hG hsmooth hUFF hS hprojection.1
  obtain ⟨candidate, hzero⟩ :=
    exists_fullSupport_relativeLocalMaxCandidate_of_strictLexRefinement
      (exists_charbonnelRelativeLocalMaxCandidate hω hbound) hrefine
  exact candidate.stableIntervalSeparation_of_defect_zero hzero

end AbelFormalization
