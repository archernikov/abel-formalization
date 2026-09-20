import AbelFormalization.CharbonnelSection53RelativeLexDescent

/-!
# Charbonnel 5.3(c): the global `(M, δ)` stratum

The proof in the paper starts with the largest component count `M` among
positive balls in the compact base `ω`.  It then minimizes the defect `δ`
among **those** balls with count `M`.  When `δ > 0`, the lexicographic
induction either passes to a smaller rank on a restricted base or, at the
same rank, constructs a nested sequence of balls avoiding the defective
component supports.  The source's weak-structure tameness and compact
limiting-fiber argument rule out that stationary sequence.  Compactness and
the numerical vertical-ball count alone do not: a compact dense-spike set
has a stationary rank `(2,1)` on every ball while horizontal affine sections
have unbounded component counts.

Concretely, enumerate a dense subset of `[0,1]` without repetitions as
`q₁,q₂,...`, put `a_m = 3⁻ᵐ` and
`K_m = [0,a_m] ∪ [2a_m,3a_m]`, and let
`S = ([0,1] × {0}) ∪ ⋃_m ({q_m} × K_m)`.
Because `K_{m+1} ⊆ [0,a_m]` and `K_m → {0}`, `S` is compact.  Every
positive relative ball sees exactly `K_j` for the least `j` with `q_j` in
the ball, so its count/defect rank is always `(2,1)`.  At height
`t_m = (5/2)a_m`, the horizontal section is precisely
`{q₁,...,q_m}`: `t_m ∈ K_j` for `j ≤ m` and `t_m ∉ K_j` for `j > m`.
This proves the affine-section component counts are unbounded.

This module records the paper's global stratum and the stationary sequence
with relative balls.  It proves the elementary existence and compactness
bridges.  The chain construction and its exclusion are named as separate
properties, rather than inferred from the stronger candidatewise premise in
`CharbonnelSection53RelativeLexDescent`.
-/

noncomputable section

open Set Function Filter
open scoped Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Closed component supports -/

/-- For a compact `S` and closed base `B`, the base support of a vertical
component is compact.  This is the projected compact intersection used when
the source forms its finite union `β_{x,ε}` of incomplete supports. -/
theorem charbonnelVerticalComponentBaseSupport_isCompact
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : IsCompact S) {B : Set (RealEuclidean n)}
    (hB : IsClosed B)
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S B : Set ℝ)) :
    IsCompact (charbonnelVerticalComponentBaseSupport S B c) := by
  let I : Set ℝ :=
    realConnectedComponentCarrier (charbonnelVerticalImageOver S B) c
  let K : Set (RealEuclidean (n + 1)) :=
    S ∩ charbonnelVerticalBaseCoordinate ⁻¹' B ∩
      charbonnelVerticalLastCoordinate ⁻¹' I
  have hI : IsCompact I :=
    realConnectedComponentCarrier_isCompact_of_isCompact
      (charbonnelVerticalImageOver_isCompact hS hB) c
  have hK : IsCompact K := by
    exact
      (hS.inter_right
        (hB.preimage continuous_charbonnelVerticalBaseCoordinate)).inter_right
          (hI.isClosed.preimage
            continuous_charbonnelVerticalLastCoordinate)
  have hImage :
      charbonnelVerticalComponentBaseSupport S B c =
        charbonnelVerticalBaseCoordinate '' K := by
    ext x
    constructor
    · rintro ⟨hxB, t, htI, hxtS⟩
      refine ⟨charbonnelAppendLastCoordinate x t, ?_, ?_⟩
      · refine ⟨⟨hxtS, ?_⟩, ?_⟩
        · change realEuclideanTakeLeft
            (charbonnelAppendLastCoordinate x t) ∈ B
          simpa only [charbonnelAppendLastCoordinate,
            realEuclideanTakeLeft_append] using hxB
        · change charbonnelAppendLastCoordinate x t (Fin.last n) ∈ I
          simpa only [charbonnelAppendLastCoordinate_last] using htI
      · change realEuclideanTakeLeft
          (charbonnelAppendLastCoordinate x t) = x
        simp only [charbonnelAppendLastCoordinate,
          realEuclideanTakeLeft_append]
    · rintro ⟨z, ⟨⟨hzS, hzB⟩, hzI⟩, rfl⟩
      refine ⟨hzB, charbonnelVerticalLastCoordinate z, hzI, ?_⟩
      simpa only [charbonnelVerticalBaseCoordinate,
        charbonnelVerticalLastCoordinate,
        charbonnelAppendLastCoordinate_takeLeft_last] using hzS
  rw [hImage]
  exact hK.image continuous_charbonnelVerticalBaseCoordinate

theorem charbonnelVerticalComponentBaseSupport_isClosed
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : IsCompact S) {B : Set (RealEuclidean n)}
    (hB : IsClosed B)
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S B : Set ℝ)) :
    IsClosed (charbonnelVerticalComponentBaseSupport S B c) :=
  (charbonnelVerticalComponentBaseSupport_isCompact hS hB c).isClosed

/-! ## The weak-structure bound needed beyond compactness -/

/-- Charbonnel's WS5 bound for **all** affine sections of the source set.
The compact dense-spike example with stable vertical count two fails this
condition on horizontal lines, so it cannot be omitted from a source proof
of the stationary-sequence contradiction. -/
def CharbonnelUniformAffineSectionComponentBound {d : ℕ}
    (S : Set (RealEuclidean d)) : Prop :=
  ∃ N : ℕ, ∀ V : AffineSubspace ℝ (RealEuclidean d),
    ENat.card (ConnectedComponents
      ((S ∩ (V : Set (RealEuclidean d))) : Set (RealEuclidean d))) ≤
        (N : ℕ∞)

/-- Literal-zero Charbonnel members have the full WS5 affine-section bound,
which rules out the compact dense-spike obstruction. -/
theorem literalZeroSet_charbonnelClosure_uniformAffineSectionComponentBound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {d : ℕ} {S : Set (RealEuclidean d)}
    (hd : 0 < d)
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) d) :
    CharbonnelUniformAffineSectionComponentBound S :=
  literalZeroSet_charbonnelClosure_ws5_affineSections
    hG hsmooth hUFF hd hS

/-! ## The global maximum and minimum defect -/

/-- The source's stratum `M_M`: a positive relative ball attaining the
largest local vertical component count among *all* balls in `ω`. -/
def CharbonnelRelativeGlobalMaxCandidate {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Type :=
  {candidate : CharbonnelRelativeLocalMaxCandidate ω S //
    ∀ (y : RealEuclidean n), y ∈ ω →
      ∀ (s : ℝ), 0 < s →
        charbonnelRelativeLocalVerticalComponentCount ω S y s ≤
          (candidate.count : ℕ∞)}

/-- Boundedness from 5.3(a) guarantees that `M_M` is nonempty. -/
theorem exists_charbonnelRelativeGlobalMaxCandidate
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : ω.Nonempty)
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S) :
    Nonempty (CharbonnelRelativeGlobalMaxCandidate ω S) := by
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
  let candidate : CharbonnelRelativeLocalMaxCandidate ω S := {
    center := p.1.1
    center_mem := p.2.1
    radius := p.1.2
    radius_pos := p.2.2
    count := M
    count_eq := hp
    locally_maximal := by
      intro y hy s hs _hsub
      exact hmax ⟨(y, s), ⟨hy, hs⟩⟩ }
  refine ⟨⟨candidate, ?_⟩⟩
  intro y hy s hs
  exact hmax ⟨(y, s), ⟨hy, hs⟩⟩

/-- Every ball in the global-maximal stratum has the same component count
`M`, expressed as an equality in `ℕ∞`. -/
theorem charbonnelRelativeGlobalMaxCandidates_count_eq
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (a b : CharbonnelRelativeGlobalMaxCandidate ω S) :
    (a.1.count : ℕ∞) = (b.1.count : ℕ∞) := by
  apply le_antisymm
  · have h := b.2 a.1.center a.1.center_mem
        a.1.radius a.1.radius_pos
    rw [a.1.count_eq] at h
    exact h
  · have h := a.2 b.1.center b.1.center_mem
        b.1.radius b.1.radius_pos
    rw [b.1.count_eq] at h
    exact h

/-- The minimum of the finite-valued defect function on the global-maximum
stratum; this is the source's integer `δ`. -/
def CharbonnelRelativeMinimalDefectGlobalCandidate {n : ℕ}
    (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Type :=
  {candidate : CharbonnelRelativeGlobalMaxCandidate ω S //
    ∀ other : CharbonnelRelativeGlobalMaxCandidate ω S,
      candidate.1.defectCount ≤ other.1.defectCount}

theorem exists_charbonnelRelativeMinimalDefectGlobalCandidate
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hstarting : Nonempty (CharbonnelRelativeGlobalMaxCandidate ω S)) :
    Nonempty (CharbonnelRelativeMinimalDefectGlobalCandidate ω S) := by
  let Global := CharbonnelRelativeGlobalMaxCandidate ω S
  let defect : Global → ℕ := fun candidate ↦ candidate.1.defectCount
  have hwf : WellFounded ((· < ·) on defect) :=
    wellFounded_lt.onFun
  obtain ⟨minimum, _hmem, hminimal⟩ :=
    hwf.has_min (Set.univ : Set Global)
      ⟨Classical.choice hstarting, Set.mem_univ _⟩
  refine ⟨⟨minimum, ?_⟩⟩
  intro other
  have hnot : ¬ defect other < defect minimum :=
    hminimal other (Set.mem_univ _)
  dsimp [defect] at hnot
  omega

/-- All globally minimal-defect balls share the source's integer `δ`. -/
theorem charbonnelRelativeMinimalDefectGlobalCandidates_defect_eq
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (a b : CharbonnelRelativeMinimalDefectGlobalCandidate ω S) :
    a.1.1.defectCount = b.1.1.defectCount :=
  le_antisymm (a.2 b.1) (b.2 a.1)

/-! ## The stationary nested-ball obstruction in 5.3(c) -/

/-- The union `β` of the base supports of the components whose supports
are proper subsets of this relative ball. -/
def charbonnelRelativeDefectiveSupportUnion
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S) :
    Set (RealEuclidean n) :=
  ⋃ c : ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ),
    if charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c =
          charbonnelRelativeClosedBall ω candidate.center candidate.radius then
      (∅ : Set (RealEuclidean n))
    else
      charbonnelVerticalComponentBaseSupport S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) c

/-- Finite component count and compactness make the defective-support union
closed.  Its complement is the relative open region used for the next ball
in the stationary-sequence construction. -/
theorem charbonnelRelativeDefectiveSupportUnion_isClosed
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω) (hS : IsCompact S)
    (candidate : CharbonnelRelativeLocalMaxCandidate ω S) :
    IsClosed (charbonnelRelativeDefectiveSupportUnion candidate) := by
  letI : Finite (ConnectedComponents
      (charbonnelVerticalImageOver S
        (charbonnelRelativeClosedBall ω candidate.center candidate.radius) : Set ℝ)) :=
    ENat.card_lt_top.mp (candidate.count_eq.trans_lt (by simp))
  unfold charbonnelRelativeDefectiveSupportUnion
  apply isClosed_iUnion_of_finite
  intro c
  split_ifs
  · exact isClosed_empty
  · exact charbonnelVerticalComponentBaseSupport_isClosed hS
      (charbonnelRelativeClosedBall_isClosed hω.isClosed
        candidate.center candidate.radius) c

/-- Exactly the sequence excluded in 5.3(c), now indexed by global-maximal,
minimal-defect relative balls.  Each next ball lies inside the previous
ball after deleting its incomplete component supports, and radii shrink to
zero. -/
def CharbonnelSection53StationaryNestedSequence
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∃ sequence : ℕ → CharbonnelRelativeMinimalDefectGlobalCandidate ω S,
    (sequence 0).1.1.defectCount ≠ 0 ∧
    (∀ k : ℕ,
      charbonnelRelativeClosedBall ω
          (sequence (k + 1)).1.1.center
          (sequence (k + 1)).1.1.radius ⊆
        charbonnelRelativeClosedBall ω
            (sequence k).1.1.center (sequence k).1.1.radius \
          charbonnelRelativeDefectiveSupportUnion (sequence k).1.1) ∧
    Tendsto (fun k : ℕ ↦ (sequence k).1.1.radius) atTop (nhds 0)

/-- The stationary-sequence exclusion asserted in the paper for members of
its weak set structure.  Compactness and finite limiting-fiber components
alone do not establish it: the dense-spike example above has both, yet a
same-rank chain can converge to a one-component fiber.  The missing
neighborhood/component stabilization remains explicit. -/
def CharbonnelSection53NoStationaryNestedSequence
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ¬ CharbonnelSection53StationaryNestedSequence ω S

/-- A concrete missing bridge from the stationary chain to WS5: every
finite bound is exceeded by the component count of some affine section of
`S`.  The compact dense-spike example exhibits exactly this phenomenon on
horizontal lines.  Proving this implication for source members would turn
the paper's nested-ball contradiction into a direct WS5 contradiction. -/
def CharbonnelSection53StationaryForcesAffineExplosion
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  CharbonnelSection53StationaryNestedSequence ω S →
    ∀ N : ℕ,
      ∃ V : AffineSubspace ℝ (RealEuclidean (n + 1)),
        (N : ℕ∞) < ENat.card (ConnectedComponents
          ((S ∩ (V : Set (RealEuclidean (n + 1)))) :
            Set (RealEuclidean (n + 1))))

/-- Once the chain-to-affine-section bridge is available, the already
formalized WS5 bound excludes the stationary chain. -/
theorem charbonnelSection53_noStationary_of_affineExplosion
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hws5 : CharbonnelUniformAffineSectionComponentBound S)
    (hexplosion : CharbonnelSection53StationaryForcesAffineExplosion ω S) :
    CharbonnelSection53NoStationaryNestedSequence ω S := by
  intro hchain
  obtain ⟨N, hN⟩ := hws5
  obtain ⟨V, hgt⟩ := hexplosion hchain N
  exact (lt_irrefl (N : ℕ∞)) (hgt.trans_le (hN V))

/-- A source-shaped implication isolating the unfinished 5.3(c) analytic
step.  The antecedents record the compact set, its compact full-projection
base, WS5 on all affine sections, and the proved 5.3(a) relative incidence
bound.  The consequent is exactly the stationary nested-ball exclusion.
No proof of this implication is asserted here. -/
def CharbonnelSection53WS5StationaryExclusion
    {n : ℕ} (ω : Set (RealEuclidean n))
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  IsCompact ω → IsCompact S →
    CharbonnelFullBaseProjection ω S →
    CharbonnelUniformAffineSectionComponentBound S →
    CharbonnelRelativeUniformLocalVerticalComponentBound ω S →
      CharbonnelSection53NoStationaryNestedSequence ω S

theorem charbonnelSection53_ws5StationaryExclusion_of_affineExplosion
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hexplosion : CharbonnelSection53StationaryForcesAffineExplosion ω S) :
    CharbonnelSection53WS5StationaryExclusion ω S := by
  intro _hωcompact _hScompact _hprojection hws5 _hrelative
  exact charbonnelSection53_noStationary_of_affineExplosion
    hws5 hexplosion

/-- For literal-zero closure members, WS5 and the moving-ball incidence
bound are already formalized.  The only extra input in this assembly is the
explicit stationary-exclusion implication for the compact source set. -/
theorem literalZeroSet_charbonnelClosure_noStationaryNestedSequence_of_ws5Exclusion
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hωcompact : IsCompact ω)
    (hScompact : IsCompact S)
    (hprojection : CharbonnelFullBaseProjection ω S)
    (hexclusion : CharbonnelSection53WS5StationaryExclusion ω S) :
    CharbonnelSection53NoStationaryNestedSequence ω S := by
  have hws5 : CharbonnelUniformAffineSectionComponentBound S :=
    literalZeroSet_charbonnelClosure_uniformAffineSectionComponentBound
      hG hsmooth hUFF (by omega) hS
  have hrelative :
      CharbonnelRelativeUniformLocalVerticalComponentBound ω S :=
    literalZeroSet_charbonnelClosure_relativeUniformLocalVerticalComponentBound
      hG hsmooth hUFF hS hprojection.1
  exact hexclusion hωcompact hScompact hprojection hws5 hrelative

end AbelFormalization
