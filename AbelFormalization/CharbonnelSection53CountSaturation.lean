import AbelFormalization.CharbonnelSection53GlobalDichotomy

/-!
# Count saturation in Charbonnel 5.3(c)

The local choice in the printed proof has three logically separate parts.
One must find a relative ball avoiding the current defective supports,
recover the globally maximal component count `M` there if direct descent
does not occur, and then preserve the minimum defect `δ` while shrinking
the radius.  The first part is already proved in
`CharbonnelSection53GlobalDichotomy` from closed supports and the relative
5.3(a) incidence bound.  This module proves the second part.

The resulting successor is in the global `M` stratum, and its defect is at
least the global minimum `δ`.  Equality of defects and a numerical radius
bound are not inferred from WS5 here; they are exactly the further content
needed for `CharbonnelSection53NoDescentSuccessorChoice`.  Likewise no
stationary-chain-to-affine-section explosion is claimed.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- A local maximum contained in a globally minimal-defect candidate has
count at most the source's global `M`.  If direct lexicographic descent is
absent, the count must be exactly `M`: a smaller first rank coordinate
would itself be a direct descent, regardless of the new defect. -/
theorem charbonnelSection53_count_eq_of_noLocalLexDescent
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hnoDescent : ¬ CharbonnelSection53LocalLexDescentFrom candidate)
    (next : CharbonnelRelativeLocalMaxCandidate ω S)
    (hsub : charbonnelRelativeClosedBall ω next.center next.radius ⊆
      charbonnelRelativeClosedBall ω
        candidate.1.1.center candidate.1.1.radius) :
    next.count = candidate.1.1.count := by
  have hle : (next.count : ℕ∞) ≤
      (candidate.1.1.count : ℕ∞) := by
    rw [← next.count_eq]
    exact candidate.1.2 next.center next.center_mem
      next.radius next.radius_pos
  have hleNat : next.count ≤ candidate.1.1.count := by
    simpa only [ENat.natCast_le_natCast] using hle
  by_contra hne
  have hlt : next.count < candidate.1.1.count :=
    lt_of_le_of_ne hleNat hne
  apply hnoDescent
  refine ⟨next, hsub, ?_⟩
  change Prod.Lex (· < ·) (· < ·)
    (next.count, next.defectCount)
    (candidate.1.1.count, candidate.1.1.defectCount)
  exact Prod.lex_iff.mpr (Or.inl hlt)

/-- A local maximum with count `M` belongs to the global-maximal stratum.
This promotion uses the candidate's global upper bound, not local topology. -/
def charbonnelSection53_globalCandidate_of_equalCount
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (next : CharbonnelRelativeLocalMaxCandidate ω S)
    (hcount : next.count = candidate.1.1.count) :
    CharbonnelRelativeGlobalMaxCandidate ω S :=
  ⟨next, by
    intro y hy s hs
    have hglobal := candidate.1.2 y hy s hs
    simpa only [← hcount] using hglobal⟩

/-- If an interior point of the current relative ball survives deletion of
its closed defective supports, then the proved 5.3(a) bound chooses a ball
inside the survivor region.  Failure of direct descent forces its count
to be the same global `M`; minimality of `δ` gives the exact inequality
`δ ≤ defect(next)`.  This is the maximal-count portion of the successor
choice in 5.3(c). -/
theorem charbonnelSection53_exists_badAvoiding_globalMax_of_noDescent
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hω : IsCompact ω) (hS : IsCompact S)
    (hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S)
    (candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hnoDescent : ¬ CharbonnelSection53LocalLexDescentFrom candidate)
    {x : RealEuclidean n}
    (hxω : x ∈ ω)
    (hxinner : x ∈ Metric.ball
      candidate.1.1.center candidate.1.1.radius)
    (hxβ : x ∉ charbonnelRelativeDefectiveSupportUnion candidate.1.1) :
    ∃ next : CharbonnelRelativeGlobalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω next.1.center next.1.radius ⊆
        charbonnelRelativeClosedBall ω
          candidate.1.1.center candidate.1.1.radius \
            charbonnelRelativeDefectiveSupportUnion candidate.1.1 ∧
      candidate.1.1.defectCount ≤ next.1.defectCount := by
  obtain ⟨nextLocal, hsub, _hle⟩ :=
    exists_badAvoiding_localMax_count_le hω hS hbound
      candidate.1.1 hxω hxinner hxβ
  have hinside : charbonnelRelativeClosedBall ω
      nextLocal.center nextLocal.radius ⊆
      charbonnelRelativeClosedBall ω
        candidate.1.1.center candidate.1.1.radius :=
    hsub.trans Set.sdiff_subset
  have hcount : nextLocal.count = candidate.1.1.count :=
    charbonnelSection53_count_eq_of_noLocalLexDescent
      candidate hnoDescent nextLocal hinside
  let next : CharbonnelRelativeGlobalMaxCandidate ω S :=
    charbonnelSection53_globalCandidate_of_equalCount
      candidate nextLocal hcount
  exact ⟨next, hsub, candidate.2 next⟩

/-- For literal-zero closure members, WS5 on the moving-ball incidence
set has already supplied the relative 5.3(a) bound.  The theorem additionally
uses compactness, full base projection, failure of direct descent, and an
interior point outside the defective-support union. -/
theorem literalZeroSet_charbonnelClosure_exists_badAvoiding_globalMax_of_noDescent
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (hclosure : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hω : IsCompact ω) (hS : IsCompact S)
    (hprojection : CharbonnelFullBaseProjection ω S)
    (candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hnoDescent : ¬ CharbonnelSection53LocalLexDescentFrom candidate)
    {x : RealEuclidean n}
    (hxω : x ∈ ω)
    (hxinner : x ∈ Metric.ball
      candidate.1.1.center candidate.1.1.radius)
    (hxβ : x ∉ charbonnelRelativeDefectiveSupportUnion candidate.1.1) :
    ∃ next : CharbonnelRelativeGlobalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω next.1.center next.1.radius ⊆
        charbonnelRelativeClosedBall ω
          candidate.1.1.center candidate.1.1.radius \
            charbonnelRelativeDefectiveSupportUnion candidate.1.1 ∧
      candidate.1.1.defectCount ≤ next.1.defectCount := by
  have hbound : CharbonnelRelativeUniformLocalVerticalComponentBound ω S :=
    literalZeroSet_charbonnelClosure_relativeUniformLocalVerticalComponentBound
      hG hsmooth hUFF hclosure hprojection.1
  exact charbonnelSection53_exists_badAvoiding_globalMax_of_noDescent
    hω hS hbound candidate hnoDescent hxω hxinner hxβ

end AbelFormalization
