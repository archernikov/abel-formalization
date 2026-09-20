import AbelFormalization.CharbonnelSection53GlobalDichotomy

/-!
# A direct 5.3(c) descent strictly lowers the component count

The candidate `c` lies in the global maximal-count stratum `M_M` and has
minimum defect `δ` there.  If a contained locally maximal ball has a
strictly smaller lexicographic `(M,δ)` rank, its first coordinate must be
smaller.  At equal `M`, the new ball would also be globally maximal, while
minimality of `δ` forbids a smaller defect.  This elementary rank fact keeps
the direct branch of the dichotomy aligned with the paper's smaller-`M`
induction.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

theorem charbonnelSection53_directLexDescent_strictlyLowersCount
    {n : ℕ} {ω : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + 1))}
    (candidate : CharbonnelRelativeMinimalDefectGlobalCandidate ω S)
    (hdescent : CharbonnelSection53LocalLexDescentFrom candidate) :
    ∃ next : CharbonnelRelativeLocalMaxCandidate ω S,
      charbonnelRelativeClosedBall ω next.center next.radius ⊆
        charbonnelRelativeClosedBall ω
          candidate.1.1.center candidate.1.1.radius ∧
      next.count < candidate.1.1.count := by
  obtain ⟨next, hsub, hlex⟩ := hdescent
  change Prod.Lex (· < ·) (· < ·)
      (next.count, next.defectCount)
      (candidate.1.1.count, candidate.1.1.defectCount) at hlex
  refine ⟨next, hsub, ?_⟩
  rcases Prod.lex_iff.mp hlex with hcount | ⟨hcountEq, hdefect⟩
  · change next.count < candidate.1.1.count at hcount
    exact hcount
  · exfalso
    change next.count = candidate.1.1.count at hcountEq
    change next.defectCount < candidate.1.1.defectCount at hdefect
    have hglobal : ∀ (y : RealEuclidean n), y ∈ ω →
        ∀ (s : ℝ), 0 < s →
          charbonnelRelativeLocalVerticalComponentCount ω S y s ≤
            (next.count : ℕ∞) := by
      intro y hy s hs
      have h := candidate.1.2 y hy s hs
      change charbonnelRelativeLocalVerticalComponentCount ω S y s ≤
        (candidate.1.1.count : ℕ∞) at h
      rw [hcountEq]
      exact h
    let nextGlobal : CharbonnelRelativeGlobalMaxCandidate ω S :=
      ⟨next, hglobal⟩
    have hminimum : candidate.1.1.defectCount ≤ next.defectCount :=
      candidate.2 nextGlobal
    exact (lt_irrefl next.defectCount) (hdefect.trans_le hminimum)

end AbelFormalization
