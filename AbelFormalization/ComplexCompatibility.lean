import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith

/-! # Compatibility of complex analytic extensions

Complex analytic functions agreeing on a real interval agree on a connected
complex domain containing that interval. In particular, extensions of the same
real function on disks centered on the real axis agree wherever the disks meet.
-/

open Set Metric

namespace AbelFormalization

/-- Real agreement on an open preconnected complex domain containing a real
point determines a complex analytic function uniquely. -/
theorem analytic_eqOn_of_real_agreement {F G : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hU : IsOpen U) (hc : IsPreconnected U) {a : ℝ} (ha : (a : ℂ) ∈ U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → F (t : ℂ) = G (t : ℂ)) :
    EqOn F G U := by
  apply hF.eqOn_of_preconnected_of_mem_closure hG hc ha
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU (a : ℂ) ha
  let d : ℝ := min δ ε / 2
  have hd : 0 < d := div_pos (lt_min hδ hε) (by norm_num)
  have hdδ : d < δ := by
    have hh := min_le_left δ ε
    dsimp [d]
    linarith
  have hdε : d < ε := by
    have hh := min_le_right δ ε
    dsimp [d]
    linarith
  have hdist : dist (a : ℂ) ((a + d : ℝ) : ℂ) = d := by
    rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    rw [show a - (a + d) = -d by ring, abs_neg, abs_of_pos hd]
  have htU : ((a + d : ℝ) : ℂ) ∈ U := by
    apply hδU
    rw [Metric.mem_ball, dist_comm, hdist]
    exact hdδ
  have hne : ((a + d : ℝ) : ℂ) ≠ (a : ℂ) := by
    intro he
    have hh := Complex.ofReal_injective he
    linarith
  refine ⟨((a + d : ℝ) : ℂ), ⟨hreal (a + d) htU, ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff] using hne
  · simpa only [hdist] using hdε

/-- Projection onto the real axis stays in a disk whose center is real. -/
theorem realPart_mem_ball {z : ℂ} {x r : ℝ} (hz : z ∈ ball (x : ℂ) r) :
    (z.re : ℂ) ∈ ball (x : ℂ) r := by
  change dist (z.re : ℂ) (x : ℂ) < r
  calc
    dist (z.re : ℂ) (x : ℂ) = |z.re - x| := by
      rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    _ ≤ ‖z - (x : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using
        Complex.abs_re_le_norm (z - (x : ℂ))
    _ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz

/-- Two complex analytic extensions of one real function on disks centered on
the real axis agree on their entire overlap. Empty overlaps are included. -/
theorem analytic_extensions_eqOn_inter {f : ℝ → ℝ} {F G : ℂ → ℂ}
    {x y r s : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball (x : ℂ) r))
    (hG : AnalyticOnNhd ℂ G (ball (y : ℂ) s))
    (hFr : ∀ t : ℝ, t ∈ ball x r → F (t : ℂ) = (f t : ℂ))
    (hGr : ∀ t : ℝ, t ∈ ball y s → G (t : ℂ) = (f t : ℂ)) :
    EqOn F G (ball (x : ℂ) r ∩ ball (y : ℂ) s) := by
  intro z hz
  have ha : (z.re : ℂ) ∈ ball (x : ℂ) r ∩ ball (y : ℂ) s :=
    ⟨realPart_mem_ball hz.1, realPart_mem_ball hz.2⟩
  have he := analytic_eqOn_of_real_agreement
    (hF.mono inter_subset_left) (hG.mono inter_subset_right)
    (isOpen_ball.inter isOpen_ball)
    ((convex_ball (x : ℂ) r).inter (convex_ball (y : ℂ) s)).isPreconnected ha
    (fun t ht => by
      have htx : t ∈ ball x r := by
        simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using ht.1
      have hty : t ∈ ball y s := by
        simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using ht.2
      exact (hFr t htx).trans (hGr t hty).symm)
  exact he hz

end AbelFormalization
