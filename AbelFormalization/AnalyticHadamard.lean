import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Group.Constructions

/-! # Analytic Hadamard decomposition

An analytic function minus its value at the origin factors through the input
by an analytic family of continuous linear maps. The construction shifts its
genuinely convergent multilinear power series; it does not use a smooth
factorization or assume convergence of a formal series.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Analytic Hadamard factorization in a normed space: the factor itself is
analytic with values in continuous linear maps. -/
theorem analyticAt_exists_sub_eq_linear {f : E → F} (hf : AnalyticAt 𝕜 f 0) :
    ∃ G : E → E →L[𝕜] F, AnalyticAt 𝕜 G 0 ∧
      ∀ᶠ x in 𝓝 (0 : E), f x - f 0 = G x x := by
  obtain ⟨p, r, hp⟩ := hf
  have hspos : 0 < p.shift.radius := by
    rw [FormalMultilinearSeries.radius_shift]
    exact hp.radius_pos
  have hs := p.shift.hasFPowerSeriesOnBall hspos
  refine ⟨p.shift.sum, hs.analyticAt, ?_⟩
  filter_upwards [Metric.eball_mem_nhds (0 : E) hp.r_pos] with x hx
  have hsum := (hasSum_nat_add_iff' 1).mpr (hp.hasSum hx)
  have hxs : x ∈ Metric.eball (0 : E) p.shift.radius := by
    rw [FormalMultilinearSeries.radius_shift]
    exact Metric.eball_subset_eball hp.r_le hx
  have hev := (ContinuousLinearMap.apply 𝕜 F x).hasSum (hs.hasSum hxs)
  have hc : ∀ n : ℕ, p.shift n (fun _ => x) x = p (n + 1) (fun _ => x) := by
    intro n
    simp only [FormalMultilinearSeries.shift, ContinuousMultilinearMap.curryRight_apply]
    congr 1
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
  simp only [Finset.sum_range_one, hp.coeff_zero, zero_add] at hsum
  change HasSum (fun n => p.shift n (fun _ => x) x) (p.shift.sum (0 + x) x) at hev
  simp only [hc, zero_add] at hev
  exact hsum.unique hev

/-- In finitely many coordinates, the analytic factors of Hadamard's lemma
are scalar-valued analytic functions on one common neighborhood. -/
theorem analyticAt_exists_sub_eq_sum_coordinates [CompleteSpace 𝕜] {ι : Type*} [Fintype ι]
    {f : (ι → 𝕜) → 𝕜} (hf : AnalyticAt 𝕜 f 0) :
    ∃ g : ι → (ι → 𝕜) → 𝕜, (∀ i, AnalyticAt 𝕜 (g i) 0) ∧
      ∀ᶠ x in 𝓝 (0 : ι → 𝕜), f x - f 0 = ∑ i, x i * g i x := by
  classical
  obtain ⟨G, hG, hEq⟩ := analyticAt_exists_sub_eq_linear hf
  refine ⟨fun i x => G x (Pi.single i 1), ?_, ?_⟩
  · intro i
    exact ((ContinuousLinearMap.apply 𝕜 𝕜 (Pi.single i 1)).analyticAt (G 0)).comp hG
  · filter_upwards [hEq] with x hx
    rw [hx]
    conv_lhs => arg 2; rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have he : Pi.single i (x i) = x i • Pi.single i (1 : 𝕜) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp
      · simp [hj]
    rw [he, map_smul, smul_eq_mul]

end AbelFormalization
