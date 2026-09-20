import AbelFormalization.AbelHermiteFamily
import AbelFormalization.CentralSubstitution
import AbelFormalization.CentralRemainderHolomorphic
import AbelFormalization.CentralThreshold

/-! # The full uniform Hermite interpolation lemma

This assembles the ordinary interpolation family and the central expansion
with a jointly holomorphic, uniformly bounded remainder.  All node and scale
parameters are independent complex variables.  The central identity uses
the actual divided-difference remainder, evaluated at the exponential scale.

The signed-Stirling sum is indexed from zero through `r`. For positive `r`
the zero coefficient vanishes by `signedStirling_zero`, so this is exactly
the manuscript's sum from one through `r`.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

/-- A central function jointly analytic on the half-radius disk is analytic
on the closed quarter-radius disk at each fixed allowed center. -/
theorem centralComplexFunction_analyticOnNhd_quarter {F : ℂ → ℂ} {X : ℝ}
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (rightHalfStrip X 1 ×ˢ ball (0 : ℂ) (1 / 2)))
    {u : ℂ} (hu : u ∈ rightHalfStrip X 1) :
    AnalyticOnNhd ℂ (centralComplexFunction F u) (closedBall (0 : ℂ) (1 / 4)) := by
  intro η hη
  have hηn : ‖η‖ ≤ 1 / 4 := by simpa only [mem_closedBall, dist_zero_right] using hη
  have hηball : η ∈ ball (0 : ℂ) (1 / 2) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  exact (hH (u, η) ⟨hu, hηball⟩).fun_comp
    (f := fun z : ℂ => (u, z)) (analyticAt_const.prod analyticAt_id)

variable {ι : Type*} [Fintype ι]

/-- All conclusions of the uniform Hermite lemma, including its central
parameter family. Complex Abel values are given by the explicit extensions
`branch` and `F`; the central remainder is the specified analytic divided
difference, rather than an additional unspecified function. -/
structure FullHermiteLemmaSpec (A : ℝ → ℝ) (B : ℝ) (m : ι → ℕ)
    (X0 K K0 u0 ε Kr : ℝ) (branch : ℝ → ℂ → ℂ) (F : ℂ → ℂ) : Prop where
  family : AbelHermiteFamilySpec A B m X0 K K0 branch
  centralThreshold_pos : 0 < u0
  parameterRadius_pos : 0 < ε
  remainderConstant_pos : 0 < Kr
  threshold_compatible : X0 < E u0
  exponentialScale_lt_radius : Real.exp (-u0) < ε
  central_extension_analytic : AnalyticOnNhd ℂ F (rightHalfStrip u0 ε)
  central_extension_realAgreement : ∀ u : ℝ, u0 < u → F (u : ℂ) = (A u : ℂ)
  remainder_holomorphic : ∀ r : ℕ, r < totalMultiplicity m →
    DifferentiableOn ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralRemainder F m (1 / 4) v.1.1 v.2 v.1.2 r)
      (centralParameterDomain u0 ε B)
  remainder_bound : ∀ r : ℕ, r < totalMultiplicity m →
    ∀ v ∈ centralParameterDomain (ι := ι) u0 ε B,
      ‖centralRemainder F m (1 / 4) v.1.1 v.2 v.1.2 r‖ ≤ Kr * (1 + v.1.1.re)
  central_identity : ∀ u : ℝ, u0 < u → ∀ δ ∈ hermiteNodeNeighborhood B,
    ∀ r : ℕ, 1 ≤ r → r < totalMultiplicity m →
      abelHermiteCoeff branch B m (E u) δ r = (Real.exp (-u) : ℂ) ^ r *
        ((∑ j ∈ Finset.range (r + 1), (signedStirling r j : ℂ) *
          ((iteratedDeriv j A u : ℝ) : ℂ)) +
          (Real.exp (-u) : ℂ) *
            centralRemainder F m (1 / 4) (u : ℂ) (Real.exp (-u) : ℂ) δ r)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- The full Hermite interpolation lemma holds uniformly for every positive
node-radius bound and every finite family of multiplicities with positive
total degree. No distinctness hypothesis is imposed on the nodes. -/
theorem exists_hermiteLemma {B : ℝ} (hB : 0 < B) (m : ι → ℕ)
    (hd : 0 < totalMultiplicity m) :
    ∃ X0 K K0 u0 ε Kr : ℝ, ∃ branch : ℝ → ℂ → ℂ, ∃ F : ℂ → ℂ,
      FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F := by
  obtain ⟨X0, K, K0, branch, hfamily⟩ := hA.exists_abelHermiteFamily hB m hd
  obtain ⟨U, Kc, F, hU, hKc, hF, heF, hH, hHbound⟩ :=
    hA.exists_bounded_centralComplexFunction
  obtain ⟨D, hD, hrem⟩ := exists_uniform_centralCoefficient_remainder_bounds m hB
  have hqStar : 0 < centralScaleRadius B := centralScaleRadius_pos hB
  let ε : ℝ := min (1 / 2) (centralScaleRadius B / 4)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hqStar (by norm_num))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεone : ε ≤ 1 := by linarith
  have hεqhalf : ε < centralScaleRadius B / 2 := by
    have hh : ε ≤ centralScaleRadius B / 4 := min_le_right _ _
    linarith
  have hεq : ε < centralScaleRadius B :=
    hεqhalf.trans (half_lt_self hqStar)
  obtain ⟨u0, hu0, hUu0, htail⟩ := exists_central_threshold X0 U B hε hB
  let Kr : ℝ := 2 * D * Kc / centralScaleRadius B
  have hKr : 0 < Kr := div_pos (mul_pos (mul_pos (by norm_num) hD) hKc) hqStar
  have hstrip : rightHalfStrip u0 ε ⊆ rightHalfStrip U 1 := by
    intro u hu
    exact ⟨hUu0.trans hu.1, hu.2.trans_le hεone⟩
  have hquarter : ∀ u ∈ rightHalfStrip U 1,
      AnalyticOnNhd ℂ (centralComplexFunction F u) (closedBall (0 : ℂ) (1 / 4)) :=
    fun _ hu => centralComplexFunction_analyticOnNhd_quarter hH hu
  obtain ⟨_, _, hEX0, hExp0, _⟩ := htail u0 le_rfl
  refine ⟨X0, K, K0, u0, ε, Kr, branch, F, {
    family := hfamily
    centralThreshold_pos := hu0
    parameterRadius_pos := hε
    remainderConstant_pos := hKr
    threshold_compatible := hEX0
    exponentialScale_lt_radius := hExp0
    central_extension_analytic := hF.mono hstrip
    central_extension_realAgreement := fun u hu => heF u (hUu0.trans hu)
    remainder_holomorphic := ?_
    remainder_bound := ?_
    central_identity := ?_ }⟩
  · intro r hr
    exact centralRemainder_differentiableOn_domain hB hH m hr hUu0.le hεone hεqhalf.le
  · intro r hr v hv
    have huv : v.1.1 ∈ rightHalfStrip U 1 := hstrip hv.1.1
    have hupos : 0 < v.1.1.re := hu0.trans hv.1.1.1
    have hqv : ‖v.2‖ < centralScaleRadius B := by
      have hqε : ‖v.2‖ < ε := by simpa only [mem_ball, dist_zero_right] using hv.2
      exact hqε.trans hεq
    exact ((hrem F Kc v.1.1 v.1.2 hKc hupos (hquarter _ huv)
      (hHbound _ huv) (fun i => (hv.1.2 i).le) r hr).2 v.2 hqv).2
  · intro u hu δ hδ r hr hrd
    obtain ⟨hupos, hUu, hEX, _, hscale⟩ := htail u hu.le
    have huc : (u : ℂ) ∈ rightHalfStrip U 1 := by
      exact ⟨hUu, by simp⟩
    have hFat : AnalyticAt ℂ F (u : ℂ) := hF _ huc
    have hGat : AnalyticAt ℂ (branch (E u)) (E u : ℂ) :=
      hfamily.branch_analytic (E u) hEX _ (mem_ball_self (by linarith : 0 < B + 2))
    have heFgerm : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hUu] with y hy
      exact heF y hy
    have heGgerm : (fun y : ℝ => branch (E u) (y : ℂ)) =ᶠ[𝓝 (E u)]
        fun y => (A y : ℂ) := by
      filter_upwards [ball_mem_nhds (E u) (by linarith : 0 < B + 2)] with y hy
      exact hfamily.branch_realAgreement (E u) hEX y hy
    have hnodes : ∀ i, δ i ∈ ball (0 : ℂ) (B + 1) := by
      intro i
      have hi := hδ i
      simp only [mem_ball, dist_zero_right]
      linarith
    exact hA.normalizedHermiteCoeff_stirling_remainder δ m hupos
      (by linarith : 0 < B + 1) hFat hGat heFgerm heGgerm
      (hfamily.shifted_analytic (E u) hEX) (hquarter _ huc) hscale hnodes hr hrd

end IsAbel
end AbelFormalization
