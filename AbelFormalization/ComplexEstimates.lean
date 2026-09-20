import AbelFormalization.CompactComplexExtension
import AbelFormalization.ComplexLogIterates
import AbelFormalization.LogBound
import AbelFormalization.ComplexCompatibility

/-!
# Bounded holomorphic extensions on fixed-radius disks near infinity

Local branches on a compact fundamental interval are pulled back by iterated
principal logarithms. The orbit index is bounded by the Abel value, so the
real logarithmic bound also controls the complex extension.
-/

noncomputable section

namespace AbelFormalization.IsAbel

open Set Function Filter Metric
open scoped Topology

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem bounded_complex_extension_of_logarithms {x u ρ M C : ℝ} (n : ℕ)
    (hMx : M ≤ x) (hbase : BoundedComplexExtension A u ρ C)
    (ha : AnalyticOnNhd ℂ (complexL^[n]) (ball (x : ℂ) M))
    (hm : MapsTo (complexL^[n]) (ball (x : ℂ) M) (ball (u : ℂ) ρ)) :
    BoundedComplexExtension A x M ((n : ℝ) + C) := by
  obtain ⟨F, hF, he, hb⟩ := hbase
  refine ⟨fun z => (n : ℂ) + F (complexL^[n] z),
    analyticOnNhd_const.add (hF.comp ha hm), ?_, ?_⟩
  · intro y hy
    have hypos : 0 < y := by
      have hd : |y - x| < M := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hy
      have hl := (abs_lt.mp hd).1
      linarith
    have hyc : (y : ℂ) ∈ ball (x : ℂ) M := by
      simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using hy
    have hmem := hm hyc
    rw [complexL_iterate_ofReal hypos] at hmem
    have hreal : L^[n] y ∈ ball u ρ := by
      simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using hmem
    change (n : ℂ) + F (complexL^[n] (y : ℂ)) = (A y : ℂ)
    rw [complexL_iterate_ofReal hypos, he _ hreal,
      hA.abel_L_iterate hypos n]
    push_cast
    ring
  · intro z hz
    have h := norm_add_le (n : ℂ) (F (complexL^[n] z))
    have hn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    rw [hn] at h
    exact h.trans (add_le_add (le_refl _) (hb _ (hm hz)))

/-- On any fixed-radius disk about a sufficiently large real number, there
is a holomorphic extension bounded by a constant times the logarithm of the
center. -/
theorem eventually_bounded_complex_extension {M : ℝ} (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      BoundedComplexExtension A x M (K * Real.log x) := by
  obtain ⟨ρ₀, hρ₀, C, hC, hbranches⟩ :=
    hA.uniform_complex_extensions_fundamental (U := 1) zero_lt_one
  let ρ : ℝ := min ρ₀ 1
  have hρ : 0 < ρ := lt_min hρ₀ zero_lt_one
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  obtain ⟨R, D, hR, hlog⟩ := hA.exists_log_upper_bound
  refine ⟨1 + |D + C|, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop M,
    eventually_ge_atTop (M + M / ρ), eventually_ge_atTop R,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    (hA.orbitIndex_tendsto_atTop 1).eventually (eventually_ge_atTop 1)]
    with x hx1 hxM hxlarge hxR hxlog hindex
  let n : ℕ := orbitIndex A 1 x
  let u : ℝ := orbitBase A 1 x
  have hu := hA.orbitBase_mem zero_lt_one hx1
  have hux : E^[n] u = x := hA.iterate_orbitBase (zero_lt_one.trans_le hx1)
  have hbase : BoundedComplexExtension A u ρ C :=
    (hbranches u ⟨hu.1, hu.2.le⟩).mono (min_le_left _ _) le_rfl
  have hn : 1 ≤ n := hindex
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change n = m + 1 at hm
  have hden : 0 < 1 + x - M := by linarith
  have hsmall : M / (1 + x - M) ≤ ρ := by
    apply (div_le_iff₀ hden).mpr
    have h := (div_le_iff₀ hρ).mp (show M / ρ ≤ x - M by linarith)
    nlinarith
  have hiter := complexL_iterate_large_disk hρ (hρ1.trans hu.1) hM m
    (by rw [← hm, hux]; linarith : M < 1 + E^[m + 1] u)
    (by rw [← hm, hux]; exact hsmall)
  rw [← hm, hux] at hiter
  have hext := hA.bounded_complex_extension_of_logarithms n hxM hbase hiter.1 hiter.2
  apply hext.mono le_rfl
  have hnA : (n : ℝ) ≤ A x := by
    have hf := Nat.floor_le (hA.nonneg_of_one_le hx1)
    simpa only [n, orbitIndex, hA.normalized, sub_zero] using hf
  have hl := hlog x hxR
  have hprod := mul_nonneg (abs_nonneg (D + C)) (sub_nonneg.mpr hxlog)
  nlinarith [le_abs_self (D + C)]

theorem exists_bounded_complex_extensions {M : ℝ} (hM : 0 < M) :
    ∃ xM K : ℝ, 1 < xM ∧ 0 < K ∧
      ∀ x : ℝ, xM < x → BoundedComplexExtension A x M (K * Real.log x) := by
  obtain ⟨K, hK, he⟩ := hA.eventually_bounded_complex_extension hM
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  refine ⟨max R 2, K, lt_of_lt_of_le (by norm_num) (le_max_right _ _), hK, ?_⟩
  intro x hx
  exact hR x ((le_max_left _ _).trans hx.le)

/-- The extensions can be chosen together and agree on every overlap. -/
theorem exists_compatible_bounded_complex_extensions {M : ℝ} (hM : 0 < M) :
    ∃ xM K : ℝ, ∃ F : ℝ → ℂ → ℂ, 1 < xM ∧ 0 < K ∧
      (∀ x : ℝ, xM < x →
        AnalyticOnNhd ℂ (F x) (ball (x : ℂ) M) ∧
          (∀ y : ℝ, y ∈ ball x M → F x (y : ℂ) = (A y : ℂ)) ∧
          ∀ z ∈ ball (x : ℂ) M, ‖F x z‖ ≤ K * Real.log x) ∧
      ∀ x y : ℝ, xM < x → xM < y →
        EqOn (F x) (F y) (ball (x : ℂ) M ∩ ball (y : ℂ) M) := by
  classical
  obtain ⟨xM, K, hxM, hK, he⟩ := hA.exists_bounded_complex_extensions hM
  let F : ℝ → ℂ → ℂ := fun x =>
    if hx : xM < x then (he x hx).choose else fun _ => 0
  have hF : ∀ x : ℝ, xM < x →
      AnalyticOnNhd ℂ (F x) (ball (x : ℂ) M) ∧
        (∀ y : ℝ, y ∈ ball x M → F x (y : ℂ) = (A y : ℂ)) ∧
        ∀ z ∈ ball (x : ℂ) M, ‖F x z‖ ≤ K * Real.log x := by
    intro x hx
    simpa only [F, dite_eq_left hx] using (he x hx).choose_spec
  refine ⟨xM, K, F, hxM, hK, hF, ?_⟩
  intro x y hx hy
  exact analytic_extensions_eqOn_inter (hF x hx).1 (hF y hy).1
    (hF x hx).2.1 (hF y hy).2.1

end AbelFormalization.IsAbel
