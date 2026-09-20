import AbelFormalization.ParametricChartCover

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

theorem exists_countable_parametric_chart_cover
    (Phi : X × Y → Z) (S : Set (X × Y))
    (hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p)
    (hSurj : ∀ p ∈ S, (fderiv ℝ Phi p).range = ⊤) :
    ∃ T : Set S, T.Countable ∧
      ∀ q : S, ∃ p : S, p ∈ T ∧
        (q : X × Y) ∈ parametricImplicitRegularSource
          Phi p (hPhi p p.property) (hSurj p p.property) := by
  let U : S → Set S := fun p =>
    Subtype.val ⁻¹' parametricImplicitRegularSource
      Phi p (hPhi p p.property) (hSurj p p.property)
  have hU : ∀ p : S, U p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      (parametricImplicitRegularSource_mem_nhds
        Phi p (hPhi p p.property) (hSurj p p.property))
  obtain ⟨T, hTcount, hTcover⟩ := TopologicalSpace.countable_cover_nhds hU
  refine ⟨T, hTcount, ?_⟩
  intro q
  have hq : q ∈ ⋃ p ∈ T, U p := by
    rw [hTcover]
    exact Set.mem_univ q
  simp only [Set.mem_iUnion] at hq
  obtain ⟨p, hpT, hqp⟩ := hq
  exact ⟨p, hpT, hqp⟩

variable [MeasurableSpace Y] [BorelSpace Y]

theorem exists_parameter_with_regular_fixed_slice
    (Phi : X × Y → Z) (S : Set (X × Y)) (z : Z)
    (hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hLevel : ∀ p ∈ S, Phi p = z)
    (hSurj : ∀ p ∈ S, (fderiv ℝ Phi p).range = ⊤) :
    ∃ c : Y, ∀ q ∈ S, q.2 = c →
      (fstPartial (fderiv ℝ Phi q)).range = ⊤ := by
  obtain ⟨T, hTcount, hTcover⟩ :=
    exists_countable_parametric_chart_cover Phi S hPhi hSurj
  letI : Countable T := hTcount.to_subtype
  let chart : T → Y → X × Y := fun i =>
    parametricLevelChart Phi i.1.1 (hPhi i.1.1 i.1.2) hdim
      (hSurj i.1.1 i.1.2)
  let projection : T → Y → Y := fun i y => (chart i y).2
  let criticalDomain : T → Set Y := fun i =>
    {y | y ∈ parametricChartParameterSet Phi i.1.1
          (hPhi i.1.1 i.1.2) hdim
          (hSurj i.1.1 i.1.2) ∧
        chart i y ∈ S ∧
        (fstPartial (fderiv ℝ Phi (chart i y))).range ≠ ⊤}
  obtain ⟨c, hc⟩ := exists_avoiding_countable_critical_images
    projection criticalDomain
    (fun i y hy => by
      exact (differentiableAt_parametricLevelChart_of_mem
        Phi i.1.1 (hPhi i.1.1 i.1.2) hdim
          (hSurj i.1.1 i.1.2) hy.1).snd)
    (fun i y hy => by
      exact parametricLevelProjection_det_eq_zero_of_mem
        Phi i.1.1 (hPhi i.1.1 i.1.2) hdim (hSurj i.1.1 i.1.2)
        hy.1 (hSurj (chart i y) hy.2.1) hy.2.2)
  refine ⟨c, ?_⟩
  intro q hqS hqc
  by_contra hqBad
  let qs : S := ⟨q, hqS⟩
  obtain ⟨p, hpT, hqU⟩ := hTcover qs
  let i : T := ⟨p, hpT⟩
  have hlevel : Phi q = Phi p := (hLevel q hqS).trans (hLevel p p.property).symm
  obtain ⟨y, hyParam, hyChart⟩ := exists_parametricLevelChart_parameter
    Phi p q (hPhi p p.property) hdim (hSurj p p.property) hlevel hqU
  have hchartEq : chart i y = q := by
    simpa only [chart, i] using hyChart
  have hyS : chart i y ∈ S := by
    rw [hchartEq]
    exact hqS
  have hyBad : (fstPartial (fderiv ℝ Phi (chart i y))).range ≠ ⊤ := by
    rw [hchartEq]
    exact hqBad
  have hyCritical : y ∈ criticalDomain i := by
    exact ⟨by simpa [i] using hyParam, hyS, hyBad⟩
  apply hc i
  refine ⟨y, hyCritical, ?_⟩
  change (chart i y).2 = c
  rw [hchartEq, hqc]

end AbelFormalization
