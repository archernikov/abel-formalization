import AbelFormalization.ParametricImplicitChart

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

def parametricChartParameterSet
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) : Set Y :=
  {y | parametricLevelCoordinates Phi p hdim hSurj y ∈
      (parametricImplicitChart Phi p hPhi hSurj).target ∧
    ContDiffAt ℝ 1 Phi (parametricLevelChart Phi p hPhi hdim hSurj y) ∧
      (fderiv ℝ (parametricImplicitChart Phi p hPhi hSurj)
        (parametricLevelChart Phi p hPhi hdim hSurj y)).IsInvertible}

theorem differentiableAt_parametricLevelChart_of_mem
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    {y : Y}
    (hy : y ∈ parametricChartParameterSet Phi p hPhi hdim hSurj) :
    DifferentiableAt ℝ (parametricLevelChart Phi p hPhi hdim hSurj) y :=
  (contDiffAt_parametricLevelChart_of_mem
    Phi p hPhi hdim hSurj y hy.1 hy.2.1 hy.2.2).differentiableAt one_ne_zero

theorem fderiv_parametricLevelChart_range_eq_ker_of_mem
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    {y : Y}
    (hy : y ∈ parametricChartParameterSet Phi p hPhi hdim hSurj)
    (hPointSurj : (fderiv ℝ Phi
      (parametricLevelChart Phi p hPhi hdim hSurj y)).range = ⊤) :
    (fderiv ℝ (parametricLevelChart Phi p hPhi hdim hSurj) y).range =
      (fderiv ℝ Phi
        (parametricLevelChart Phi p hPhi hdim hSurj y)).ker :=
  fderiv_parametricLevelChart_range_eq_ker
    Phi p hPhi hdim hSurj y hy.1 hy.2.1 hy.2.2 hPointSurj

theorem parametricLevelChart_value_of_mem
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    {y : Y}
    (hy : y ∈ parametricChartParameterSet Phi p hPhi hdim hSurj) :
    Phi (parametricLevelChart Phi p hPhi hdim hSurj y) = Phi p := by
  have hr := (parametricImplicitChart Phi p hPhi hSurj).right_inv hy.1
  have hrfst := congrArg Prod.fst hr
  simpa [parametricLevelChart, parametricLevelCoordinates] using hrfst

theorem exists_parametricLevelChart_parameter
    (Phi : X × Y → Z) (p q : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (hlevel : Phi q = Phi p)
    (hq : q ∈ parametricImplicitRegularSource Phi p hPhi hSurj) :
    ∃ y ∈ parametricChartParameterSet Phi p hPhi hdim hSurj,
      parametricLevelChart Phi p hPhi hdim hSurj y = q := by
  let e := parametricImplicitChart Phi p hPhi hSurj
  let k : (fderiv ℝ Phi p).ker := (e q).2
  let y : Y := (parameterKernelEquiv (fderiv ℝ Phi p) hdim hSurj).symm k
  have hcoord : parametricLevelCoordinates Phi p hdim hSurj y = e q := by
    apply Prod.ext
    · change Phi p = (e q).1
      rw [show (e q).1 = Phi q by
        exact parametricImplicitChart_fst Phi p q hPhi hSurj]
      exact hlevel.symm
    · change parameterKernelEquiv (fderiv ℝ Phi p) hdim hSurj y = (e q).2
      simp [y, k]
  have hgamma : parametricLevelChart Phi p hPhi hdim hSurj y = q := by
    change e.symm (parametricLevelCoordinates Phi p hdim hSurj y) = q
    rw [hcoord]
    exact e.left_inv hq.1
  refine ⟨y, ?_, hgamma⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoord]
    exact e.map_source hq.1
  · rw [hgamma]
    exact hq.2.1
  · rw [hgamma]
    exact hq.2.2

theorem parametricLevelProjection_det_eq_zero_of_mem
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    {y : Y}
    (hy : y ∈ parametricChartParameterSet Phi p hPhi hdim hSurj)
    (hPointSurj : (fderiv ℝ Phi
      (parametricLevelChart Phi p hPhi hdim hSurj y)).range = ⊤)
    (hfixed : (fstPartial (fderiv ℝ Phi
      (parametricLevelChart Phi p hPhi hdim hSurj y))).range ≠ ⊤) :
    (fderiv ℝ (fun t =>
      (parametricLevelChart Phi p hPhi hdim hSurj t).2) y).det = 0 := by
  apply chartProjection_det_eq_zero_of_fixedParameter_not_regular
    Phi (parametricLevelChart Phi p hPhi hdim hSurj) y
  · exact differentiableAt_parametricLevelChart_of_mem
      Phi p hPhi hdim hSurj hy
  · exact fderiv_parametricLevelChart_range_eq_ker_of_mem
      Phi p hPhi hdim hSurj hy hPointSurj
  · exact hPointSurj
  · exact hfixed

end AbelFormalization
