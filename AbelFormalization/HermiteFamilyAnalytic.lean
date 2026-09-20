import AbelFormalization.HermiteCoefficientAnalytic

/-! # Joint analytic dependence on the target family and the nodes

An analytic family with values in the contour Banach space can be multiplied
by the analytic Hermite kernel. Applying the bounded contour functional then
gives the actual scalar interpolation coefficients with all parameters free.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι : Type*} [Fintype ι]

/-- Joint power-series analyticity of the contour coefficient whenever the
target's contour restriction is an analytic Banach-valued family. -/
theorem analyticAt_hermiteContourCoeff_family {R : ℝ} (hR : 0 ≤ R)
    (m : ι → ℕ) (j : ℕ) (f : E × ℂ → ℂ)
    (G : E → C(sphere (0 : ℂ) R, ℂ)) {p : E} (hG : AnalyticAt ℂ G p)
    (he : ∀ᶠ v in 𝓝 p, ∀ z : sphere (0 : ℂ) R, G v z = f (v, z))
    (δ : ι → ℂ)
    (hQ : ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0) :
    AnalyticAt ℂ (fun v : E × (ι → ℂ) =>
      hermiteContourCoeff (fun z => f (v.1, z)) (nodePolynomial v.2 m) R j) (p, δ) := by
  let K : (E × (ι → ℂ)) → C(sphere (0 : ℂ) R, ℂ) :=
    fun v => hermiteContourKernelMap R v.2 m j * G v.1
  have hu := isUnit_nodeContourDenominator R δ m hQ
  have hkbase : AnalyticAt ℂ
      (fun ε : ι → ℂ => hermiteContourKernelMap R ε m j) δ :=
    analyticAt_hermiteContourKernelMap R m j δ hu
  have hproj : AnalyticAt ℂ (fun v : E × (ι → ℂ) => v.2) (p, δ) := analyticAt_snd
  have hkernel : AnalyticAt ℂ
      (fun v : E × (ι → ℂ) => hermiteContourKernelMap R v.2 m j) (p, δ) :=
    AnalyticAt.fun_comp (g := fun ε : ι → ℂ => hermiteContourKernelMap R ε m j)
      (f := fun v : E × (ι → ℂ) => v.2) hkbase hproj
  have htarget : AnalyticAt ℂ (fun v : E × (ι → ℂ) => G v.1) (p, δ) :=
    hG.comp (f := fun v : E × (ι → ℂ) => v.1) analyticAt_fst
  have hK : AnalyticAt ℂ K (p, δ) := hkernel.fun_mul htarget
  have ha : AnalyticAt ℂ (fun v => cauchyNormalization * contourIntegralCLM R hR (K v))
      (p, δ) := analyticAt_const.fun_mul
    (((contourIntegralCLM R hR).analyticAt (K (p, δ))).comp (f := K) hK)
  have hunit : ∀ᶠ ε in 𝓝 δ, IsUnit (nodeContourDenominator R ε m) :=
    (analyticAt_nodeContourDenominator R m δ).continuousAt
      (Units.isOpen.mem_nhds hu)
  have het : ∀ᶠ v : E × (ι → ℂ) in 𝓝 (p, δ),
      ∀ z : sphere (0 : ℂ) R, G v.1 z = f (v.1, z) := by
    have hπ : Tendsto (fun v : E × (ι → ℂ) => v.1) (𝓝 (p, δ)) (𝓝 p) :=
      continuousAt_fst
    exact hπ.eventually he
  have heu : ∀ᶠ v : E × (ι → ℂ) in 𝓝 (p, δ),
      IsUnit (nodeContourDenominator R v.2 m) := by
    have hπ : Tendsto (fun v : E × (ι → ℂ) => v.2) (𝓝 (p, δ)) (𝓝 δ) :=
      continuousAt_snd
    exact hπ.eventually hunit
  apply ha.congr
  filter_upwards [het, heu] with v hve hvu
  unfold hermiteContourCoeff
  congr 1
  apply contourIntegralCLM_eq_circleIntegral R hR
  intro z
  dsimp only [K]
  rw [ContinuousMap.mul_apply, hermiteContourKernelMap_apply R v.2 m j hvu, hve z]
  dsimp only [hermiteCoefficientKernel]
  ring

end AbelFormalization
