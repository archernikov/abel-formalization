import AbelFormalization.ContourFunctional
import AbelFormalization.HermiteAnalytic
import AbelFormalization.HermiteContour
import Mathlib.Topology.ContinuousMap.Units

/-!
# Analytic dependence of the integrated Hermite coefficients

We work in the Banach algebra of continuous complex functions on the contour.
The denominator and numerator are polynomial maps of the nodes with values in
that algebra. At a tuple with no node on the contour, the denominator is a unit.
Analytic inversion followed by the bounded linear contour functional proves
multivariable analyticity of the actual contour coefficients.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Polynomial
open scoped Topology

/-- The coordinate function on the contour circle. -/
def contourCoordinate (R : ℝ) : C(sphere (0 : ℂ) R, ℂ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem contourCoordinate_apply (R : ℝ) (z : sphere (0 : ℂ) R) :
    contourCoordinate R z = z := rfl

variable {ι : Type*} [Fintype ι]

/-- The node polynomial restricted to the contour, expressed in its Banach algebra. -/
def nodeContourDenominator (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) :
    C(sphere (0 : ℂ) R, ℂ) :=
  ∏ i, (contourCoordinate R - δ i • 1) ^ m i

@[simp]
theorem nodeContourDenominator_apply (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ)
    (z : sphere (0 : ℂ) R) :
    nodeContourDenominator R δ m z = (nodePolynomial δ m).eval (z : ℂ) := by
  simp [nodeContourDenominator, nodePolynomial_eval]

/-- The coefficient numerator, expressed in the contour Banach algebra. -/
def nodeContourNumerator (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ) :
    C(sphere (0 : ℂ) R, ℂ) :=
  ∑ i ∈ Finset.Icc (j + 1) (totalMultiplicity m),
    (nodePolynomial δ m).coeff i • contourCoordinate R ^ (i - (j + 1))

@[simp]
theorem nodeContourNumerator_apply (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ)
    (z : sphere (0 : ℂ) R) :
    nodeContourNumerator R δ m j z = (hermiteKernel (nodePolynomial δ m) z).coeff j := by
  simp [nodeContourNumerator, hermiteKernel_coeff, nodePolynomial_natDegree, mul_comm]

/-- The denominator is an entire map into the Banach algebra of contour functions. -/
theorem analyticAt_nodeContourDenominator (R : ℝ) (m : ι → ℕ) (δ : ι → ℂ) :
    AnalyticAt ℂ (fun ε : ι → ℂ => nodeContourDenominator R ε m) δ := by
  unfold nodeContourDenominator
  apply Finset.analyticAt_fun_prod
  intro i _
  apply AnalyticAt.fun_pow
  apply AnalyticAt.fun_sub analyticAt_const
  have hp : AnalyticAt ℂ (fun ε : ι → ℂ => ε i) δ := by
    exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt δ).congr
      (Filter.Eventually.of_forall fun ε => ContinuousLinearMap.proj_apply i ε)
  exact hp.fun_smul analyticAt_const

/-- The numerator is an entire map into the same Banach algebra. -/
theorem analyticAt_nodeContourNumerator (R : ℝ) (m : ι → ℕ) (j : ℕ) (δ : ι → ℂ) :
    AnalyticAt ℂ (fun ε : ι → ℂ => nodeContourNumerator R ε m j) δ := by
  unfold nodeContourNumerator
  exact Finset.analyticAt_fun_sum _ fun i _ =>
    (analyticAt_nodePolynomial_coeff m i δ).fun_smul analyticAt_const

theorem isUnit_nodeContourDenominator (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ)
    (h : ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0) :
    IsUnit (nodeContourDenominator R δ m) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  intro z
  rw [nodeContourDenominator_apply]
  exact h z z.property

/-- Inverting a unit continuous function agrees pointwise with scalar inversion. -/
theorem continuousMap_ringInverse_apply {X : Type*} [TopologicalSpace X]
    (g : C(X, ℂ)) (hg : IsUnit g) (z : X) :
    Ring.inverse g z = (g z)⁻¹ := by
  have hz := ((ContinuousMap.isUnit_iff_forall_ne_zero g).mp hg) z
  have hm := congrArg (fun f : C(X, ℂ) => f z) (Ring.mul_inverse_cancel g hg)
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply] at hm
  apply mul_left_cancel₀ hz
  simpa only [mul_inv_cancel₀ hz] using hm

/-- The Banach-algebra version of the coefficient kernel. -/
def hermiteContourKernelMap (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ) :
    C(sphere (0 : ℂ) R, ℂ) :=
  nodeContourNumerator R δ m j * Ring.inverse (nodeContourDenominator R δ m)

theorem hermiteContourKernelMap_apply (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ)
    (h : IsUnit (nodeContourDenominator R δ m)) (z : sphere (0 : ℂ) R) :
    hermiteContourKernelMap R δ m j z = hermiteCoefficientKernel δ m z j := by
  simp only [hermiteContourKernelMap, ContinuousMap.mul_apply,
    continuousMap_ringInverse_apply _ h, nodeContourNumerator_apply,
    nodeContourDenominator_apply, hermiteCoefficientKernel, div_eq_mul_inv]

/-- Analytic Banach-valued coefficient kernels at every invertible denominator. -/
theorem analyticAt_hermiteContourKernelMap (R : ℝ) (m : ι → ℕ) (j : ℕ) (δ : ι → ℂ)
    (h : IsUnit (nodeContourDenominator R δ m)) :
    AnalyticAt ℂ (fun ε : ι → ℂ => hermiteContourKernelMap R ε m j) δ := by
  have hi : AnalyticAt ℂ Ring.inverse (nodeContourDenominator R δ m) :=
    analyticOnNhd_inverse _ h
  exact (analyticAt_nodeContourNumerator R m j δ).fun_mul
    (hi.fun_comp (f := fun ε : ι → ℂ => nodeContourDenominator R ε m)
      (analyticAt_nodeContourDenominator R m δ))

/-- Full multivariable analyticity of the actual integrated Hermite coefficient.
Only boundary continuity of the interpolated function is needed. -/
theorem analyticAt_hermiteContourCoeff_nodes (R : ℝ) (hR : 0 ≤ R) (m : ι → ℕ)
    (j : ℕ) (f : ℂ → ℂ) (hf : ContinuousOn f (sphere (0 : ℂ) R)) (δ : ι → ℂ)
    (hQ : ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0) :
    AnalyticAt ℂ (fun ε : ι → ℂ => hermiteContourCoeff f (nodePolynomial ε m) R j) δ := by
  let fc : C(sphere (0 : ℂ) R, ℂ) :=
    ⟨fun z => f z, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let g : (ι → ℂ) → ℂ := fun ε => cauchyNormalization *
    contourIntegralCLM R hR (hermiteContourKernelMap R ε m j * fc)
  have hu := isUnit_nodeContourDenominator R δ m hQ
  have hp : AnalyticAt ℂ
      (fun ε : ι → ℂ => hermiteContourKernelMap R ε m j * fc) δ :=
    (analyticAt_hermiteContourKernelMap R m j δ hu).fun_mul analyticAt_const
  have hg : AnalyticAt ℂ g δ := analyticAt_const.fun_mul
    (((contourIntegralCLM R hR).analyticAt (hermiteContourKernelMap R δ m j * fc)).fun_comp
      (f := fun ε : ι → ℂ => hermiteContourKernelMap R ε m j * fc) hp)
  have he : ∀ᶠ ε in 𝓝 δ, IsUnit (nodeContourDenominator R ε m) :=
    (analyticAt_nodeContourDenominator R m δ).continuousAt
      (Units.isOpen.mem_nhds hu)
  apply hg.congr
  filter_upwards [he] with ε hε
  unfold g hermiteContourCoeff
  congr 1
  apply contourIntegralCLM_eq_circleIntegral R hR
  intro z
  simp only [ContinuousMap.mul_apply, hermiteContourKernelMap_apply R ε m j hε,
    hermiteCoefficientKernel]
  change _ * f z = _
  ring

/-- A convenient domain version with the exact nonvanishing contour condition. -/
theorem analyticOnNhd_hermiteContourCoeff_nodes (R : ℝ) (hR : 0 ≤ R) (m : ι → ℕ)
    (j : ℕ) (f : ℂ → ℂ) (hf : ContinuousOn f (sphere (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (fun δ : ι → ℂ => hermiteContourCoeff f (nodePolynomial δ m) R j)
      {δ | ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0} :=
  fun δ hδ => analyticAt_hermiteContourCoeff_nodes R hR m j f hf δ hδ

/-- In particular, the coefficient is analytic for every allowed node tuple in
the paper's uniform contour construction. -/
theorem analyticOnNhd_hermiteContourCoeff_nodePolydisk {B : ℝ} (hB : 0 < B)
    (m : ι → ℕ) (j : ℕ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (sphere (0 : ℂ) (B + 1))) :
    AnalyticOnNhd ℂ (fun δ : ι → ℂ => hermiteContourCoeff f (nodePolynomial δ m) (B + 1) j)
      {δ | ∀ i, ‖δ i‖ ≤ B + 1 / 4} := by
  intro δ hδ
  apply analyticAt_hermiteContourCoeff_nodes (B + 1) (by linarith) m j f hf δ
  intro z hz
  exact nodePolynomial_contour_ne_zero_closed m hδ
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)

end AbelFormalization
