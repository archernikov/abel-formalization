import AbelFormalization.SquaredDistanceCriticalFamilyContDiff
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def normalizedCofactorVectorField {r : ℕ}
    (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) : E → E := fun x =>
  (fderiv ℝ h x (criticalCofactorTangent H h basis x))⁻¹ •
    criticalCofactorTangent H h basis x

theorem contDiffAt_normalizedCofactorVectorField {r : ℕ}
    (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hH : ∀ i, ContDiffAt ℝ 2 (H i) x)
    (hh : ContDiffAt ℝ 2 h x)
    (hdet : criticalDeterminant H h basis x ≠ 0) :
    ContDiffAt ℝ 1 (normalizedCofactorVectorField H h basis) x := by
  have htangent : ContDiffAt ℝ 1
      (criticalCofactorTangent H h basis) x := by
    exact contDiffAt_criticalCofactorTangent H h basis x hH hh
  have hdh : ContDiffAt ℝ 1 (fun y => fderiv ℝ h y) x :=
    hh.fderiv_right (by norm_num)
  have hscalar : ContDiffAt ℝ 1
      (fun y => fderiv ℝ h y (criticalCofactorTangent H h basis y)) x :=
    hdh.clm_apply htangent
  have hscalar_ne :
      fderiv ℝ h x (criticalCofactorTangent H h basis x) ≠ 0 := by
    rwa [← criticalDeterminant_eq_fderiv_criticalCofactorTangent H h basis x]
  exact (hscalar.inv hscalar_ne).smul htangent

theorem fderiv_normalizedCofactorVectorField_constraint_eq_zero {r : ℕ}
    (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E) (i : Fin r) :
    fderiv ℝ (H i) x (normalizedCofactorVectorField H h basis x) = 0 := by
  rw [normalizedCofactorVectorField, map_smul, smul_eq_mul,
    fderiv_constraint_criticalCofactorTangent_eq_zero, mul_zero]

theorem fderiv_normalizedCofactorVectorField_comparison_eq_one {r : ℕ}
    (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hdet : criticalDeterminant H h basis x ≠ 0) :
    fderiv ℝ h x (normalizedCofactorVectorField H h basis x) = 1 := by
  rw [normalizedCofactorVectorField, map_smul, smul_eq_mul]
  have hs : fderiv ℝ h x (criticalCofactorTangent H h basis x) ≠ 0 := by
    rwa [← criticalDeterminant_eq_fderiv_criticalCofactorTangent H h basis x]
  exact inv_mul_cancel₀ hs

theorem normalizedCofactorVectorField_ne_zero {r : ℕ}
    (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hdet : criticalDeterminant H h basis x ≠ 0) :
    normalizedCofactorVectorField H h basis x ≠ 0 := by
  have hs : fderiv ℝ h x (criticalCofactorTangent H h basis x) ≠ 0 := by
    rwa [← criticalDeterminant_eq_fderiv_criticalCofactorTangent H h basis x]
  exact smul_ne_zero (inv_ne_zero hs)
    (criticalCofactorTangent_ne_zero_of_criticalDeterminant_ne_zero
      H h h basis x hdet)

theorem exists_local_normalizedCofactorIntegralCurve {r : ℕ}
    {M Ω : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : M)
    (hΩ : Ω ∈ 𝓝 (x : E))
    (hH : ∀ y ∈ Ω, ∀ i, ContDiffAt ℝ 2 (H i) y)
    (hh : ∀ y ∈ Ω, ContDiffAt ℝ 2 h y)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hlocalConstraint : ∃ U ∈ 𝓝 (x : E),
      U ∩ {y | ∀ i, H i y = H i x} ⊆ M) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E,
      γ 0 = x ∧ ∀ t ∈ Ioo (-ε) ε,
        γ t ∈ M ∧
          HasDerivAt γ
            (normalizedCofactorVectorField H h basis (γ t)) t ∧
          h (γ t) = h x + t := by
  obtain ⟨U, hU, hUM⟩ := hlocalConstraint
  have hxΩ : (x : E) ∈ Ω := mem_of_mem_nhds hΩ
  have hfield : ContDiffAt ℝ 1
      (normalizedCofactorVectorField H h basis) x :=
    contDiffAt_normalizedCofactorVectorField H h basis x
      (hH x hxΩ) (hh x hxΩ) (hdet x x.property)
  obtain ⟨γ, hγzero, ε₀, hε₀, hγderiv⟩ :=
    hfield.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hzeroMem : (0 : ℝ) ∈ Ioo (0 - ε₀) (0 + ε₀) := by
    constructor <;> linarith
  have hγcont : ContinuousAt γ 0 :=
    (hγderiv 0 hzeroMem).continuousAt
  have hstay : γ ⁻¹' (Ω ∩ U) ∈ 𝓝 0 := by
    apply hγcont.preimage_mem_nhds
    rw [hγzero]
    exact inter_mem hΩ hU
  have htimeWindow : Ioo (0 - ε₀) (0 + ε₀) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ),
      t ∈ Ioo (0 - ε₀) (0 + ε₀) ∧ γ t ∈ Ω ∩ U :=
    by
      filter_upwards [htimeWindow, hstay]
        with t ht hγt
      exact ⟨ht, hγt⟩
  rw [Metric.eventually_nhds_iff_ball] at htime
  obtain ⟨ε, hε, hεstay⟩ := htime
  have hlocal : ∀ t ∈ Ioo (-ε) ε,
      t ∈ Ioo (0 - ε₀) (0 + ε₀) ∧ γ t ∈ Ω ∩ U := by
    intro t ht
    apply hεstay t
    simpa [Real.dist_eq, abs_lt] using ht
  have hconstraint : ∀ i, EqOn (H i ∘ γ) (fun _ => H i x) (Ioo (-ε) ε) := by
    intro i
    apply isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    · intro t ht
      have htlocal := hlocal t ht
      exact ((hH (γ t) htlocal.2.1 i).differentiableAt (by norm_num)).hasFDerivAt
        |>.comp_hasDerivAt t (hγderiv t htlocal.1)
        |>.differentiableAt.differentiableWithinAt
    · exact differentiableOn_const _
    · intro t ht
      have htlocal := hlocal t ht
      have hcomp := ((hH (γ t) htlocal.2.1 i).differentiableAt
        (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hγderiv t htlocal.1)
      rw [hcomp.deriv, deriv_const]
      exact fderiv_normalizedCofactorVectorField_constraint_eq_zero
        H h basis (γ t) i
    · exact ⟨neg_neg_of_pos hε, hε⟩
    · simp [hγzero]
  have hγM : ∀ t ∈ Ioo (-ε) ε, γ t ∈ M := by
    intro t ht
    have htlocal := hlocal t ht
    apply hUM
    exact ⟨htlocal.2.2, fun i => hconstraint i ht⟩
  have hcomparison : EqOn (h ∘ γ) (fun t => h x + t) (Ioo (-ε) ε) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    · intro t ht
      have htlocal := hlocal t ht
      exact ((hh (γ t) htlocal.2.1).differentiableAt (by norm_num)).hasFDerivAt
        |>.comp_hasDerivAt t (hγderiv t htlocal.1)
        |>.differentiableAt.differentiableWithinAt
    · fun_prop
    · intro t ht
      have htlocal := hlocal t ht
      have hcomp := ((hh (γ t) htlocal.2.1).differentiableAt
        (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hγderiv t htlocal.1)
      rw [hcomp.deriv]
      have hrhs : HasDerivAt (fun s : ℝ => h x + s) 1 t := by
        exact (hasDerivAt_id t).const_add (h x)
      rw [hrhs.deriv]
      exact fderiv_normalizedCofactorVectorField_comparison_eq_one
        H h basis (γ t) (hdet (γ t) (hγM t ht))
    · exact ⟨neg_neg_of_pos hε, hε⟩
    · simp [hγzero]
  refine ⟨ε, hε, γ, hγzero, ?_⟩
  intro t ht
  exact ⟨hγM t ht, hγderiv t (hlocal t ht).1, hcomparison ht⟩

end AbelFormalization
