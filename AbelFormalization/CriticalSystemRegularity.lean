import AbelFormalization.RegularConstraintFiber
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The square system formed from the constraints and their critical
determinant. -/
def criticalSystemMap {r : ℕ} (H : Fin r → E → ℝ) (K : E → ℝ) :
    E → Fin (r + 1) → ℝ :=
  fun x i ↦ functionTupleSnoc H K i x

/-- The product Fréchet derivative of the square critical system. -/
def criticalSystemFDeriv {r : ℕ} (H : Fin r → E → ℝ) (K : E → ℝ)
    (x : E) : E →L[ℝ] (Fin (r + 1) → ℝ) :=
  ContinuousLinearMap.pi
    (fun i ↦ fderiv ℝ (functionTupleSnoc H K i) x)

theorem hasStrictFDerivAt_criticalSystemMap {r : ℕ}
    (H : Fin r → E → ℝ) (K : E → ℝ) (x : E)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : HasStrictFDerivAt K (fderiv ℝ K x) x) :
    HasStrictFDerivAt (criticalSystemMap H K)
      (criticalSystemFDeriv H K x) x := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa [criticalSystemMap, criticalSystemFDeriv] using hK
  · simpa [criticalSystemMap, criticalSystemFDeriv] using hH j

/-- If the constraint derivative has the tangent line as its kernel and the
last equation has nonzero derivative on that line, the square critical
derivative is injective. -/
theorem criticalSystemFDeriv_injective_of_ker_eq_span {r : ℕ}
    (H : Fin r → E → ℝ) (K : E → ℝ) (x τ : E)
    (hker : (constraintFDeriv H x).ker = ℝ ∙ τ)
    (hKτ : fderiv ℝ K x τ ≠ 0) :
    Function.Injective (criticalSystemFDeriv H K x) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hvConstraint : v ∈ (constraintFDeriv H x).ker := by
    rw [LinearMap.mem_ker]
    ext i
    have hi := congrFun hv i.castSucc
    simpa [criticalSystemFDeriv, constraintFDeriv] using hi
  rw [hker] at hvConstraint
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvConstraint
  have hvK : fderiv ℝ K x v = 0 := by
    have hi := congrFun hv (Fin.last r)
    simpa [criticalSystemFDeriv] using hi
  rw [← hc, map_smul, smul_eq_mul] at hvK
  have hc0 : c = 0 := (mul_eq_zero.mp hvK).resolve_right hKτ
  rw [← hc, hc0, zero_smul]

/-- In equal finite dimensions the preceding derivative is surjective, hence
the critical point is a regular zero of the square system. -/
theorem criticalSystemFDeriv_surjective_of_ker_eq_span {r : ℕ}
    [FiniteDimensional ℝ E]
    (H : Fin r → E → ℝ) (K : E → ℝ) (x τ : E)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hker : (constraintFDeriv H x).ker = ℝ ∙ τ)
    (hKτ : fderiv ℝ K x τ ≠ 0) :
    Function.Surjective (criticalSystemFDeriv H K x) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (criticalSystemFDeriv_injective_of_ker_eq_span H K x τ hker hKτ)

theorem criticalSystemMap_apply_castSucc {r : ℕ}
    (H : Fin r → E → ℝ) (K : E → ℝ) (x : E) (i : Fin r) :
    criticalSystemMap H K x i.castSucc = H i x := by
  simp [criticalSystemMap]

theorem criticalSystemMap_apply_last {r : ℕ}
    (H : Fin r → E → ℝ) (K : E → ℝ) (x : E) :
    criticalSystemMap H K x (Fin.last r) = K x := by
  simp [criticalSystemMap]

/-- A zero of the constraint equations and last critical equation is a
regular zero when the tangent-line test holds. -/
theorem mem_regularZeroSet_criticalSystemMap_of_ker_eq_span {r : ℕ}
    [FiniteDimensional ℝ E]
    {Omega : Set E} (H : Fin r → E → ℝ) (K : E → ℝ) (x τ : E)
    (hxOmega : x ∈ Omega)
    (hHx : ∀ i, H i x = 0) (hKx : K x = 0)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hker : (constraintFDeriv H x).ker = ℝ ∙ τ)
    (hKτ : fderiv ℝ K x τ ≠ 0) :
    x ∈ regularZeroSet Omega (criticalSystemMap H K) := by
  refine ⟨hxOmega, ?_, ?_⟩
  · ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [criticalSystemMap_apply_last]
      exact hKx
    · rw [criticalSystemMap_apply_castSucc]
      exact hHx j
  · rw [(hasStrictFDerivAt_criticalSystemMap H K x hH hK).hasFDerivAt.fderiv]
    exact criticalSystemFDeriv_surjective_of_ker_eq_span
      H K x τ hdim hker hKτ

/-- A constrained critical point is a regular zero of the explicit critical
system once the Morse tangent test has been verified. -/
theorem constrainedCriticalPoint_mem_regularZeroSet {r : ℕ}
    [FiniteDimensional ℝ E]
    {M Omega : Set E} (H : Fin r → E → ℝ) (ρ K : E → ℝ)
    (basis : Fin (r + 1) → E) (x : M) (τ : E)
    (hxOmega : (x : E) ∈ Omega)
    (hHx : ∀ i, H i x = 0)
    (hKcritical : K x = criticalDeterminant H ρ basis x)
    (hxCritical : x ∈ constrainedCriticalSet M H ρ basis)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hker : (constraintFDeriv H x).ker = ℝ ∙ τ)
    (hKτ : fderiv ℝ K x τ ≠ 0) :
    (x : E) ∈ regularZeroSet Omega (criticalSystemMap H K) := by
  have hCriticalZero : criticalDeterminant H ρ basis x = 0 := hxCritical
  apply mem_regularZeroSet_criticalSystemMap_of_ker_eq_span
    H K (x : E) τ hxOmega hHx (hKcritical.trans hCriticalZero)
    hH hK hdim hker hKτ

/-- The full finite-component conclusion with the two geometric inputs in
the form used by the manuscript: independent constraint differentials and a
nonzero derivative of the critical equation along the tangent line. -/
theorem finite_connectedComponents_of_finite_regularCriticalSystem_of_tangent
    {r : ℕ} [FiniteDimensional ℝ E]
    {M Omega : Set E} (H : Fin r → E → ℝ) (ρ K : E → ℝ)
    (basis : Fin (r + 1) → E) (τ : M → E)
    (hρcont : Continuous ρ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | ρ (x : E) ≤ R})
    (hregularFinite :
      (regularZeroSet Omega (criticalSystemMap H K)).Finite)
    (hOmega : ∀ x : M, (x : E) ∈ Omega)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hKcritical : ∀ x : M,
      K x = criticalDeterminant H ρ basis x)
    (hlocalConstraint : ∀ x : M, ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (hsurj : ∀ x : M, (constraintFDeriv H x).range = ⊤)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : ∀ x : M, HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hker : ∀ x : M, (constraintFDeriv H x).ker = ℝ ∙ τ x)
    (hKτ : ∀ x : M, x ∈ constrainedCriticalSet M H ρ basis →
      fderiv ℝ K x (τ x) ≠ 0)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Finite (ConnectedComponents M) := by
  apply
    finite_connectedComponents_of_finite_regularCriticalSystem_of_surjectiveConstraint
      H ρ basis (criticalSystemMap H K)
      hρcont hcompact hregularFinite
  · intro x hx
    exact constrainedCriticalPoint_mem_regularZeroSet
      H ρ K basis x (τ x) (hOmega x) (hMzero x) (hKcritical x) hx
      (hH x) (hK x) hdim (hker x) (hKτ x hx)
  · exact hlocalConstraint
  · exact hsurj
  · exact hH
  · exact hρ

end AbelFormalization
