import AbelFormalization.RegularZeroBasics

/-!
# Scaling a square system of equations

At a common zero, multiplying each equation by a differentiable scalar
multiplies the corresponding row of the derivative by its value at that
zero.  If all of those values are nonzero, this diagonal row operation
preserves surjectivity and hence preserves regular zeros.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Coordinatewise multiplication by a real vector, as a continuous linear
map on a finite real coordinate space. -/
def coordinatewiseMulCLM {n : ℕ} (c : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    (c i) • ContinuousLinearMap.proj (R := ℝ) i

@[simp]
theorem coordinatewiseMulCLM_apply {n : ℕ} (c v : Fin n → ℝ) (i : Fin n) :
    coordinatewiseMulCLM c v i = c i * v i := by
  simp [coordinatewiseMulCLM, smul_eq_mul]

/-- When all coordinates are nonzero, coordinatewise multiplication is a
continuous linear equivalence. -/
def coordinatewiseMulEquiv {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun i ↦
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 (c i) (hc i))

@[simp]
theorem coordinatewiseMulEquiv_apply {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (v : Fin n → ℝ) (i : Fin n) :
    coordinatewiseMulEquiv c hc v i = c i * v i := by
  simp [coordinatewiseMulEquiv, ContinuousLinearEquiv.smulLeft, Units.smul_def,
    smul_eq_mul]

theorem coordinatewiseMulEquiv_toContinuousLinearMap {n : ℕ}
    (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) :
    (coordinatewiseMulEquiv c hc :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = coordinatewiseMulCLM c := by
  ext v i
  simp

/-- Derivative identity for coordinatewise equation scaling at a common
zero. -/
theorem fderiv_coordinatewise_mul_at_zero {n : ℕ}
    {F d : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hF : DifferentiableAt ℝ F x) (hd : DifferentiableAt ℝ d x)
    (hzero : F x = 0) :
    fderiv ℝ (fun y i ↦ d y i * F y i) x =
      (coordinatewiseMulCLM (d x)).comp (fderiv ℝ F x) := by
  have hFi : ∀ i, DifferentiableAt ℝ (fun y ↦ F y i) x := fun i ↦
    differentiableAt_pi.mp hF i
  have hdi : ∀ i, DifferentiableAt ℝ (fun y ↦ d y i) x := fun i ↦
    differentiableAt_pi.mp hd i
  have hpi : fderiv ℝ (fun y i ↦ d y i * F y i) x =
      ContinuousLinearMap.pi (fun i ↦
        fderiv ℝ (fun y ↦ d y i * F y i) x) :=
    fderiv_pi (fun i ↦ (hdi i).mul (hFi i))
  rw [hpi]
  ext v i
  rw [ContinuousLinearMap.pi_apply]
  have hmul := fderiv_mul (hdi i) (hFi i)
  have hfun : (fun y ↦ d y i * F y i) =
      (fun y ↦ d y i) * (fun y ↦ F y i) := by
    funext y
    rfl
  rw [hfun]
  rw [hmul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply,
    coordinatewiseMulCLM_apply]
  rw [fderiv_apply hF i, fderiv_apply hd i]
  simp [hzero]

/-- Surjectivity is preserved after composing with a coordinatewise
nonzero diagonal map. -/
theorem surjective_coordinatewiseMulCLM_comp_iff {n : ℕ}
    (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    Function.Surjective ((coordinatewiseMulCLM c).comp D) ↔
      Function.Surjective D := by
  rw [← coordinatewiseMulEquiv_toContinuousLinearMap c hc]
  constructor
  · intro h z
    obtain ⟨v, hv⟩ := h (coordinatewiseMulEquiv c hc z)
    change coordinatewiseMulEquiv c hc (D v) =
      coordinatewiseMulEquiv c hc z at hv
    refine ⟨v, (coordinatewiseMulEquiv c hc).injective ?_⟩
    exact hv
  · intro h
    exact (coordinatewiseMulEquiv c hc).surjective.comp h

/-- Multiplying each equation by a nonzero differentiable scalar preserves
membership in the regular-zero set.  Nonvanishing is required only at the
point under consideration. -/
theorem mem_regularZeroSet_coordinatewise_mul_iff {n : ℕ}
    {Omega : Set (Fin n → ℝ)}
    {F d : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hF : DifferentiableAt ℝ F x) (hd : DifferentiableAt ℝ d x)
    (hdne : ∀ i, d x i ≠ 0) :
    x ∈ regularZeroSet Omega (fun y i ↦ d y i * F y i) ↔
      x ∈ regularZeroSet Omega F := by
  constructor
  · rintro ⟨hxOmega, hxzero, hxsurj⟩
    have hFzero : F x = 0 := by
      funext i
      have hi := congr_fun hxzero i
      simp only [Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hdne i)
    refine ⟨hxOmega, hFzero, ?_⟩
    rw [fderiv_coordinatewise_mul_at_zero hF hd hFzero,
      surjective_coordinatewiseMulCLM_comp_iff (d x) hdne] at hxsurj
    exact hxsurj
  · rintro ⟨hxOmega, hxzero, hxsurj⟩
    refine ⟨hxOmega, ?_, ?_⟩
    · funext i
      simp [hxzero]
    · rw [fderiv_coordinatewise_mul_at_zero hF hd hxzero,
        surjective_coordinatewiseMulCLM_comp_iff (d x) hdne]
      exact hxsurj

end AbelFormalization
