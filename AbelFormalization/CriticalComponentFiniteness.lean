import AbelFormalization.LagrangeCriticalDeterminant
import AbelFormalization.RegularZeroBasics

/-!
# From finite critical systems to finite components

This file packages the exact logical bridge in the exponential-adjunction
argument.  Local connectedness of each regular constraint fiber turns a
componentwise minimum into a constrained local minimum.  Lagrange multipliers
then put it in the determinant-zero critical set.  Compact sublevels and
finiteness of that set imply finitely many connected components.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The determinant obtained by appending the objective differential to the
constraint differentials. -/
def criticalDeterminant {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) : ℝ :=
  Matrix.det (fun i j ↦
    fderiv ℝ (functionTupleSnoc H ρ i) x (basis j))

/-- The critical determinant zero set, regarded as a subset of the closed
constraint locus `M`. -/
def constrainedCriticalSet {r : ℕ} (M : Set E)
    (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) : Set M :=
  {x | criticalDeterminant H ρ basis (x : E) = 0}

/-- A componentwise minimum on a constraint locus is a critical-determinant
zero when the local constraint fiber stays in that component. -/
theorem componentMinimizer_mem_constrainedCriticalSet
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : M)
    (hmin : x ∈ componentMinimizers (fun y : M ↦ ρ (y : E)))
    (hlocalFiber : ∃ U ∈ nhds (x : E),
      ∀ y ∈ U, (∀ i, H i y = H i x) →
        ∃ hyM : y ∈ M, (⟨y, hyM⟩ : M) ∈ connectedComponent x)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    x ∈ constrainedCriticalSet M H ρ basis := by
  obtain ⟨U, hU, hlocalFiber⟩ := hlocalFiber
  change IsMinOn (fun y : M ↦ ρ (y : E)) (connectedComponent x) x at hmin
  have hlocal : IsLocalMinOn ρ {y : E | ∀ i, H i y = H i x} (x : E) := by
    rw [IsLocalMinOn]
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin]
      with y hyU hyfiber
    obtain ⟨hyM, hycomponent⟩ := hlocalFiber y hyU hyfiber
    exact hmin hycomponent
  exact criticalSystemDeterminant_eq_zero_of_isLocalExtrOn
    H ρ x basis (Or.inl hlocal) hH hρ

/-- The abstract finite-component conclusion of the Morse/critical-point
part of exponential adjunction. -/
theorem finite_connectedComponents_of_finite_constrainedCriticalSet
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E)
    (hρcont : Continuous ρ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | ρ (x : E) ≤ R})
    (hcritical : (constrainedCriticalSet M H ρ basis).Finite)
    (hlocalFiber : ∀ x : M, ∃ U ∈ nhds (x : E),
      ∀ y ∈ U, (∀ i, H i y = H i x) →
        ∃ hyM : y ∈ M, (⟨y, hyM⟩ : M) ∈ connectedComponent x)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Finite (ConnectedComponents M) := by
  apply finite_connectedComponents_of_finite_componentMinimizers
    (fun x : M ↦ ρ (x : E))
    (hρcont.comp continuous_subtype_val) hcompact
  apply hcritical.subset
  intro x hx
  exact componentMinimizer_mem_constrainedCriticalSet H ρ basis x hx
    (hlocalFiber x) (hH x) (hρ x)

/-- Finiteness of ambient regular zeros implies finiteness of the constrained
critical set whenever every critical point is one of those regular zeros. -/
theorem finite_constrainedCriticalSet_of_finite_regularZeroSet
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ} {M Omega : Set E} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (G : E → F)
    (hregularFinite : (regularZeroSet Omega G).Finite)
    (hcriticalRegular : ∀ x : M,
      x ∈ constrainedCriticalSet M H ρ basis →
        (x : E) ∈ regularZeroSet Omega G) :
    (constrainedCriticalSet M H ρ basis).Finite := by
  have hpreimage :
      ((fun x : M ↦ (x : E)) ⁻¹' regularZeroSet Omega G).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hregularFinite
  exact hpreimage.subset fun x hx ↦ hcriticalRegular x hx

/-- Combined form matching the end of the paper's critical-point argument:
finite regular zeros of the square critical system force finite components. -/
theorem finite_connectedComponents_of_finite_regularCriticalSystem
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ} {M Omega : Set E} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (G : E → F)
    (hρcont : Continuous ρ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | ρ (x : E) ≤ R})
    (hregularFinite : (regularZeroSet Omega G).Finite)
    (hcriticalRegular : ∀ x : M,
      x ∈ constrainedCriticalSet M H ρ basis →
        (x : E) ∈ regularZeroSet Omega G)
    (hlocalFiber : ∀ x : M, ∃ U ∈ nhds (x : E),
      ∀ y ∈ U, (∀ i, H i y = H i x) →
        ∃ hyM : y ∈ M, (⟨y, hyM⟩ : M) ∈ connectedComponent x)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Finite (ConnectedComponents M) :=
  finite_connectedComponents_of_finite_constrainedCriticalSet H ρ basis
    hρcont hcompact
    (finite_constrainedCriticalSet_of_finite_regularZeroSet
      H ρ basis G hregularFinite hcriticalRegular)
    hlocalFiber hH hρ

end AbelFormalization
