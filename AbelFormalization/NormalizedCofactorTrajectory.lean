import AbelFormalization.NormalizedCofactorFlowBox
import AbelFormalization.SameIntegralTrajectory

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The local normalized cofactor flow box makes the trajectory class of each
point a neighborhood in the constrained set. -/
theorem normalizedCofactor_trajectoryClass_mem_nhds
    {r : ℕ} {M Ω : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (hΩ : ∀ x ∈ M, Ω ∈ 𝓝 x)
    (hH : ∀ y ∈ Ω, ∀ i, ContDiffAt ℝ 2 (H i) y)
    (hh : ∀ y ∈ Ω, ContDiffAt ℝ 2 h y)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hMzero : ∀ y ∈ M, ∀ i, H i y = 0)
    (hlocalConstraint : ∀ x : M, ∃ U ∈ 𝓝 (x : E),
      U ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (x : M) :
    trajectoryClass (normalizedCofactorVectorField H h basis) M x ∈ 𝓝 x := by
  obtain ⟨ε, hε, γ, hγzero, hγlocal, U, hU, hflowBox⟩ :=
    exists_local_normalizedCofactorIntegralCurve_flowBox
      H h basis x (hΩ x x.property) hH hh hdet
      (fun y hy i => (hMzero y hy i).trans (hMzero x x.property i).symm)
      (hlocalConstraint x)
  apply mem_of_superset (continuousAt_subtype_val.preimage_mem_nhds hU)
  intro y hyU
  change Nonempty (SameIntegralTrajectoryIn
    (normalizedCofactorVectorField H h basis) M x y)
  obtain ⟨ht, hγt⟩ := hflowBox y hyU y.property
  refine ⟨{
    lower := -ε
    upper := ε
    sourceTime := 0
    targetTime := h y - h x
    curve := γ
    sourceTime_mem := ?_
    targetTime_mem := ht
    source_eq := hγzero
    target_eq := hγt
    isIntegral := ?_
    curve_mem := ?_ }⟩
  · exact ⟨neg_neg_of_pos hε, hε⟩
  · intro t ht'
    exact (hγlocal t ht').2.1.hasDerivWithinAt
  · intro t ht'
    exact (hγlocal t ht').1

/-- A connected component of a regular codimension-one constraint locus is
regular-arc connected.  The proof uses local normalized cofactor flows and
ODE uniqueness, requiring smoothness only near the constrained set. -/
theorem regularArcIn_of_mem_connectedComponent_normalizedCofactor
    {r : ℕ} {M Ω : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (hΩ : ∀ x ∈ M, Ω ∈ 𝓝 x)
    (hH : ∀ y ∈ Ω, ∀ i, ContDiffAt ℝ 2 (H i) y)
    (hh : ∀ y ∈ Ω, ContDiffAt ℝ 2 h y)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hMzero : ∀ y ∈ M, ∀ i, H i y = 0)
    (hlocalConstraint : ∀ x : M, ∃ U ∈ 𝓝 (x : E),
      U ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (x y : M) (hy : y ∈ connectedComponent x) (hxy : x ≠ y) :
    RegularArcIn M x y := by
  let V := normalizedCofactorVectorField H h basis
  have hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z := by
    intro z hz
    exact contDiffAt_normalizedCofactorVectorField H h basis z
      (hH z (mem_of_mem_nhds (hΩ z hz)))
      (hh z (mem_of_mem_nhds (hΩ z hz))) (hdet z hz)
  have hlocal : ∀ z : M, trajectoryClass V M z ∈ 𝓝 z := by
    intro z
    exact normalizedCofactor_trajectoryClass_mem_nhds
      H h basis hΩ hH hh hdet hMzero hlocalConstraint z
  apply regularArcIn_of_mem_connectedComponent hV
    (fun z hz => normalizedCofactorVectorField_ne_zero H h basis z (hdet z hz))
    (fun z => show z ∈ trajectoryClass V M z from
      mem_of_mem_nhds (hlocal z)) hlocal x y hy hxy

end AbelFormalization
