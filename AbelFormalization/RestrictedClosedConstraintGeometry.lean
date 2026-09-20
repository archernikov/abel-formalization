import AbelFormalization.RestrictedStrictDifferentiability

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

theorem mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p (a + 1)) :
    x ∈ restrictedClosedDenominatorLocus H u q ↔
      (∀ i, restrictedDenominatorSystem H q i x = 0) ∧
        ∀ i, 0 ≤ u i (restrictedSourceDropAux 1 x) := by
  constructor
  · intro hx
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [← restrictedSourceAppendAuxOne_projection x,
          restrictedDenominatorSystem_last_appendAuxOne]
        exact sub_eq_zero.mpr hx.2.2
      · rw [← restrictedSourceAppendAuxOne_projection x,
          restrictedDenominatorSystem_castSucc_appendAuxOne]
        exact hx.1 j
    · exact hx.2.1
  · rintro ⟨hsystem, hu⟩
    constructor
    · intro i
      have hi := hsystem i.castSucc
      rwa [← restrictedSourceAppendAuxOne_projection x,
        restrictedDenominatorSystem_castSucc_appendAuxOne] at hi
    · constructor
      · exact hu
      · have hlast := hsystem (Fin.last r)
        rw [← restrictedSourceAppendAuxOne_projection x,
          restrictedDenominatorSystem_last_appendAuxOne,
          sub_eq_zero] at hlast
        exact hlast

theorem isOpen_restrictedBoundaryPositiveLocus
    {m p a b : ℕ}
    (u : Fin b → RestrictedSource m p a → ℝ)
    (hu : ∀ i, Continuous (u i)) :
    IsOpen {x : RestrictedSource m p (a + 1) |
      ∀ i, 0 < u i (restrictedSourceDropAux 1 x)} := by
  have hdrop : Continuous
      (restrictedSourceDropAux (m := m) (p := p) (a := a) 1) := by
    unfold restrictedSourceDropAux
    fun_prop
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const ((hu i).comp hdrop)

theorem restrictedClosedDenominatorLocus_localConstraint
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    (hu : ∀ i, Continuous (u i))
    (x : restrictedClosedDenominatorLocus H u (boundaryDenominator J u)) :
    ∃ V ∈ 𝓝 (x : RestrictedSource m p (a + 1)),
      V ∩ {y | ∀ i,
        restrictedDenominatorSystem H (boundaryDenominator J u) i y =
          restrictedDenominatorSystem H (boundaryDenominator J u) i x} ⊆
        restrictedClosedDenominatorLocus H u (boundaryDenominator J u) := by
  let V : Set (RestrictedSource m p (a + 1)) :=
    {y | ∀ i, 0 < u i (restrictedSourceDropAux 1 y)}
  have hVopen : IsOpen V :=
    isOpen_restrictedBoundaryPositiveLocus u hu
  have hxV : (x : RestrictedSource m p (a + 1)) ∈ V :=
    (restrictedClosedDenominatorLocus_boundary_strictPos H u J x.property).1
  refine ⟨V, hVopen.mem_nhds hxV, ?_⟩
  intro y hy
  rw [mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg]
  have hxzero :=
    (mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg
      H u (boundaryDenominator J u) x).mp x.property
  exact ⟨fun i ↦ (hy.2 i).trans (hxzero.1 i),
    fun i ↦ (hy.1 i).le⟩

theorem restrictedExponentialAdjunctionClosedCurve_localConstraint
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (x : restrictedExponentialAdjunctionClosedCurve H D R J) :
    ∃ V ∈ 𝓝 (x : RestrictedSource m p ((a + 1) + 1)),
      V ∩ {y | ∀ i,
        restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)) i y =
          restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)) i x} ⊆
        restrictedExponentialAdjunctionClosedCurve H D R J := by
  exact restrictedClosedDenominatorLocus_localConstraint H
    (restrictedBoundaryFactors D R) J
      (continuous_restrictedBoundaryFactors D R) x

end AbelFormalization

