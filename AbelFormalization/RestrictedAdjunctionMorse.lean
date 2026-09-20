import AbelFormalization.RestrictedAdjunctionFiniteComponents

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem constrainedCriticalPoint_mem_regularZeroSet_of_criticalDeterminant_ne_zero
    {r : ℕ} {M Omega : Set E}
    (H : Fin r → E → ℝ) (rho K : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : M)
    (hxOmega : (x : E) ∈ Omega)
    (hHx : ∀ i, H i x = 0)
    (hKcritical : K x = criticalDeterminant H rho basis x)
    (hxCritical : x ∈ constrainedCriticalSet M H rho basis)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hKdet : criticalDeterminant H K basis x ≠ 0) :
    (x : E) ∈ regularZeroSet Omega (criticalSystemMap H K) := by
  refine ⟨hxOmega, ?_, ?_⟩
  · ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [criticalSystemMap_apply_last]
      exact hKcritical.trans hxCritical
    · rw [criticalSystemMap_apply_castSucc]
      exact hHx j
  · rw [(hasStrictFDerivAt_criticalSystemMap H K x hH hK).hasFDerivAt.fderiv]
    change Function.Surjective
      (constraintFDeriv (functionTupleSnoc H K) x)
    exact LinearMap.range_eq_top.mp
      ((constraintJacobianInBasis_det_ne_zero_iff_surjective
        (functionTupleSnoc H K) basis x).mp hKdet)

variable {ι : Type*}

theorem IsAbel.finite_connectedComponents_restrictedAdjunctionClosedCurve_of_morse
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a + 1) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (criticalBasis : Module.Basis (Fin ((n + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)))
    (rho K : RestrictedSource m p ((a + 1) + 1) → ℝ)
    (hH : ∀ i, H i ∈ T.level level) (hJ : J ∈ T.level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g basis y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (hrhomem : rho ∈
      (T.extendAuxAbel A representative offset 1).level level)
    (hKmem : K ∈
      (T.extendAuxAbel A representative offset 1).level level)
    (hrhocont : Continuous rho)
    (hrhoproper : ∀ c : ℝ, IsCompact {x | rho x ≤ c})
    (hKcritical : ∀ x ∈ restrictedAbelJetDomain
        (a := (a + 1) + 1) D representative offset,
      K x = criticalDeterminant
        (restrictedDenominatorSystem H
          (boundaryDenominator J (restrictedBoundaryFactors D R)))
        rho criticalBasis x)
    (hregularFinite :
      (regularZeroSet
        (restrictedBaseOpenDomain (m := m) (a := (a + 1) + 1) D R)
        (criticalSystemMap
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R))) K)).Finite)
    (hMorse : ∀ x : restrictedExponentialAdjunctionClosedCurve H D R J,
      x ∈ constrainedCriticalSet
        (restrictedExponentialAdjunctionClosedCurve H D R J)
        (restrictedDenominatorSystem H
          (boundaryDenominator J (restrictedBoundaryFactors D R)))
        rho criticalBasis →
      criticalDeterminant
        (restrictedDenominatorSystem H
          (boundaryDenominator J (restrictedBoundaryFactors D R)))
        K criticalBasis x ≠ 0) :
    Finite (ConnectedComponents
      (restrictedExponentialAdjunctionClosedCurve H D R J)) := by
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  obtain ⟨hqmem, hsystemmem⟩ :=
    T.restrictedExponentialAdjunctionSystem_mem_level
      R level H J hH hJ
  have hsystemmemAbel : ∀ i, restrictedDenominatorSystem H q i ∈
      (T.extendAuxAbel A representative offset 1).level level := by
    intro i
    rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
    exact hsystemmem i
  apply hA.finite_connectedComponents_restrictedAdjunctionClosedCurve
    representative offset T level R H J g basis criticalBasis rho K
      hH hJ hJeq hDomain hrhomem hrhocont hrhoproper hregularFinite
  intro x hxCritical
  apply constrainedCriticalPoint_mem_regularZeroSet_of_criticalDeterminant_ne_zero
    (restrictedDenominatorSystem H q) rho K criticalBasis x
  · exact restrictedExponentialAdjunctionClosedCurve_mem_baseOpenDomain
      H D R J x.property
  · exact (mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg
      H (restrictedBoundaryFactors D R) q x).mp x.property |>.1
  · exact hKcritical x (interior_subset
      (restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
        H D R J representative offset hDomain x.property))
  · exact hxCritical
  · intro i
    exact hA.hasStrictFDerivAt_on_restrictedAdjunctionClosedCurve_of_mem
      representative offset T level R H J criticalBasis (0 : Fin ((n + 1) + 1))
        hDomain (hsystemmemAbel i) x
  · exact hA.hasStrictFDerivAt_on_restrictedAdjunctionClosedCurve_of_mem
      representative offset T level R H J criticalBasis (0 : Fin ((n + 1) + 1))
        hDomain hKmem x
  · exact hMorse x hxCritical

end AbelFormalization
