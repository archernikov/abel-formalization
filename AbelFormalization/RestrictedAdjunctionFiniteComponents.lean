import AbelFormalization.RestrictedAdjunctionConstraintSurjectivity

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem restrictedBaseClosedDomain_subset_AbelJetDomain_drop_one
    {m p a : ℕ} {D : RestrictedBox p}
    (R : ℝ) (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a + 1) D R ⊆
      restrictedAbelJetDomain (a := a + 1) D representative offset) :
    restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset := by
  intro x hx
  have happend : restrictedSourceAppendAuxOne x 0 ∈
      restrictedBaseClosedDomain (m := m) (a := a + 1) D R := by
    exact hx
  have hjet := hDomain happend
  have hdrop := restrictedSourceDropAux_mem_restrictedAbelJetDomain hjet
  simpa using hdrop

theorem IsAbel.hasStrictFDerivAt_on_restrictedAdjunctionClosedCurve_of_mem
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
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (basis : Module.Basis κ ℝ
      (RestrictedSource m p ((a + 1) + 1))) (j₀ : κ)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    {f : RestrictedSource m p ((a + 1) + 1) → ℝ}
    (hf : f ∈ (T.extendAuxAbel A representative offset 1).level level)
    (x : restrictedExponentialAdjunctionClosedCurve H D R J) :
    HasStrictFDerivAt f (fderiv ℝ f x) x := by
  apply hA.hasStrictFDerivAt_of_mem_restrictedAbelTower_level_of_mem_interior
    representative offset (T.extendAuxAbel A representative offset 1)
      level basis j₀ hf
  exact restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
    H D R J representative offset hDomain x.property

theorem IsAbel.finite_connectedComponents_restrictedAdjunctionClosedCurve
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
    (hrhocont : Continuous rho)
    (hrhoproper : ∀ c : ℝ, IsCompact {x | rho x ≤ c})
    (hregularFinite :
      (regularZeroSet
        (restrictedBaseOpenDomain (m := m) (a := (a + 1) + 1) D R)
        (criticalSystemMap
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R))) K)).Finite)
    (hcriticalRegular : ∀ x :
        restrictedExponentialAdjunctionClosedCurve H D R J,
      x ∈ constrainedCriticalSet
        (restrictedExponentialAdjunctionClosedCurve H D R J)
        (restrictedDenominatorSystem H
          (boundaryDenominator J (restrictedBoundaryFactors D R)))
        rho criticalBasis →
      (x : RestrictedSource m p ((a + 1) + 1)) ∈ regularZeroSet
        (restrictedBaseOpenDomain (m := m) (a := (a + 1) + 1) D R)
        (criticalSystemMap
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R))) K)) :
    Finite (ConnectedComponents
      (restrictedExponentialAdjunctionClosedCurve H D R J)) := by
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  let M : Set (RestrictedSource m p ((a + 1) + 1)) :=
    restrictedExponentialAdjunctionClosedCurve H D R J
  have hDomainOne : restrictedBaseClosedDomain
      (m := m) (a := a + 1) D R ⊆
      restrictedAbelJetDomain (a := a + 1) D representative offset :=
    restrictedBaseClosedDomain_subset_AbelJetDomain_drop_one
      R representative offset hDomain
  have hMclosed : IsClosed M :=
    hA.isClosed_restrictedExponentialAdjunctionClosedCurve
      representative offset T level R H J hH hJ hDomainOne
  have hcompactM : ∀ c : ℝ, IsCompact {x : M | rho x ≤ c} :=
    fun c ↦ isCompact_subtype_sublevel_of_isClosed
      hMclosed rho hrhoproper c
  obtain ⟨hqmem, hsystemmem⟩ :=
    T.restrictedExponentialAdjunctionSystem_mem_level
      R level H J hH hJ
  have hsystemmemAbel : ∀ i, restrictedDenominatorSystem H q i ∈
      (T.extendAuxAbel A representative offset 1).level level := by
    intro i
    rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
    exact hsystemmem i
  apply finite_connectedComponents_of_finite_regularCriticalSystem_of_surjectiveConstraint
    (restrictedDenominatorSystem H q) rho criticalBasis
      (criticalSystemMap (restrictedDenominatorSystem H q) K)
      hrhocont hcompactM
  · simpa [q, M] using hregularFinite
  · simpa [q, M] using hcriticalRegular
  · intro x
    exact restrictedExponentialAdjunctionClosedCurve_localConstraint
      H D R J x
  · intro x
    exact hA.restrictedAdjunctionClosedCurve_constraintFDeriv_surjective
      representative offset T level R H J g basis hH hJ hJeq hDomain x
  · intro x i
    exact hA.hasStrictFDerivAt_on_restrictedAdjunctionClosedCurve_of_mem
      representative offset T level R H J criticalBasis (0 : Fin ((n + 1) + 1))
        hDomain (hsystemmemAbel i) x
  · intro x
    exact hA.hasStrictFDerivAt_on_restrictedAdjunctionClosedCurve_of_mem
      representative offset T level R H J criticalBasis (0 : Fin ((n + 1) + 1))
        hDomain hrhomem x

end AbelFormalization
