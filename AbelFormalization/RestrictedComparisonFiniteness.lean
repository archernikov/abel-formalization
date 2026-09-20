import AbelFormalization.FiniteComparisonFromComponents

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem IsAbel.finite_restrictedAdjunctionClosedCurve_comparisonZeroSet
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (j₀ : Fin n)
    (closedBasis : Module.Basis (Fin ((n + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)))
    (hgmem : g ∈ T.level level)
    (hH : ∀ i, H i ∈
      (T.extendAuxAbel A representative offset 1).level level)
    (hJ : J ∈
      (T.extendAuxAbel A representative offset 1).level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g basis y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (hfinite : Finite (ConnectedComponents
      (restrictedExponentialAdjunctionClosedCurve H D R J)))
    (hArc : ∀ x y : restrictedExponentialAdjunctionClosedCurve H D R J,
      y ∈ connectedComponent x → x ≠ y →
        RegularArcIn (restrictedExponentialAdjunctionClosedCurve H D R J) x y) :
    ({x : restrictedExponentialAdjunctionClosedCurve H D R J |
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1) x = 0} :
      Set (restrictedExponentialAdjunctionClosedCurve H D R J)).Finite := by
  let TE := T.extendAuxAbel A representative offset 1
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  let G := restrictedDenominatorSystem H q
  let h := restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1
  let M := restrictedExponentialAdjunctionClosedCurve H D R J
  obtain ⟨hqmem, hsystemmem⟩ :=
    TE.restrictedExponentialAdjunctionSystem_mem_level R level H J hH hJ
  have hsystemmemAbel : ∀ i, G i ∈
      (TE.extendAuxAbel A representative offset 1).level level := by
    intro i
    rw [TE.extendAuxAbel_level_eq_extendAux A representative offset]
    simpa [G, q] using hsystemmem i
  have hMzero : ∀ x : M, ∀ i, G i x = 0 := by
    intro x i
    have hx : (x : RestrictedSource m p ((a + 1) + 1)) ∈
        restrictedExponentialAdjunctionClosedCurve H D R J := x.property
    have hzero :=
      (mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg
        H (restrictedBoundaryFactors D R)
          (boundaryDenominator J (restrictedBoundaryFactors D R)) x).mp hx
    simpa [G, q] using hzero.1 i
  have hGstrict : ∀ x : M, ∀ i,
      HasStrictFDerivAt (G i) (fderiv ℝ (G i) x) x := by
    intro x i
    exact hA.hasStrictFDerivAt_on_restrictedAdjunctionClosedCurve_of_mem
      representative offset TE level R H J closedBasis
        (0 : Fin ((n + 1) + 1)) hDomain (hsystemmemAbel i) x
  have hDomainOne : restrictedBaseClosedDomain
      (m := m) (a := a + 1) D R ⊆
      restrictedAbelJetDomain (a := a + 1) D representative offset :=
    restrictedBaseClosedDomain_subset_AbelJetDomain_drop_one
      R representative offset hDomain
  have hDomainZero : restrictedBaseClosedDomain
      (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset :=
    restrictedBaseClosedDomain_subset_AbelJetDomain_drop_one
      R representative offset hDomainOne
  have hhstrict : ∀ x : M,
      HasStrictFDerivAt h (fderiv ℝ h x) x := by
    intro x
    have hyCurve : restrictedSourceDropAux 1
        (x : RestrictedSource m p ((a + 1) + 1)) ∈
        restrictedExponentialAdjunctionCurve H D R J :=
      restrictedExponentialAdjunctionClosedCurve_drop_mem
        H D R J (by simpa [M] using x.property)
    have hyData := (mem_restrictedExponentialAdjunctionCurve_iff
      H D R J _).mp hyCurve
    have hbaseOpen : restrictedSourceDropAux 1
        (restrictedSourceDropAux 1
          (x : RestrictedSource m p ((a + 1) + 1))) ∈
        restrictedBaseOpenDomain D R :=
      ⟨hyData.2.1.1, hyData.2.1.2.1⟩
    have hbaseInterior :=
      restrictedBaseOpenDomain_subset_interior_AbelJetDomain
        D R representative offset hDomainZero hbaseOpen
    have hgstrict :=
      hA.hasStrictFDerivAt_of_mem_restrictedAbelTower_level_of_mem_interior
        representative offset T level basis j₀ hgmem hbaseInterior
    have hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a)
        (restrictedSourceDropAux 1
          (x : RestrictedSource m p ((a + 1) + 1))) ≠ 0 :=
      ne_of_gt hyData.2.1.2.2
    simpa [h] using
      (hasStrictFDerivAt_restrictedClosedExponentialGraphComparison
        g hgstrict hY)
  have hdet : ∀ x : M, criticalDeterminant G h closedBasis x ≠ 0 := by
    intro x
    simpa [G, h, q, M] using
      hA.restrictedAdjunctionClosedCurve_logComparisonCriticalDeterminant_ne_zero
        representative offset T level R H J g basis closedBasis
          hgmem hH hJ hJeq hDomain x
  apply finite_comparisonZeroSet_of_finite_components_of_cofactor
    G h closedBasis (by simpa [M] using hfinite) hMzero
      (by simpa [M] using hArc) hGstrict hhstrict hdet

end AbelFormalization
