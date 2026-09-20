import AbelFormalization.RestrictedComparisonLiftFiniteness

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem IsAbel.finite_regularZeroSet_of_restrictedAdjunctionGeometry
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (F : Fin n → RestrictedSource m p a → ℝ)
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
    (hequiv : Nonempty (
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) ≃
        {y : RestrictedSource m p (a + 1) |
          y ∈ restrictedExponentialAdjunctionCurve H D R J ∧
          restrictedExponentialGraphComparison g y = 0}))
    (hfinite : Finite (ConnectedComponents
      (restrictedExponentialAdjunctionClosedCurve H D R J)))
    (hArc : ∀ x y : restrictedExponentialAdjunctionClosedCurve H D R J,
      y ∈ connectedComponent x → x ≠ y →
        RegularArcIn (restrictedExponentialAdjunctionClosedCurve H D R J) x y) :
    (regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)).Finite := by
  have hclosed :=
    hA.finite_restrictedAdjunctionClosedCurve_comparisonZeroSet
      representative offset T level R H J g basis j₀ closedBasis
        hgmem hH hJ hJeq hDomain hfinite hArc
  have hopen : ({y : RestrictedSource m p (a + 1) |
      y ∈ restrictedExponentialAdjunctionCurve H D R J ∧
        restrictedExponentialGraphComparison g y = 0} :
      Set (RestrictedSource m p (a + 1))).Finite := by
    apply finite_openComparisonZero_of_finite_closedComparisonZero
      H (restrictedBoundaryFactors D R) J
        (restrictedExponentialGraphComparison g)
    simpa [restrictedExponentialAdjunctionClosedCurve,
      Function.comp_apply] using hclosed
  exact finite_regularZeroSet_of_equiv_openComparisonZero hequiv hopen

end AbelFormalization
