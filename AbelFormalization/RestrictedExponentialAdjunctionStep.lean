import AbelFormalization.RestrictedAdjunctionFinitenessBridge
import AbelFormalization.RestrictedSourceSnocBasis
import AbelFormalization.DimensionZeroRegularZeros

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Exponential adjunction after isolating the two geometric facts about the
closed reciprocal curve. -/
theorem IsAbel.finite_regularZeroSet_level_succ_of_adjunctionGeometry_of_index
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (i : Fin ell) (R : ℝ)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (j₀ : Fin n)
    (hF : ∀ k, F k ∈ T.level (i.val + 1))
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (hgeometry : ∀
      (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
      (J : RestrictedSource m p (a + 1) → ℝ),
      (∀ k, H k ∈
        (T.extendAuxAbel A representative offset 1).level i.val) →
      J ∈ (T.extendAuxAbel A representative offset 1).level i.val →
      (∀ y ∈ restrictedAbelJetDomain (a := a + 1)
        D representative offset,
        J y = restrictedExponentialAdjunctionJacobian H (T.exponent i)
          basis y) →
      Finite (ConnectedComponents
          (restrictedExponentialAdjunctionClosedCurve H D R J)) ∧
        (∀ x y : restrictedExponentialAdjunctionClosedCurve H D R J,
          y ∈ connectedComponent x → x ≠ y →
            RegularArcIn
              (restrictedExponentialAdjunctionClosedCurve H D R J) x y)) :
    (regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)).Finite := by
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
  have hOpenDomain : restrictedBaseOpenDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset :=
    (restrictedBaseOpenDomain_subset_closedDomain D R).trans hDomainZero
  obtain ⟨H, J, hH, hJ, heval, hJeq, hequiv⟩ :=
    hA.exists_restrictedLastGeneratorAdjunctionData
      representative offset T i R F basis hF hOpenDomain
  obtain ⟨hfinite, hArc⟩ := hgeometry H J hH hJ hJeq
  exact hA.finite_regularZeroSet_of_restrictedAdjunctionGeometry
    representative offset T i.val R F H J (T.exponent i) basis j₀
      (restrictedSourceAuxTwoBasis basis) (T.exponent_mem i)
      hH hJ hJeq hDomain hequiv hfinite hArc

/-- Exponential adjunction in every source dimension.  In dimension zero the
source is a one-point space; in positive dimension the reciprocal-curve
geometry feeds the comparison-and-Rolle argument. -/
theorem IsAbel.finite_regularZeroSet_level_succ_of_adjunctionGeometry
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (i : Fin ell) (R : ℝ)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (hF : ∀ k, F k ∈ T.level (i.val + 1))
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (hgeometry : ∀
      (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
      (J : RestrictedSource m p (a + 1) → ℝ),
      (∀ k, H k ∈
        (T.extendAuxAbel A representative offset 1).level i.val) →
      J ∈ (T.extendAuxAbel A representative offset 1).level i.val →
      (∀ y ∈ restrictedAbelJetDomain (a := a + 1)
        D representative offset,
        J y = restrictedExponentialAdjunctionJacobian H (T.exponent i)
          basis y) →
      Finite (ConnectedComponents
          (restrictedExponentialAdjunctionClosedCurve H D R J)) ∧
        (∀ x y : restrictedExponentialAdjunctionClosedCurve H D R J,
          y ∈ connectedComponent x → x ≠ y →
            RegularArcIn
              (restrictedExponentialAdjunctionClosedCurve H D R J) x y)) :
    (regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)).Finite := by
  cases n with
  | zero =>
      exact finite_regularZeroSet_of_basis_fin_zero basis _ _
  | succ n =>
      exact hA.finite_regularZeroSet_level_succ_of_adjunctionGeometry_of_index
        representative offset T i R F basis ⟨0, Nat.succ_pos n⟩
          hF hDomain hgeometry

end AbelFormalization
