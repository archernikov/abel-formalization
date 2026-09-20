import AbelFormalization.RestrictedTowerDifferentiability
import AbelFormalization.RestrictedLastGeneratorRegularity

/-!
# Complete lower-level package for one exponential adjunction

This file combines polynomial lifting, directional differentiation, and the
regular-zero graph correspondence.  It produces lower-level expressions for
both the lifted system and the manuscript's global determinant and identifies
the original regular zeros with comparison-function zeros on their open
lifted curve.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Replacing a Jacobian by an expression equal to it throughout the common
jet domain leaves the restricted open adjunction curve unchanged. -/
theorem restrictedExponentialAdjunctionCurve_eq_of_eqOn_jetDomain
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (J J' : RestrictedSource m p (a + 1) → ℝ)
    (hDomain : restrictedBaseOpenDomain D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (hJJ' : ∀ y ∈
      restrictedAbelJetDomain (a := a + 1) D representative offset,
        J y = J' y) :
    restrictedExponentialAdjunctionCurve H D R J =
      restrictedExponentialAdjunctionCurve H D R J' := by
  ext y
  rw [mem_restrictedExponentialAdjunctionCurve_iff,
    mem_restrictedExponentialAdjunctionCurve_iff]
  have hyjet :
      ((∀ i, R < y.1.1 i) ∧ y.1.2 ∈ D.openBox ∧
          0 < y.2 (Fin.last a)) →
        y ∈ restrictedAbelJetDomain (a := a + 1) D representative offset := by
    intro hy
    have hbase : restrictedSourceDropAux 1 y ∈
        restrictedAbelJetDomain (a := a) D representative offset := by
      apply hDomain
      exact ⟨hy.1, hy.2.1⟩
    rw [← restrictedSourceAppendAuxOne_projection y]
    exact restrictedSourceAppendAuxOne_mem_restrictedAbelJetDomain
      hbase (restrictedAuxCoordinate (Fin.last a) y)
  constructor
  · rintro ⟨hH, hbounds, hJ⟩
    exact ⟨hH, hbounds, by rwa [← hJJ' y (hyjet hbounds)]⟩
  · rintro ⟨hH, hbounds, hJ'⟩
    exact ⟨hH, hbounds, by rwa [hJJ' y (hyjet hbounds)]⟩

/-- Full algebraic and regular-zero package for eliminating the last
exponential generator.  Both the lifted equations and the global determinant
are expressions at the preceding tower level. -/
theorem IsAbel.exists_restrictedLastGeneratorAdjunctionData
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
    (hDomain : restrictedBaseOpenDomain D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset) :
    ∃ H : Fin n → RestrictedSource m p (a + 1) → ℝ,
      ∃ J : RestrictedSource m p (a + 1) → ℝ,
      (∀ k, H k ∈
        (T.extendAuxAbel A representative offset 1).level i.val) ∧
      J ∈ (T.extendAuxAbel A representative offset 1).level i.val ∧
      (∀ x k,
        H k (restrictedSourceAppendAuxOne x (T.generator i x)) = F k x) ∧
      (∀ y ∈ restrictedAbelJetDomain (a := a + 1) D representative offset,
        J y = restrictedExponentialAdjunctionJacobian H (T.exponent i) basis y) ∧
      Nonempty (
        regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) ≃
          {y : RestrictedSource m p (a + 1) |
            y ∈ restrictedExponentialAdjunctionCurve H D R J ∧
            restrictedExponentialGraphComparison (T.exponent i) y = 0}) := by
  obtain ⟨H, hH, heval⟩ :=
    T.exists_restrictedAbelLastGeneratorSystemLift_of_mem_level_succ
      A representative offset i F hF
  obtain ⟨J, hJ, hJeq⟩ :=
    hA.exists_restrictedExponentialAdjunctionJacobianExpression
      representative offset T i H basis hH
  have hHdiff : ∀ x ∈ restrictedBaseOpenDomain D R,
      DifferentiableAt ℝ (restrictedSystemProductForm H)
        (x, Real.exp (T.exponent i x)) := by
    intro x hx
    exact hA.differentiableAt_restrictedSystemProductForm_of_mem
      representative offset T H hH (hDomain hx) _
  have hgdiff : ∀ x ∈ restrictedBaseOpenDomain D R,
      DifferentiableAt ℝ (T.exponent i) x := by
    intro x hx
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset T (T.exponent_mem i) (hDomain hx)
  let eActual := restrictedRegularZeroSetEquivComparisonZeroOn
    H D R (T.exponent i) basis hHdiff hgdiff
  have hsubst : restrictedExponentialGraphSubstitution H (T.exponent i) =
      constraintMap F :=
    T.restrictedLastGeneratorSystemLift_substitution i H F heval
  have hcurve :
      restrictedExponentialAdjunctionCurve H D R J =
        restrictedExponentialAdjunctionCurve H D R
          (restrictedExponentialAdjunctionJacobian H (T.exponent i) basis) :=
    restrictedExponentialAdjunctionCurve_eq_of_eqOn_jetDomain
      H D R representative offset J
        (restrictedExponentialAdjunctionJacobian H (T.exponent i) basis)
      hDomain hJeq
  have eResult :
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) ≃
        {y : RestrictedSource m p (a + 1) |
          y ∈ restrictedExponentialAdjunctionCurve H D R J ∧
          restrictedExponentialGraphComparison (T.exponent i) y = 0} := by
    rw [← hsubst, hcurve]
    exact eActual
  exact ⟨H, J, hH, hJ, heval, hJeq, ⟨eResult⟩⟩

end AbelFormalization
