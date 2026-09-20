import AbelFormalization.RestrictedAdjunctionCriticalCoordinates

/-!
# Canonical critical system for a restricted adjunction curve

This specializes the expression-level critical-system construction to the
canonical coordinates of the twice-enlarged source.  In addition to tower
membership and the exact determinant formula, it proves continuity and
compactness of every squared-distance sublevel.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem IsAbel.exists_restrictedAdjunctionCanonicalCriticalSystem
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a + 1) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (H : Fin ((m + p) + a) → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (center : Fin ((((m + p) + a) + 1) + 1) → ℝ)
    (hH : ∀ k, H k ∈ T.level level) (hJ : J ∈ T.level level) :
    ∃ q : RestrictedSource m p (a + 1) → ℝ,
      ∃ rho K : RestrictedSource m p ((a + 1) + 1) → ℝ,
      ∃ derivative :
        Matrix (Fin ((((m + p) + a) + 1) + 1))
          (Fin ((((m + p) + a) + 1) + 1))
          (RestrictedSource m p ((a + 1) + 1) → ℝ),
      q = boundaryDenominator J (restrictedBoundaryFactors D R) ∧
      q ∈ T.level level ∧
      rho = algebraicSquaredDistance
        (restrictedAdjunctionCriticalCoordinates m p a) center ∧
      rho ∈ (T.extendAuxAbel A representative offset 1).level level ∧
      K ∈ (T.extendAuxAbel A representative offset 1).level level ∧
      (∀ k, functionTupleSnoc (restrictedDenominatorSystem H q) K k ∈
        (T.extendAuxAbel A representative offset 1).level level) ∧
      (∀ i j, derivative i j ∈
        (T.extendAuxAbel A representative offset 1).level level) ∧
      (∀ x ∈ restrictedAbelJetDomain (a := (a + 1) + 1)
          D representative offset,
        ∀ i j,
          DifferentiableAt ℝ
            (functionTupleSnoc (restrictedDenominatorSystem H q) rho i) x ∧
          derivative i j x = fderiv ℝ
            (functionTupleSnoc (restrictedDenominatorSystem H q) rho i) x
              (restrictedAdjunctionCriticalBasis m p a j)) ∧
      (∀ x ∈ restrictedAbelJetDomain (a := (a + 1) + 1)
          D representative offset,
        K x = Matrix.det (fun i j ↦ fderiv ℝ
          (functionTupleSnoc (restrictedDenominatorSystem H q) rho i) x
            (restrictedAdjunctionCriticalBasis m p a j))) ∧
      Continuous rho ∧
      (∀ c : ℝ, IsCompact {x | rho x ≤ c}) := by
  have hcoordinate : ∀ k, restrictedAdjunctionCriticalCoordinates m p a k ∈
      (T.extendAuxAbel A representative offset 1).level level :=
    restrictedAdjunctionCriticalCoordinates_mem_level representative offset
      (T.extendAuxAbel A representative offset 1) level
  obtain ⟨q, rho, K, derivative, hqdef, hqmem, hrhodef, hrhomem,
      hKmem, htuple, hderivative, hderivEq, hKEq⟩ :=
    hA.exists_restrictedAdjunctionCriticalSystemExpressions
      representative offset T level R H J
      (restrictedAdjunctionCriticalBasis m p a)
      (restrictedAdjunctionCriticalCoordinates m p a) center hH hJ hcoordinate
  have hrhocont : Continuous rho := by
    rw [hrhodef]
    rw [show algebraicSquaredDistance
        (restrictedAdjunctionCriticalCoordinates m p a) center =
        fun x ↦ ∑ i,
          (restrictedAdjunctionCriticalCoordinates m p a i x - center i) ^ 2 by
      funext x
      exact algebraicSquaredDistance_apply _ _ x]
    apply continuous_finsetSum Finset.univ
    intro i hi
    have hcoord : Continuous
        (restrictedAdjunctionCriticalCoordinates m p a i) := by
      exact (continuous_apply i).comp
        (LinearEquiv.toContinuousLinearEquiv
          (restrictedAdjunctionCriticalBasis m p a).equivFun).continuous
    exact (hcoord.sub continuous_const).pow 2
  have hrhoproper : ∀ c : ℝ, IsCompact {x | rho x ≤ c} := by
    intro c
    rw [hrhodef]
    exact isCompact_restrictedAdjunctionCriticalSquaredDistance_sublevel
      m p a center c
  exact ⟨q, rho, K, derivative, hqdef, hqmem, hrhodef, hrhomem,
    hKmem, htuple, hderivative, hderivEq, hKEq, hrhocont, hrhoproper⟩

end AbelFormalization
