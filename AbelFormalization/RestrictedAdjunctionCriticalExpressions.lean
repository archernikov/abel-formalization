import AbelFormalization.RestrictedSourceBasis

/-!
# Critical-system expressions after exponential adjunction

The reciprocal boundary equation and the squared-distance critical system
are obtained by polynomial operations and directional differentiation.  This
file packages the fact that every resulting equation remains at the lower
exponential level after the two fresh auxiliary variables are added.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- The denominator equation and the whole squared-distance critical system
remain at the preceding exponential level. -/
theorem IsAbel.exists_restrictedAdjunctionCriticalSystemExpressions
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
    (basis : Fin ((n + 1) + 1) → RestrictedSource m p ((a + 1) + 1))
    (coordinate : Fin ((n + 1) + 1) →
      RestrictedSource m p ((a + 1) + 1) → ℝ)
    (center : Fin ((n + 1) + 1) → ℝ)
    (hH : ∀ k, H k ∈ T.level level) (hJ : J ∈ T.level level)
    (hcoordinate : ∀ k, coordinate k ∈
      (T.extendAuxAbel A representative offset 1).level level) :
    ∃ q : RestrictedSource m p (a + 1) → ℝ,
      ∃ rho K : RestrictedSource m p ((a + 1) + 1) → ℝ,
      ∃ derivative : Matrix (Fin ((n + 1) + 1)) (Fin ((n + 1) + 1))
        (RestrictedSource m p ((a + 1) + 1) → ℝ),
      q = boundaryDenominator J (restrictedBoundaryFactors D R) ∧
      q ∈ T.level level ∧
      rho = algebraicSquaredDistance coordinate center ∧
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
              (basis j)) ∧
      (∀ x ∈ restrictedAbelJetDomain (a := (a + 1) + 1)
          D representative offset,
        K x = Matrix.det (fun i j ↦ fderiv ℝ
          (functionTupleSnoc (restrictedDenominatorSystem H q) rho i) x
            (basis j))) := by
  let q := boundaryDenominator J (restrictedBoundaryFactors D R)
  obtain ⟨hq, hsystem⟩ :=
    T.restrictedExponentialAdjunctionSystem_mem_level R level H J hH hJ
  have hsystemAbel : ∀ k, restrictedDenominatorSystem H q k ∈
      (T.extendAuxAbel A representative offset 1).level level := by
    intro k
    rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
    exact hsystem k
  obtain ⟨rho, K, derivative, hrho, hrhomem, hKmem, htuple,
      hderivative, hderivEq, hKEq⟩ :=
    hA.exists_restrictedAbelTower_criticalSystemExpressions
      representative offset (T.extendAuxAbel A representative offset 1)
      level (restrictedDenominatorSystem H q) basis coordinate center
      hsystemAbel hcoordinate
  exact ⟨q, rho, K, derivative, rfl, hq, hrho, hrhomem, hKmem,
    htuple, hderivative, hderivEq, hKEq⟩

end AbelFormalization
