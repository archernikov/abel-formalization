import AbelFormalization.RestrictedAdjunctionMorse

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem IsAbel.finite_connectedComponents_restrictedAdjunctionClosedCurve_of_canonical_morse
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
    (g : RestrictedSource m p a → ℝ)
    (center : Fin ((((m + p) + a) + 1) + 1) → ℝ)
    (hH : ∀ i, H i ∈ T.level level) (hJ : J ∈ T.level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g
        (restrictedSourceBasis m p a) y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (hregularFinite : ∀ F :
        RestrictedSource m p ((a + 1) + 1) →
          Fin ((((m + p) + a) + 1) + 1) → ℝ,
      (∀ k, (fun x ↦ F x k) ∈
        (T.extendAuxAbel A representative offset 1).level level) →
      (regularZeroSet
        (restrictedBaseOpenDomain (m := m) (a := (a + 1) + 1) D R)
        F).Finite)
    (hMorse : ∀ K : RestrictedSource m p ((a + 1) + 1) → ℝ,
      (∀ y ∈ restrictedAbelJetDomain (a := (a + 1) + 1)
          D representative offset,
        K y = criticalDeterminant
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)))
          (algebraicSquaredDistance
            (restrictedAdjunctionCriticalCoordinates m p a) center)
          (restrictedAdjunctionCriticalBasis m p a) y) →
      ∀ x : restrictedExponentialAdjunctionClosedCurve H D R J,
        x ∈ constrainedCriticalSet
          (restrictedExponentialAdjunctionClosedCurve H D R J)
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)))
          (algebraicSquaredDistance
            (restrictedAdjunctionCriticalCoordinates m p a) center)
          (restrictedAdjunctionCriticalBasis m p a) →
        criticalDeterminant
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)))
          K (restrictedAdjunctionCriticalBasis m p a) x ≠ 0) :
    Finite (ConnectedComponents
      (restrictedExponentialAdjunctionClosedCurve H D R J)) := by
  obtain ⟨q, rho, K, derivative, hqdef, hqmem, hrhodef, hrhomem,
      hKmem, htuple, hderivative, hderivEq, hKEq, hrhocont, hrhoproper⟩ :=
    hA.exists_restrictedAdjunctionCanonicalCriticalSystem
      representative offset T level R H J center hH hJ
  subst q
  subst rho
  apply hA.finite_connectedComponents_restrictedAdjunctionClosedCurve_of_morse
    representative offset T level R H J g
      (restrictedSourceBasis m p a)
      (restrictedAdjunctionCriticalBasis m p a)
      (algebraicSquaredDistance
        (restrictedAdjunctionCriticalCoordinates m p a) center)
      K hH hJ hJeq hDomain hrhomem hKmem hrhocont hrhoproper
  · intro y hy
    simpa [criticalDeterminant] using hKEq y hy
  · apply hregularFinite
    intro k
    simpa [criticalSystemMap] using htuple k
  · exact hMorse K (by
      intro y hy
      simpa [criticalDeterminant] using hKEq y hy)

end AbelFormalization
