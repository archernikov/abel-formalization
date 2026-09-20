import AbelFormalization.RestrictedBoundaryFactors

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- The paper's open lifted curve before adjoining the reciprocal coordinate. -/
def restrictedExponentialAdjunctionCurve {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ) :
    Set (RestrictedSource m p (a + 1)) :=
  restrictedOpenDenominatorLocus H (restrictedBoundaryFactors D R) J

theorem mem_restrictedExponentialAdjunctionCurve_iff
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (x : RestrictedSource m p (a + 1)) :
    x ∈ restrictedExponentialAdjunctionCurve H D R J ↔
      (∀ i, H i x = 0) ∧
        ((∀ i, R < x.1.1 i) ∧ x.1.2 ∈ D.openBox ∧
          0 < x.2 (Fin.last a)) ∧ J x ≠ 0 := by
  change ((∀ i, H i x = 0) ∧
      (∀ i, 0 < restrictedBoundaryFactors D R i x) ∧ J x ≠ 0) ↔ _
  rw [restrictedBoundaryFactors_pos_iff]

/-- The paper's closed reciprocal realization of the lifted curve. -/
def restrictedExponentialAdjunctionClosedCurve {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ) :
    Set (RestrictedSource m p ((a + 1) + 1)) :=
  restrictedClosedDenominatorLocus H (restrictedBoundaryFactors D R)
    (boundaryDenominator J (restrictedBoundaryFactors D R))

theorem isClosed_restrictedExponentialAdjunctionClosedCurve
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ i, Continuous (H i)) (hJ : Continuous J) :
    IsClosed (restrictedExponentialAdjunctionClosedCurve H D R J) := by
  apply isClosed_restrictedClosedDenominatorLocus
  · exact hH
  · exact continuous_restrictedBoundaryFactors D R
  · exact continuous_boundaryDenominator _ _
      (continuous_restrictedBoundaryFactors D R) hJ

/-- The canonical reciprocal lift identifies the open curve with its closed
realization. -/
def restrictedExponentialAdjunctionHomeomorph
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hJ : Continuous J) :
    restrictedExponentialAdjunctionCurve H D R J ≃ₜ
      restrictedExponentialAdjunctionClosedCurve H D R J :=
  restrictedOpenClosedDenominatorHomeomorph
    H (restrictedBoundaryFactors D R) J
      (continuous_restrictedBoundaryFactors D R) hJ

theorem restrictedExponentialAdjunctionClosedCurve_drop_mem
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    {x : RestrictedSource m p ((a + 1) + 1)}
    (hx : x ∈ restrictedExponentialAdjunctionClosedCurve H D R J) :
    restrictedSourceDropAux 1 x ∈
      restrictedExponentialAdjunctionCurve H D R J := by
  exact (restrictedCanonicalDenominatorDrop H
    (restrictedBoundaryFactors D R) J ⟨x, hx⟩).property

/-- The concrete denominator and every equation defining the closed curve
remain at the same exponential-tower level. -/
theorem RestrictedExpressionTower.restrictedExponentialAdjunctionSystem_mem_level
    {m p a ell r : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p (a + 1) → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (R : ℝ) (level : ℕ)
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ i, H i ∈ T.level level) (hJ : J ∈ T.level level) :
    boundaryDenominator J (restrictedBoundaryFactors D R) ∈ T.level level ∧
      ∀ i, restrictedDenominatorSystem H
          (boundaryDenominator J (restrictedBoundaryFactors D R)) i ∈
        (T.extendAux 1).level level := by
  have hu : ∀ i, restrictedBoundaryFactors D R i ∈ T.level level :=
    T.restrictedBoundaryFactors_mem_level R level
  have hq : boundaryDenominator J (restrictedBoundaryFactors D R) ∈
      T.level level :=
    boundaryDenominator_mem_subalgebra (T.level level) J
      (restrictedBoundaryFactors D R) hJ hu
  exact ⟨hq,
    T.restrictedDenominatorSystem_mem_extendAux_level H _ hH hq⟩

end AbelFormalization
