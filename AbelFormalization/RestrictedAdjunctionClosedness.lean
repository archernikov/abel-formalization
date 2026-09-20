import AbelFormalization.RestrictedClosedJetDomain

/-!
# Closedness from jet-domain regularity
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem isClosed_restrictedClosedDenominatorLocus_of_continuousOn
    {m p a r b : ℕ}
    (S : Set (RestrictedSource m p a)) (hS : IsClosed S)
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (hH : ∀ i, ContinuousOn (H i) S)
    (hu : ∀ i, ContinuousOn (u i) S) (hq : ContinuousOn q S)
    (hsub : restrictedClosedDenominatorLocus H u q ⊆
      restrictedSourceDropAux 1 ⁻¹' S) :
    IsClosed (restrictedClosedDenominatorLocus H u q) := by
  have hbaseSub : closedDenominatorLocus H u q ⊆ Prod.fst ⁻¹' S := by
    intro x hx
    have hrestricted : restrictedSourceAppendAuxOne x.1 x.2 ∈
        restrictedClosedDenominatorLocus H u q := by
      rw [appendAuxOne_mem_restrictedClosedDenominatorLocus_iff]
      exact hx
    have hdrop := hsub hrestricted
    simpa using hdrop
  exact (isClosed_closedDenominatorLocus_of_continuousOn
    S hS H u q hH hu hq hbaseSub).preimage
      continuous_restrictedDenominatorProjection

theorem continuousOn_boundaryDenominator
    {X : Type*} [TopologicalSpace X] {b : ℕ}
    (S : Set X) (J : X → ℝ) (u : Fin b → X → ℝ)
    (hJ : ContinuousOn J S) (hu : ∀ i, ContinuousOn (u i) S) :
    ContinuousOn (boundaryDenominator J u) S := by
  apply hJ.mul
  simpa using continuousOn_finsetProd Finset.univ (fun i _ ↦ hu i)

theorem isClosed_restrictedExponentialAdjunctionClosedCurve_of_continuousOn
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ i, ContinuousOn (H i)
      (restrictedBaseClosedDomain (m := m) (a := a + 1) D R))
    (hJ : ContinuousOn J
      (restrictedBaseClosedDomain (m := m) (a := a + 1) D R)) :
    IsClosed (restrictedExponentialAdjunctionClosedCurve H D R J) := by
  let S : Set (RestrictedSource m p (a + 1)) :=
    restrictedBaseClosedDomain D R
  have hu : ∀ i, ContinuousOn (restrictedBoundaryFactors D R i) S :=
    fun i ↦ (continuous_restrictedBoundaryFactors D R i).continuousOn
  have hq : ContinuousOn
      (boundaryDenominator J (restrictedBoundaryFactors D R)) S :=
    continuousOn_boundaryDenominator S J
      (restrictedBoundaryFactors D R) hJ hu
  apply isClosed_restrictedClosedDenominatorLocus_of_continuousOn
    S (isClosed_restrictedBaseClosedDomain D R) H
      (restrictedBoundaryFactors D R)
      (boundaryDenominator J (restrictedBoundaryFactors D R)) hH hu hq
  intro x hx
  change restrictedSourceDropAux 1 x ∈ S
  have hnonneg : ∀ i, 0 ≤ restrictedBoundaryFactors D R i
      (restrictedSourceDropAux 1 x) := hx.2.1
  have hb := (restrictedBoundaryFactors_nonneg_iff D R
    (restrictedSourceDropAux 1 x)).mp hnonneg
  exact ⟨hb.1, hb.2.1⟩

theorem IsAbel.isClosed_restrictedExponentialAdjunctionClosedCurve
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell r : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a + 1) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ k, H k ∈ T.level level) (hJ : J ∈ T.level level)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a + 1) D R ⊆
      restrictedAbelJetDomain (a := a + 1) D representative offset) :
    IsClosed (restrictedExponentialAdjunctionClosedCurve H D R J) := by
  have hHcont : ∀ k, ContinuousOn (H k)
      (restrictedBaseClosedDomain (m := m) (a := a + 1) D R) := by
    intro k x hx
    exact (hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset T (hH k) (hDomain hx)).continuousAt.continuousWithinAt
  have hJcont : ContinuousOn J
      (restrictedBaseClosedDomain (m := m) (a := a + 1) D R) := by
    intro x hx
    exact (hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset T hJ (hDomain hx)).continuousAt.continuousWithinAt
  exact isClosed_restrictedExponentialAdjunctionClosedCurve_of_continuousOn
    H D R J hHcont hJcont

theorem IsAbel.exists_threshold_isClosed_restrictedExponentialAdjunctionClosedCurve
    [Finite ι]
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell r : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a + 1) A representative offset)
      (ell := ell))
    (level : ℕ)
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ k, H k ∈ T.level level) (hJ : J ∈ T.level level) :
    ∃ R : ℝ, IsClosed
      (restrictedExponentialAdjunctionClosedCurve H D R J) := by
  obtain ⟨R, hDomain⟩ :=
    exists_restrictedBaseClosedDomain_subset_AbelJetDomain
      (a := a + 1) D representative offset
  exact ⟨R,
    hA.isClosed_restrictedExponentialAdjunctionClosedCurve
      representative offset T level R H J hH hJ hDomain⟩

theorem isCompact_subtype_sublevel_of_isClosed
    {X : Type*} [TopologicalSpace X]
    {M : Set X} (hM : IsClosed M) (rho : X → ℝ)
    (hcompact : ∀ c : ℝ, IsCompact {x | rho x ≤ c})
    (c : ℝ) : IsCompact {x : M | rho (x : X) ≤ c} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [show ((↑) : M → X) '' {x : M | rho (x : X) ≤ c} =
      M ∩ {x : X | rho x ≤ c} by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxM, hxrho⟩
      exact ⟨⟨x, hxM⟩, hxrho, rfl⟩]
  exact (hcompact c).inter_left hM

end AbelFormalization
