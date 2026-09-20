import AbelFormalization.NormalizedCofactorTrajectory
import AbelFormalization.RestrictedComparisonTransversality
import AbelFormalization.DirectionalClosureContDiff

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-!
This theorem is the normalized-cofactor specialization that discharges the
`hArc` argument formerly required by
`IsAbel.finite_regularZeroSet_level_succ_of_canonicalMorse`.

The fixed ODE domain is the intersection of the interior of the twice-lifted
Abel-jet domain with the positive half-space for the graph coordinate `Y`.
Every point of the closed reciprocal curve belongs to this open set.  On it,
the denominator system is `C^∞` because it belongs to the twice-extended
tower, and the logarithmic comparison is `C^∞` because it is
`log Y - T.exponent i` (with the exponent pulled back twice).
-/

/-- Two distinct points in one connected component of the restricted closed
adjunction curve can be joined by a regular arc in that curve. -/
theorem IsAbel.regularArcIn_restrictedExponentialAdjunctionClosedCurve_of_mem_connectedComponent
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (i : Fin ell) (R : ℝ)
    (H : Fin ((m + p) + a) → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ k, H k ∈
      (T.extendAuxAbel A representative offset 1).level i.val)
    (hJ : J ∈
      (T.extendAuxAbel A representative offset 1).level i.val)
    (hJeq : ∀ z ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J z = restrictedExponentialAdjunctionJacobian H (T.exponent i)
        (restrictedSourceBasis m p a) z)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (x y : restrictedExponentialAdjunctionClosedCurve H D R J)
    (hy : y ∈ connectedComponent x) (hxy : x ≠ y) :
    RegularArcIn
      (restrictedExponentialAdjunctionClosedCurve H D R J) x y := by
  let TE := T.extendAuxAbel A representative offset 1
  let TEE := TE.extendAuxAbel A representative offset 1
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  let G : Fin (((m + p) + a) + 1) →
      RestrictedSource m p ((a + 1) + 1) → ℝ :=
    restrictedDenominatorSystem H q
  let h : RestrictedSource m p ((a + 1) + 1) → ℝ :=
    restrictedExponentialGraphComparison (T.exponent i) ∘
      restrictedSourceDropAux 1
  let B : Module.Basis (Fin ((((m + p) + a) + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)) :=
    restrictedAdjunctionCriticalBasis m p a
  let M : Set (RestrictedSource m p ((a + 1) + 1)) :=
    restrictedExponentialAdjunctionClosedCurve H D R J

  -- `Y` is the graph coordinate, i.e. the last coordinate before adjoining
  -- the reciprocal variable.
  let drop : RestrictedSource m p ((a + 1) + 1) →L[ℝ]
      RestrictedSource m p (a + 1) :=
    restrictedSourceDropAuxOneContinuousLinearMap
      (m := m) (p := p) (a := a + 1)
  let Y : RestrictedSource m p ((a + 1) + 1) →L[ℝ] ℝ :=
    (restrictedAuxCoordinateCLM (m := m) (p := p) (Fin.last a)).comp drop

  -- This is a single fixed open set, independent of the point of `M`.
  let Ω : Set (RestrictedSource m p ((a + 1) + 1)) :=
    interior (restrictedAbelJetDomain (a := (a + 1) + 1)
      D representative offset) ∩ {z | 0 < Y z}
  have hΩopen : IsOpen Ω := by
    apply isOpen_interior.inter
    exact isOpen_lt continuous_const Y.continuous
  have hMΩ : ∀ z ∈ M, z ∈ Ω := by
    intro z hz
    have hzClosed : z ∈
        restrictedExponentialAdjunctionClosedCurve H D R J := by
      simpa only [M] using hz
    have hzInterior : z ∈ interior
        (restrictedAbelJetDomain (a := (a + 1) + 1)
          D representative offset) :=
      restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
        H D R J representative offset hDomain hzClosed
    have hzCurve : restrictedSourceDropAux 1 z ∈
        restrictedExponentialAdjunctionCurve H D R J :=
      restrictedExponentialAdjunctionClosedCurve_drop_mem
        H D R J hzClosed
    have hzData := (mem_restrictedExponentialAdjunctionCurve_iff
      H D R J (restrictedSourceDropAux 1 z)).mp hzCurve
    have hYpos : 0 < restrictedAuxCoordinate
        (m := m) (p := p) (Fin.last a) (restrictedSourceDropAux 1 z) :=
      hzData.2.1.2.2
    refine ⟨hzInterior, ?_⟩
    change 0 < Y z
    simpa only [Y, drop, ContinuousLinearMap.comp_apply,
      restrictedAuxCoordinateCLM_apply, restrictedAuxCoordinate,
      restrictedSourceDropAuxOneContinuousLinearMap_apply] using hYpos
  have hΩ : ∀ z ∈ M, Ω ∈ 𝓝 z := by
    intro z hz
    exact hΩopen.mem_nhds (hMΩ z hz)

  obtain ⟨hqmem, hsystemmem⟩ :=
    TE.restrictedExponentialAdjunctionSystem_mem_level
      R i.val H J hH hJ
  have hGmem : ∀ k, G k ∈ TEE.level i.val := by
    intro k
    dsimp only [TEE]
    rw [TE.extendAuxAbel_level_eq_extendAux A representative offset]
    simpa only [G, q] using hsystemmem k

  -- All denominator equations are `C²` on the same fixed open set `Ω`.
  have hGinf : ∀ k, ContDiffOn ℝ ∞ (G k)
      (interior (restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)) := by
    intro k
    exact hA.contDiffOn_infty_of_mem_restrictedAbelTower_level
      representative offset TEE i.val B
        (0 : Fin ((((m + p) + a) + 1) + 1)) (hGmem k)
  have hGtwo : ∀ z ∈ Ω, ∀ k, ContDiffAt ℝ 2 (G k) z := by
    intro z hz k
    exact ((hGinf k).contDiffAt
      (isOpen_interior.mem_nhds hz.1)).of_le (by simp)

  -- The twice-extended exponent is definitionally the original exponent
  -- pulled back along the two successive `restrictedSourceDropAux 1` maps.
  let g₂ : RestrictedSource m p ((a + 1) + 1) → ℝ := TEE.exponent i
  have hg₂inf : ContDiffOn ℝ ∞ g₂
      (interior (restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)) := by
    exact hA.contDiffOn_infty_of_mem_restrictedAbelTower_level
      representative offset TEE i.val B
        (0 : Fin ((((m + p) + a) + 1) + 1)) (TEE.exponent_mem i)
  have hfun : h = fun z => Real.log (Y z) - g₂ z := by
    funext z
    simp [h, Y, drop, g₂, TEE, TE,
      restrictedExponentialGraphComparison, exponentialGraphComparison,
      restrictedDenominatorProjection, restrictedAuxCoordinate,
      restrictedSourceDropAux_aux, Function.comp_def]
  have hhtwo : ∀ z ∈ Ω, ContDiffAt ℝ 2 h z := by
    intro z hz
    have hYtwo : ContDiffAt ℝ 2 (fun w => Y w) z :=
      Y.contDiff.contDiffAt
    have hg₂two : ContDiffAt ℝ 2 g₂ z :=
      (hg₂inf.contDiffAt (isOpen_interior.mem_nhds hz.1)).of_le (by simp)
    rw [hfun]
    exact (hYtwo.log (ne_of_gt hz.2)).sub hg₂two

  -- The defining equations vanish on the closed reciprocal curve.
  have hMzero : ∀ z ∈ M, ∀ k, G k z = 0 := by
    intro z hz k
    have hzClosed : z ∈
        restrictedExponentialAdjunctionClosedCurve H D R J := by
      simpa only [M] using hz
    have hzero :=
      (mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg
        H (restrictedBoundaryFactors D R)
          (boundaryDenominator J (restrictedBoundaryFactors D R)) z).mp
        hzClosed
    simpa only [G, q] using hzero.1 k

  -- Transversality of the logarithmic comparison is exactly the determinant
  -- input needed by the normalized cofactor field.
  have hdet : ∀ z ∈ M, criticalDeterminant G h B z ≠ 0 := by
    intro z hz
    have hdetz :=
      hA.restrictedAdjunctionClosedCurve_logComparisonCriticalDeterminant_ne_zero
        representative offset T i.val R H J (T.exponent i)
          (restrictedSourceBasis m p a)
          (restrictedAdjunctionCriticalBasis m p a)
          (T.exponent_mem i) hH hJ hJeq hDomain
          ⟨z, by simpa only [M] using hz⟩
    simpa only [G, h, B, q, M] using hdetz

  have hlocalConstraint : ∀ z : M, ∃ U ∈ 𝓝
      (z : RestrictedSource m p ((a + 1) + 1)),
      U ∩ {w | ∀ k, G k w = G k z} ⊆ M := by
    intro z
    simpa only [G, q, M] using
      restrictedExponentialAdjunctionClosedCurve_localConstraint H D R J z

  change RegularArcIn M x y
  exact regularArcIn_of_mem_connectedComponent_normalizedCofactor
    G h B hΩ hGtwo hhtwo hdet hMzero hlocalConstraint x y hy hxy

end AbelFormalization
