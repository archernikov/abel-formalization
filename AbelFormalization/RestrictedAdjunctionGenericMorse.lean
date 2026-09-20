import AbelFormalization.SquaredDistanceGenericMorse
import AbelFormalization.RestrictedAdjunctionConstraintSurjectivity
import AbelFormalization.RestrictedAdjunctionCriticalCoordinates
import AbelFormalization.DirectionalClosureContDiff

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem criticalDeterminant_ne_zero_of_criticalSystemMap_fderiv_surjective
    {r : ℕ} (H : Fin r → E → ℝ) (K : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hH : ∀ i, DifferentiableAt ℝ (H i) x)
    (hK : DifferentiableAt ℝ K x)
    (hsurj : (fderiv ℝ (criticalSystemMap H K) x).range = ⊤) :
    criticalDeterminant H K basis x ≠ 0 := by
  have hmap : HasFDerivAt (criticalSystemMap H K)
      (constraintFDeriv (functionTupleSnoc H K) x) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [criticalSystemMap, constraintFDeriv] using hK.hasFDerivAt
    · simpa [criticalSystemMap, constraintFDeriv] using (hH j).hasFDerivAt
  rw [hmap.fderiv] at hsurj
  exact (constraintJacobianInBasis_det_ne_zero_iff_surjective
    (functionTupleSnoc H K) basis x).mpr hsurj

variable {ι : Type*}

theorem IsAbel.exists_restrictedAdjunctionCenter_regular_explicitCriticalSystem
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
    (hH : ∀ i, H i ∈ T.level level) (hJ : J ∈ T.level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g
        (restrictedSourceBasis m p a) y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset) :
    ∃ center : Fin ((((m + p) + a) + 1) + 1) → ℝ,
      ∀ x ∈ restrictedExponentialAdjunctionClosedCurve H D R J,
        squaredDistanceCriticalEquation
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)))
          (restrictedAdjunctionCriticalBasis m p a) center x = 0 →
        (fderiv ℝ (criticalSystemMap
          (restrictedDenominatorSystem H
            (boundaryDenominator J (restrictedBoundaryFactors D R)))
          (squaredDistanceCriticalEquation
            (restrictedDenominatorSystem H
              (boundaryDenominator J (restrictedBoundaryFactors D R)))
            (restrictedAdjunctionCriticalBasis m p a) center)) x).range = ⊤ := by
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  let C := restrictedDenominatorSystem H q
  let B := restrictedAdjunctionCriticalBasis m p a
  let M : Set (RestrictedSource m p ((a + 1) + 1)) :=
    restrictedExponentialAdjunctionClosedCurve H D R J
  obtain ⟨hqmem, hCmem⟩ :=
    T.restrictedExponentialAdjunctionSystem_mem_level R level H J hH hJ
  have hCmemAbel : ∀ i, C i ∈
      (T.extendAuxAbel A representative offset 1).level level := by
    intro i
    rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
    exact hCmem i
  have hzero : ∀ x ∈ M, ∀ i, C i x = 0 := by
    intro x hx
    exact (mem_restrictedClosedDenominatorLocus_iff_system_zero_and_nonneg
      H (restrictedBoundaryFactors D R) q x).mp hx |>.1
  have hsmooth : ∀ x ∈ M, ∀ i, ContDiffAt ℝ 2 (C i) x := by
    intro x hx i
    have hxInterior : x ∈ interior
        (restrictedAbelJetDomain (a := (a + 1) + 1)
          D representative offset) :=
      restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
        H D R J representative offset hDomain hx
    have hinfty := hA.contDiffOn_infty_of_mem_restrictedAbelTower_level
      representative offset (T.extendAuxAbel A representative offset 1)
      level B (0 : Fin ((((m + p) + a) + 1) + 1)) (hCmemAbel i)
    exact (hinfty.contDiffAt
      (isOpen_interior.mem_nhds hxInterior)).of_le (by simp)
  have hsurj : ∀ x ∈ M, (constraintFDeriv C x).range = ⊤ := by
    intro x hx
    simpa [C, q, M] using
      hA.restrictedAdjunctionClosedCurve_constraintFDeriv_surjective
        representative offset T level R H J g
          (restrictedSourceBasis m p a) hH hJ hJeq hDomain ⟨x, hx⟩
  simpa [q, C, B, M] using
    (exists_squaredDistanceCenter_regular_criticalSystem M C B
      hzero hsmooth hsurj)

theorem IsAbel.exists_restrictedAdjunctionMorseCenter
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
    (hH : ∀ i, H i ∈ T.level level) (hJ : J ∈ T.level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g
        (restrictedSourceBasis m p a) y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset) :
    ∃ center : Fin ((((m + p) + a) + 1) + 1) → ℝ,
      ∀ K : RestrictedSource m p ((a + 1) + 1) → ℝ,
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
            K (restrictedAdjunctionCriticalBasis m p a) x ≠ 0 := by
  obtain ⟨center, hcenter⟩ :=
    hA.exists_restrictedAdjunctionCenter_regular_explicitCriticalSystem
      representative offset T level R H J g hH hJ hJeq hDomain
  refine ⟨center, ?_⟩
  intro K hKeq x hxCritical
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  let C := restrictedDenominatorSystem H q
  let B := restrictedAdjunctionCriticalBasis m p a
  let rho := algebraicSquaredDistance
    (restrictedAdjunctionCriticalCoordinates m p a) center
  let K₀ := squaredDistanceCriticalEquation C B center
  have hK₀eq : ∀ y, K₀ y = criticalDeterminant C rho B y := by
    intro y
    rfl
  have hxInterior : (x : RestrictedSource m p ((a + 1) + 1)) ∈
      interior (restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset) :=
    restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
      H D R J representative offset hDomain x.property
  have hKeqEventually : K =ᶠ[𝓝 (x : RestrictedSource m p ((a + 1) + 1))] K₀ := by
    filter_upwards [isOpen_interior.mem_nhds hxInterior] with y hy
    exact (hKeq y (interior_subset hy)).trans (hK₀eq y).symm
  have hK₀zero : K₀ x = 0 := by
    change criticalDeterminant C rho B x = 0 at hxCritical
    exact (hK₀eq x).trans hxCritical
  have hregular₀ :
      (fderiv ℝ (criticalSystemMap C K₀) x).range = ⊤ := by
    simpa [q, C, B, K₀] using hcenter (x : RestrictedSource m p ((a + 1) + 1))
      x.property hK₀zero
  obtain ⟨hqmem, hCmem⟩ :=
    T.restrictedExponentialAdjunctionSystem_mem_level R level H J hH hJ
  have hCmemAbel : ∀ i, C i ∈
      (T.extendAuxAbel A representative offset 1).level level := by
    intro i
    rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
    exact hCmem i
  have hCtwo : ∀ i, ContDiffAt ℝ 2 (C i) x := by
    intro i
    have hinfty := hA.contDiffOn_infty_of_mem_restrictedAbelTower_level
      representative offset (T.extendAuxAbel A representative offset 1)
      level B (0 : Fin ((((m + p) + a) + 1) + 1)) (hCmemAbel i)
    exact (hinfty.contDiffAt
      (isOpen_interior.mem_nhds hxInterior)).of_le (by simp)
  have hK₀diff : DifferentiableAt ℝ K₀ x := by
    have hfamily := contDiffAt_squaredDistanceCriticalFamily C B x center hCtwo
    have hlast := contDiffAt_pi.mp hfamily
      (Fin.last (((m + p) + a) + 1))
    have hinsert : ContDiffAt ℝ 1
        (fun y : RestrictedSource m p ((a + 1) + 1) => (y, center)) x := by
      fun_prop
    have hcomp := hlast.comp
      (x : RestrictedSource m p ((a + 1) + 1)) hinsert
    have hK₀cont : ContDiffAt ℝ 1 K₀ x := by
      have hfun : (fun y : RestrictedSource m p ((a + 1) + 1) =>
          squaredDistanceCriticalFamily C B (y, center)
            (Fin.last (((m + p) + a) + 1))) = K₀ := by
        funext y
        rw [squaredDistanceCriticalFamily_last]
        rfl
      rw [← hfun]
      simpa [Function.comp_def] using hcomp
    exact hK₀cont.differentiableAt one_ne_zero
  have hdet₀ : criticalDeterminant C K₀ B x ≠ 0 :=
    criticalDeterminant_ne_zero_of_criticalSystemMap_fderiv_surjective
      C K₀ B x (fun i => (hCtwo i).differentiableAt (by norm_num))
        hK₀diff hregular₀
  have hmatrix :
      (fun i j => fderiv ℝ (functionTupleSnoc C K i) x (B j)) =
        (fun i j => fderiv ℝ (functionTupleSnoc C K₀ i) x (B j)) := by
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [functionTupleSnoc_last]
      exact congrArg (fun L : RestrictedSource m p ((a + 1) + 1) →L[ℝ] ℝ =>
        L (B j)) hKeqEventually.fderiv_eq
    · simp only [functionTupleSnoc_castSucc]
  unfold criticalDeterminant at hdet₀ ⊢
  rw [hmatrix]
  exact hdet₀

end AbelFormalization
