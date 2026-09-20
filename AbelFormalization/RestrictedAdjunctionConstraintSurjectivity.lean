import AbelFormalization.RestrictedClosedConstraintGeometry

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any invertible square matrix extending the constraint differential by
one row certifies surjectivity of the constraint differential. -/
theorem constraintFDeriv_surjective_of_extendedMatrix_det_ne_zero
    {r : ℕ} (H : Fin r → E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (hrows : ∀ i j, M i.castSucc j = fderiv ℝ (H i) x (basis j))
    (hdet : M.det ≠ 0) :
    (constraintFDeriv H x).range = ⊤ := by
  have hmatrixSurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      (M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  rw [LinearMap.range_eq_top]
  intro y
  let y' : Fin (r + 1) → ℝ :=
    fun i ↦ Fin.lastCases 0 (fun j ↦ y j) i
  obtain ⟨v, hv⟩ := hmatrixSurj y'
  refine ⟨∑ j, v j • basis j, ?_⟩
  ext i
  change fderiv ℝ (H i) x (∑ j, v j • basis j) = y i
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have hi := congrFun hv i.castSucc
  simpa [Matrix.mulVec, dotProduct, y', hrows, mul_comm] using hi

theorem constraintFDeriv_surjective_of_exponentialAdjunctionJacobian_ne_zero
    {n : ℕ} (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ)
    (hJ : exponentialAdjunctionJacobian Ftilde g basis p ≠ 0) :
    (constraintFDeriv (fun i q ↦ Ftilde q i) p).range = ⊤ := by
  apply constraintFDeriv_surjective_of_extendedMatrix_det_ne_zero
    (fun i q ↦ Ftilde q i) (graphProductBasis basis) p
      (exponentialAdjunctionJacobianMatrix Ftilde g basis p)
  · intro i j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp [exponentialAdjunctionJacobianMatrix, graphProductBasis]
    · simp [exponentialAdjunctionJacobianMatrix, graphProductBasis]
  · exact hJ

theorem constraintFDeriv_surjective_of_comp_continuousLinearEquiv
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {r : ℕ} (e : E ≃L[ℝ] E') (H : Fin r → E → ℝ) (x : E')
    (hH : ∀ i, DifferentiableAt ℝ (H i) (e.symm x))
    (hsurj : (constraintFDeriv
      (fun i y ↦ H i (e.symm y)) x).range = ⊤) :
    (constraintFDeriv H (e.symm x)).range = ⊤ := by
  rw [LinearMap.range_eq_top] at hsurj ⊢
  intro z
  obtain ⟨v, hv⟩ := hsurj z
  refine ⟨e.symm v, ?_⟩
  ext i
  have hi := congrFun hv i
  have hchain := (hH i).hasFDerivAt.comp x e.symm.hasFDerivAt
  have heq := hchain.fderiv
  have happ := congrArg (fun L : E' →L[ℝ] ℝ ↦ L v) heq
  change fderiv ℝ (H i) (e.symm x) (e.symm v) = z i
  rw [← hi]
  simpa [constraintFDeriv, Function.comp_def] using happ.symm

theorem restrictedConstraintFDeriv_surjective_of_adjunctionJacobian_ne_zero
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (y : RestrictedSource m p (a + 1))
    (hH : ∀ i, DifferentiableAt ℝ (H i) y)
    (hJ : restrictedExponentialAdjunctionJacobian H g basis y ≠ 0) :
    (constraintFDeriv H y).range = ⊤ := by
  let e : RestrictedSource m p (a + 1) ≃L[ℝ]
      RestrictedSource m p a × ℝ :=
    restrictedSourceAuxOneContinuousLinearEquiv
  have hsurj : (constraintFDeriv
      (fun i q ↦ restrictedSystemProductForm H q i) (e y)).range = ⊤ := by
    apply constraintFDeriv_surjective_of_exponentialAdjunctionJacobian_ne_zero
      (restrictedSystemProductForm H) g basis (e y)
    simpa [restrictedExponentialAdjunctionJacobian, e] using hJ
  have hresult := constraintFDeriv_surjective_of_comp_continuousLinearEquiv
    e H (e y) (by simpa using hH) (by simpa [e, restrictedSystemProductForm] using hsurj)
  simpa using hresult

theorem constraintFDeriv_denominatorProductSystem_surjective
    {r : ℕ} (H : Fin r → E → ℝ) (q : E → ℝ)
    (x : E) (z : ℝ)
    (hH : ∀ i, DifferentiableAt ℝ (H i) x)
    (hq : DifferentiableAt ℝ q x)
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hqne : q x ≠ 0) :
    (constraintFDeriv
      (functionTupleSnoc
        (fun i (p : E × ℝ) ↦ H i p.1)
        (fun p : E × ℝ ↦ p.2 * q p.1 - 1)) (x, z)).range = ⊤ := by
  rw [LinearMap.range_eq_top] at hsurj ⊢
  intro w
  obtain ⟨v, hv⟩ := hsurj (fun i ↦ w i.castSucc)
  let t : ℝ := (w (Fin.last r) - z * fderiv ℝ q x v) / q x
  refine ⟨(v, t), ?_⟩
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [constraintFDeriv]
    change fderiv ℝ
      (functionTupleSnoc (fun i (p : E × ℝ) ↦ H i p.1)
        (fun p : E × ℝ ↦ p.2 * q p.1 - 1) (Fin.last r))
      (x, z) (v, t) = w (Fin.last r)
    rw [functionTupleSnoc_last]
    have hsnd : HasFDerivAt (fun p : E × ℝ ↦ p.2)
        (ContinuousLinearMap.snd ℝ E ℝ) (x, z) :=
      (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
    have hqcomp : HasFDerivAt (fun p : E × ℝ ↦ q p.1)
        ((fderiv ℝ q x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, z) :=
      hq.hasFDerivAt.comp (x, z)
        (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
    have hbottom := (hsnd.mul hqcomp).sub_const (1 : ℝ)
    have hbottomEq : (fun p : E × ℝ ↦ p.2 * q p.1 - 1) =
        (fun p : E × ℝ ↦
          ((fun w : E × ℝ ↦ w.2) * (fun w : E × ℝ ↦ q w.1)) p - 1) := by
      rfl
    rw [hbottomEq]
    rw [hbottom.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul]
    dsimp [t]
    field_simp
    ring
  · rw [constraintFDeriv]
    change fderiv ℝ
      (functionTupleSnoc (fun i (p : E × ℝ) ↦ H i p.1)
        (fun p : E × ℝ ↦ p.2 * q p.1 - 1) j.castSucc)
      (x, z) (v, t) = w j.castSucc
    rw [functionTupleSnoc_castSucc]
    have htop := (hH j).hasFDerivAt.comp (x, z)
      (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
    have htopEq : (fun p : E × ℝ ↦ H j p.1) =
        H j ∘ (ContinuousLinearMap.fst ℝ E ℝ) := by
      rfl
    rw [htopEq, htop.fderiv]
    simpa [constraintFDeriv] using congrFun hv j

theorem restrictedDenominatorSystem_constraintFDeriv_surjective
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p (a + 1))
    (hH : ∀ i, DifferentiableAt ℝ (H i) (restrictedSourceDropAux 1 x))
    (hq : DifferentiableAt ℝ q (restrictedSourceDropAux 1 x))
    (hsurj : (constraintFDeriv H (restrictedSourceDropAux 1 x)).range = ⊤)
    (hqne : q (restrictedSourceDropAux 1 x) ≠ 0)
    (hsystem : ∀ i, DifferentiableAt ℝ
      (restrictedDenominatorSystem H q i) x) :
    (constraintFDeriv (restrictedDenominatorSystem H q) x).range = ⊤ := by
  let e : RestrictedSource m p (a + 1) ≃L[ℝ]
      RestrictedSource m p a × ℝ :=
    restrictedSourceAuxOneContinuousLinearEquiv
  have hprod : (constraintFDeriv
      (functionTupleSnoc
        (fun i (y : RestrictedSource m p a × ℝ) ↦ H i y.1)
        (fun y : RestrictedSource m p a × ℝ ↦ y.2 * q y.1 - 1))
      (e x)).range = ⊤ := by
    apply constraintFDeriv_denominatorProductSystem_surjective
    · simpa [e] using hH
    · simpa [e] using hq
    · simpa [e] using hsurj
    · simpa [e] using hqne
  have hresult := constraintFDeriv_surjective_of_comp_continuousLinearEquiv
    e (restrictedDenominatorSystem H q) (e x) (by simpa using hsystem)
      (by
        have hfun :
            (fun i y ↦ restrictedDenominatorSystem H q i (e.symm y)) =
              functionTupleSnoc
                (fun i (y : RestrictedSource m p a × ℝ) ↦ H i y.1)
                (fun y : RestrictedSource m p a × ℝ ↦ y.2 * q y.1 - 1) := by
          funext i y
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simp [e]
          · simp [e]
        rw [hfun]
        exact hprod)
  simpa using hresult

theorem IsAbel.restrictedAdjunctionClosedCurve_constraintFDeriv_surjective
    {A : ℝ → ℝ} (hA : IsAbel A)
    {ι : Type*} {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a + 1) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (hH : ∀ i, H i ∈ T.level level) (hJ : J ∈ T.level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g basis y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (x : restrictedExponentialAdjunctionClosedCurve H D R J) :
    (constraintFDeriv
      (restrictedDenominatorSystem H
        (boundaryDenominator J (restrictedBoundaryFactors D R)))
      (x : RestrictedSource m p ((a + 1) + 1))).range = ⊤ := by
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  have hxInterior : (x : RestrictedSource m p ((a + 1) + 1)) ∈
      interior (restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset) :=
    restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
      H D R J representative offset hDomain x.property
  have hxJet : (x : RestrictedSource m p ((a + 1) + 1)) ∈
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset := interior_subset hxInterior
  have hyJet : restrictedSourceDropAux 1
      (x : RestrictedSource m p ((a + 1) + 1)) ∈
      restrictedAbelJetDomain (a := a + 1) D representative offset :=
    restrictedSourceDropAux_mem_restrictedAbelJetDomain hxJet
  have hstrict := restrictedClosedDenominatorLocus_boundary_strictPos
    H (restrictedBoundaryFactors D R) J x.property
  have hactualJ : restrictedExponentialAdjunctionJacobian H g basis
      (restrictedSourceDropAux 1
        (x : RestrictedSource m p ((a + 1) + 1))) ≠ 0 := by
    rw [← hJeq _ hyJet]
    exact hstrict.2
  have hHdiff : ∀ i, DifferentiableAt ℝ (H i)
      (restrictedSourceDropAux 1
        (x : RestrictedSource m p ((a + 1) + 1))) := by
    intro i
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset T (hH i) hyJet
  have hHsurj : (constraintFDeriv H
      (restrictedSourceDropAux 1
        (x : RestrictedSource m p ((a + 1) + 1)))).range = ⊤ :=
    restrictedConstraintFDeriv_surjective_of_adjunctionJacobian_ne_zero
      H g basis _ hHdiff hactualJ
  obtain ⟨hqmem, hsystemmem⟩ :=
    T.restrictedExponentialAdjunctionSystem_mem_level
      R level H J hH hJ
  have hqdiff : DifferentiableAt ℝ q
      (restrictedSourceDropAux 1
        (x : RestrictedSource m p ((a + 1) + 1))) := by
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset T hqmem hyJet
  have hqne : q (restrictedSourceDropAux 1
      (x : RestrictedSource m p ((a + 1) + 1))) ≠ 0 :=
    denominatorGraph_denominator_ne_zero q x.property.2.2
  have hsystemdiff : ∀ i, DifferentiableAt ℝ
      (restrictedDenominatorSystem H q i)
      (x : RestrictedSource m p ((a + 1) + 1)) := by
    intro i
    have hmem : restrictedDenominatorSystem H q i ∈
        (T.extendAuxAbel A representative offset 1).level level := by
      rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
      exact hsystemmem i
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset (T.extendAuxAbel A representative offset 1)
      hmem hxJet
  exact restrictedDenominatorSystem_constraintFDeriv_surjective
    H q x hHdiff hqdiff hHsurj hqne hsystemdiff

end AbelFormalization
