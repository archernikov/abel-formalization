import AbelFormalization.DenominatorComparisonSurjectivity
import AbelFormalization.RestrictedAdjunctionCanonicalMorse

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

theorem differentiableAt_restrictedExponentialGraphComparison
    {m p a : ℕ} (g : RestrictedSource m p a → ℝ)
    {y : RestrictedSource m p (a + 1)}
    (hg : DifferentiableAt ℝ g (restrictedSourceDropAux 1 y))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y ≠ 0) :
    DifferentiableAt ℝ (restrictedExponentialGraphComparison g) y := by
  let e : RestrictedSource m p (a + 1) ≃L[ℝ]
      RestrictedSource m p a × ℝ :=
    restrictedSourceAuxOneContinuousLinearEquiv
  have heFst : (e y).1 = restrictedSourceDropAux 1 y := by
    rfl
  have heSnd : (e y).2 =
      restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y := by
    rfl
  have hlog : DifferentiableAt ℝ (fun z : RestrictedSource m p a × ℝ ↦
      Real.log z.2) (e y) :=
    (ContinuousLinearMap.snd ℝ (RestrictedSource m p a) ℝ).differentiableAt.log
      (by simpa [heSnd] using hY)
  have hgcomp : DifferentiableAt ℝ
      (fun z : RestrictedSource m p a × ℝ ↦ g z.1) (e y) :=
    by
      have hg' : DifferentiableAt ℝ g (e y).1 := by
        simpa [heFst] using hg
      exact hg'.comp (e y)
        (ContinuousLinearMap.fst ℝ (RestrictedSource m p a) ℝ).differentiableAt
  have hprod : DifferentiableAt ℝ (exponentialGraphComparison g) (e y) :=
    hlog.sub hgcomp
  have hcomp := hprod.comp y e.differentiableAt
  change DifferentiableAt ℝ
    (fun x ↦ exponentialGraphComparison g (restrictedDenominatorProjection x)) y
  simpa [e, Function.comp_def] using hcomp

theorem hasStrictFDerivAt_exponentialGraphComparison_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) {x : E} {Y : ℝ}
    (hg : HasStrictFDerivAt g (fderiv ℝ g x) x) (hY : Y ≠ 0) :
    HasStrictFDerivAt (exponentialGraphComparison g)
      (fderiv ℝ (exponentialGraphComparison g) (x, Y)) (x, Y) := by
  have hsnd : HasStrictFDerivAt (fun p : E × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ E ℝ) (x, Y) :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasStrictFDerivAt
  have hlog := hsnd.log hY
  have hgcomp : HasStrictFDerivAt (fun p : E × ℝ ↦ g p.1)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, Y) :=
    hg.comp (x, Y) (ContinuousLinearMap.fst ℝ E ℝ).hasStrictFDerivAt
  have hstrict : HasStrictFDerivAt (exponentialGraphComparison g)
      (Y⁻¹ • ContinuousLinearMap.snd ℝ E ℝ -
        (fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, Y) :=
    hlog.sub hgcomp
  rw [fderiv_exponentialGraphComparison_of_ne_zero g
    hg.differentiableAt hY]
  exact hstrict

theorem hasStrictFDerivAt_restrictedExponentialGraphComparison
    {m p a : ℕ} (g : RestrictedSource m p a → ℝ)
    {y : RestrictedSource m p (a + 1)}
    (hg : HasStrictFDerivAt g
      (fderiv ℝ g (restrictedSourceDropAux 1 y))
      (restrictedSourceDropAux 1 y))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y ≠ 0) :
    HasStrictFDerivAt (restrictedExponentialGraphComparison g)
      (fderiv ℝ (restrictedExponentialGraphComparison g) y) y := by
  let e : RestrictedSource m p (a + 1) ≃L[ℝ]
      RestrictedSource m p a × ℝ :=
    restrictedSourceAuxOneContinuousLinearEquiv
  have hprod : HasStrictFDerivAt (exponentialGraphComparison g)
      (fderiv ℝ (exponentialGraphComparison g) (e y)) (e y) := by
    apply hasStrictFDerivAt_exponentialGraphComparison_of_ne_zero
    · simpa [e, restrictedDenominatorProjection] using hg
    · simpa [e, restrictedDenominatorProjection] using hY
  have hcomp := hprod.comp y e.hasStrictFDerivAt
  have hfun : (fun x ↦ exponentialGraphComparison g (e x)) =
      restrictedExponentialGraphComparison g := by
    rfl
  rw [hfun] at hcomp
  rw [hcomp.hasFDerivAt.fderiv]
  exact hcomp

theorem restrictedLogComparison_constraintFDeriv_surjective
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (y : RestrictedSource m p (a + 1))
    (hH : ∀ i, DifferentiableAt ℝ (H i) y)
    (hg : DifferentiableAt ℝ g (restrictedSourceDropAux 1 y))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y ≠ 0)
    (hJ : restrictedExponentialAdjunctionJacobian H g basis y ≠ 0) :
    (constraintFDeriv
      (functionTupleSnoc H (restrictedExponentialGraphComparison g)) y).range = ⊤ := by
  let e : RestrictedSource m p (a + 1) ≃L[ℝ]
      RestrictedSource m p a × ℝ :=
    restrictedSourceAuxOneContinuousLinearEquiv
  have hdet : exponentialLogComparisonJacobian
      (restrictedSystemProductForm H) g basis (e y) ≠ 0 := by
    apply exponentialLogComparisonJacobian_ne_zero_of_ne_zero
    · simpa [e, restrictedDenominatorProjection] using hg
    · simpa [e, restrictedDenominatorProjection] using hY
    · change exponentialAdjunctionJacobian (restrictedSystemProductForm H) g
        basis (restrictedSourceDropAux 1 y,
          restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y) ≠ 0 at hJ
      simpa [e, restrictedDenominatorProjection] using hJ
  have hprod : (constraintFDeriv
      (exponentialLogComparisonTuple (restrictedSystemProductForm H) g)
      (e y)).range = ⊤ :=
    (constraintJacobianInBasis_det_ne_zero_iff_surjective
      (exponentialLogComparisonTuple (restrictedSystemProductForm H) g)
      (graphProductBasis basis) (e y)).mp hdet
  have htupleDiff : ∀ i, DifferentiableAt ℝ
      (functionTupleSnoc H (restrictedExponentialGraphComparison g) i) y := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using differentiableAt_restrictedExponentialGraphComparison
        g hg hY
    · simpa using hH j
  have hfun :
      (fun i z ↦ functionTupleSnoc H
        (restrictedExponentialGraphComparison g) i (e.symm z)) =
      exponentialLogComparisonTuple (restrictedSystemProductForm H) g := by
    funext i z
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [exponentialLogComparisonTuple, restrictedExponentialGraphComparison,
        e]
    · simp [exponentialLogComparisonTuple, restrictedSystemProductForm, e]
  have htransport := constraintFDeriv_surjective_of_comp_continuousLinearEquiv
    e (functionTupleSnoc H (restrictedExponentialGraphComparison g)) (e y)
      (by simpa using htupleDiff) (by rw [hfun]; exact hprod)
  simpa using htransport

theorem restrictedLogComparison_criticalDeterminant_ne_zero
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (comparisonBasis : Module.Basis (Fin (n + 1)) ℝ
      (RestrictedSource m p (a + 1)))
    (y : RestrictedSource m p (a + 1))
    (hH : ∀ i, DifferentiableAt ℝ (H i) y)
    (hg : DifferentiableAt ℝ g (restrictedSourceDropAux 1 y))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y ≠ 0)
    (hJ : restrictedExponentialAdjunctionJacobian H g basis y ≠ 0) :
    criticalDeterminant H (restrictedExponentialGraphComparison g)
      comparisonBasis y ≠ 0 := by
  exact (constraintJacobianInBasis_det_ne_zero_iff_surjective
    (functionTupleSnoc H (restrictedExponentialGraphComparison g))
      comparisonBasis y).mpr
    (restrictedLogComparison_constraintFDeriv_surjective
      H g basis y hH hg hY hJ)

/-- Pull the logarithmic comparison back to the reciprocal-coordinate
realization of the adjunction curve. -/
def restrictedClosedExponentialGraphComparison {m p a : ℕ}
    (g : RestrictedSource m p a → ℝ) :
    RestrictedSource m p ((a + 1) + 1) → ℝ :=
  fun x ↦ restrictedExponentialGraphComparison g
    (restrictedSourceDropAux 1 x)

@[simp]
theorem restrictedClosedExponentialGraphComparison_apply
    {m p a : ℕ} (g : RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p ((a + 1) + 1)) :
    restrictedClosedExponentialGraphComparison g x =
      restrictedExponentialGraphComparison g (restrictedSourceDropAux 1 x) :=
  rfl

def restrictedSourceDropAuxOneContinuousLinearMap {m p a : ℕ} :
    RestrictedSource m p (a + 1) →L[ℝ] RestrictedSource m p a where
  toFun := restrictedSourceDropAux 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_restrictedDenominatorProjection.fst

@[simp]
theorem restrictedSourceDropAuxOneContinuousLinearMap_apply
    {m p a : ℕ} (x : RestrictedSource m p (a + 1)) :
    restrictedSourceDropAuxOneContinuousLinearMap x =
      restrictedSourceDropAux 1 x := rfl

theorem differentiableAt_restrictedClosedExponentialGraphComparison
    {m p a : ℕ} (g : RestrictedSource m p a → ℝ)
    {x : RestrictedSource m p ((a + 1) + 1)}
    (hg : DifferentiableAt ℝ g
      (restrictedSourceDropAux 1 (restrictedSourceDropAux 1 x)))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a)
      (restrictedSourceDropAux 1 x) ≠ 0) :
    DifferentiableAt ℝ
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1) x := by
  have hold := differentiableAt_restrictedExponentialGraphComparison
    g hg hY
  have hcomp := hold.comp x
    (restrictedSourceDropAuxOneContinuousLinearMap
      (m := m) (p := p) (a := a + 1)).differentiableAt
  simpa only [Function.comp_apply,
    restrictedSourceDropAuxOneContinuousLinearMap_apply] using hcomp

theorem hasStrictFDerivAt_restrictedClosedExponentialGraphComparison
    {m p a : ℕ} (g : RestrictedSource m p a → ℝ)
    {x : RestrictedSource m p ((a + 1) + 1)}
    (hg : HasStrictFDerivAt g
      (fderiv ℝ g
        (restrictedSourceDropAux 1 (restrictedSourceDropAux 1 x)))
      (restrictedSourceDropAux 1 (restrictedSourceDropAux 1 x)))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a)
      (restrictedSourceDropAux 1 x) ≠ 0) :
    HasStrictFDerivAt
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1)
      (fderiv ℝ
        (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1) x) x := by
  have hold := hasStrictFDerivAt_restrictedExponentialGraphComparison
    g hg hY
  have hcomp := hold.comp x
    (restrictedSourceDropAuxOneContinuousLinearMap
      (m := m) (p := p) (a := a + 1)).hasStrictFDerivAt
  change HasStrictFDerivAt
    (fun y ↦ restrictedExponentialGraphComparison g (restrictedSourceDropAux 1 y))
    (fderiv ℝ
      (fun y ↦ restrictedExponentialGraphComparison g (restrictedSourceDropAux 1 y)) x) x
  rw [hcomp.hasFDerivAt.fderiv]
  exact hcomp

theorem restrictedClosedLogComparison_criticalDeterminant_ne_zero
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (q : RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (closedBasis : Module.Basis (Fin ((n + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)))
    (x : RestrictedSource m p ((a + 1) + 1))
    (hH : ∀ i, DifferentiableAt ℝ (H i) (restrictedSourceDropAux 1 x))
    (hq : DifferentiableAt ℝ q (restrictedSourceDropAux 1 x))
    (hg : DifferentiableAt ℝ g
      (restrictedSourceDropAux 1 (restrictedSourceDropAux 1 x)))
    (hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a)
      (restrictedSourceDropAux 1 x) ≠ 0)
    (hJ : restrictedExponentialAdjunctionJacobian H g basis
      (restrictedSourceDropAux 1 x) ≠ 0)
    (hqne : q (restrictedSourceDropAux 1 x) ≠ 0)
    (hsystem : ∀ i, DifferentiableAt ℝ
      (restrictedDenominatorSystem H q i) x) :
    criticalDeterminant (restrictedDenominatorSystem H q)
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1)
      closedBasis x ≠ 0 := by
  let h : RestrictedSource m p (a + 1) → ℝ :=
    restrictedExponentialGraphComparison g
  have hh : DifferentiableAt ℝ h (restrictedSourceDropAux 1 x) :=
    differentiableAt_restrictedExponentialGraphComparison g hg hY
  have hbase : (constraintFDeriv (functionTupleSnoc H h)
      (restrictedSourceDropAux 1 x)).range = ⊤ :=
    restrictedLogComparison_constraintFDeriv_surjective
      H g basis (restrictedSourceDropAux 1 x) hH hg hY hJ
  let e : RestrictedSource m p ((a + 1) + 1) ≃L[ℝ]
      RestrictedSource m p (a + 1) × ℝ :=
    restrictedSourceAuxOneContinuousLinearEquiv
  have hprod : (constraintFDeriv
      (denominatorComparisonProductSystem H q h) (e x)).range = ⊤ := by
    apply constraintFDeriv_denominatorComparisonProductSystem_surjective
    · simpa [e, restrictedDenominatorProjection] using hH
    · simpa [e, restrictedDenominatorProjection] using hq
    · simpa [e, restrictedDenominatorProjection] using hh
    · simpa [e, restrictedDenominatorProjection] using hbase
    · simpa [e, restrictedDenominatorProjection] using hqne
  have hcomparison : DifferentiableAt ℝ
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1) x :=
    differentiableAt_restrictedClosedExponentialGraphComparison g hg hY
  have htupleDiff : ∀ i, DifferentiableAt ℝ
      (functionTupleSnoc (restrictedDenominatorSystem H q)
        (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1) i) x := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hcomparison
    · simpa using hsystem j
  have hfun :
      (fun i z ↦ functionTupleSnoc (restrictedDenominatorSystem H q)
        (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1)
          i (e.symm z)) =
      denominatorComparisonProductSystem H q h := by
    funext i z
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [denominatorComparisonProductSystem, h, e]
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simp [denominatorComparisonProductSystem, e]
      · simp [denominatorComparisonProductSystem, e]
  have htransport := constraintFDeriv_surjective_of_comp_continuousLinearEquiv
    e (functionTupleSnoc (restrictedDenominatorSystem H q)
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1)) (e x)
      (by simpa using htupleDiff) (by rw [hfun]; exact hprod)
  apply (constraintJacobianInBasis_det_ne_zero_iff_surjective
    (functionTupleSnoc (restrictedDenominatorSystem H q)
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1))
      closedBasis x).mpr
  simpa using htransport

variable {ι : Type*}

theorem IsAbel.restrictedAdjunctionClosedCurve_logComparisonCriticalDeterminant_ne_zero
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (level : ℕ) (R : ℝ)
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (closedBasis : Module.Basis (Fin ((n + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)))
    (hgmem : g ∈ T.level level)
    (hH : ∀ i, H i ∈
      (T.extendAuxAbel A representative offset 1).level level)
    (hJ : J ∈
      (T.extendAuxAbel A representative offset 1).level level)
    (hJeq : ∀ y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset,
      J y = restrictedExponentialAdjunctionJacobian H g basis y)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (x : restrictedExponentialAdjunctionClosedCurve H D R J) :
    criticalDeterminant
      (restrictedDenominatorSystem H
        (boundaryDenominator J (restrictedBoundaryFactors D R)))
      (restrictedExponentialGraphComparison g ∘ restrictedSourceDropAux 1)
      closedBasis x ≠ 0 := by
  let TE := T.extendAuxAbel A representative offset 1
  let q : RestrictedSource m p (a + 1) → ℝ :=
    boundaryDenominator J (restrictedBoundaryFactors D R)
  let y : RestrictedSource m p (a + 1) := restrictedSourceDropAux 1 x
  have hxInterior : (x : RestrictedSource m p ((a + 1) + 1)) ∈
      interior (restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset) :=
    restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
      H D R J representative offset hDomain x.property
  have hxJet : (x : RestrictedSource m p ((a + 1) + 1)) ∈
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset := interior_subset hxInterior
  have hyJet : y ∈ restrictedAbelJetDomain (a := a + 1)
      D representative offset :=
    restrictedSourceDropAux_mem_restrictedAbelJetDomain hxJet
  have hbaseJet : restrictedSourceDropAux 1 y ∈
      restrictedAbelJetDomain (a := a) D representative offset :=
    restrictedSourceDropAux_mem_restrictedAbelJetDomain hyJet
  have hyCurve : y ∈ restrictedExponentialAdjunctionCurve H D R J := by
    exact restrictedExponentialAdjunctionClosedCurve_drop_mem
      H D R J x.property
  have hyData := (mem_restrictedExponentialAdjunctionCurve_iff
    H D R J y).mp hyCurve
  have hY : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) y ≠ 0 :=
    ne_of_gt hyData.2.1.2.2
  have hactualJ : restrictedExponentialAdjunctionJacobian H g basis y ≠ 0 := by
    rw [← hJeq y hyJet]
    exact hyData.2.2
  have hHdiff : ∀ i, DifferentiableAt ℝ (H i) y := by
    intro i
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset TE (hH i) hyJet
  obtain ⟨hqmem, hsystemmem⟩ :=
    TE.restrictedExponentialAdjunctionSystem_mem_level
      R level H J hH hJ
  have hsystemmemAbel : ∀ i, restrictedDenominatorSystem H q i ∈
      (TE.extendAuxAbel A representative offset 1).level level := by
    intro i
    rw [TE.extendAuxAbel_level_eq_extendAux A representative offset]
    simpa [q] using hsystemmem i
  have hqdiff : DifferentiableAt ℝ q y := by
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset TE hqmem hyJet
  have hgdiff : DifferentiableAt ℝ g (restrictedSourceDropAux 1 y) :=
    hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset T hgmem hbaseJet
  have hqne : q y ≠ 0 :=
    denominatorGraph_denominator_ne_zero q x.property.2.2
  have hsystemdiff : ∀ i, DifferentiableAt ℝ
      (restrictedDenominatorSystem H q i) x := by
    intro i
    exact hA.differentiableAt_of_mem_restrictedAbelTower_level
      representative offset (TE.extendAuxAbel A representative offset 1)
        (hsystemmemAbel i) hxJet
  apply restrictedClosedLogComparison_criticalDeterminant_ne_zero
    H q g basis closedBasis x hHdiff hqdiff hgdiff hY hactualJ hqne
      hsystemdiff

end AbelFormalization
