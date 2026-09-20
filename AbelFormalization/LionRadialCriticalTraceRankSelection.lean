import AbelFormalization.LionRadialParameterTransversality
import AbelFormalization.LionLemma4RegularMinorCover
import AbelFormalization.SquaredDistanceCriticalFamilyContDiff
import AbelFormalization.LionCriticalCoefficientSelectionLinearAlgebra

noncomputable section

open Set Function Filter
open scoped BigOperators ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Coordinate vector representing the Fréchet derivative of a scalar map in
the standard Euclidean basis. -/
def euclideanFDerivCoordinates {n : ℕ}
    (f : RealEuclideanFunction n) (x : RealEuclidean n) :
    RealEuclidean n :=
  fun j ↦ fderiv ℝ f x (Pi.single j 1)

/-- Standard-coordinate form of the logarithmic Lagrange covector for an
objective `rho` and constraints `H`. -/
def euclideanLogLagrangeStationarityCoordinates {n r : ℕ}
    (H : Fin r → RealEuclideanFunction n)
    (rho : RealEuclideanFunction n) (lambda : RealEuclidean r)
    (x : RealEuclidean n) : RealEuclidean n :=
  (rho x)⁻¹ • euclideanFDerivCoordinates rho x -
    ∑ i, lambda i • euclideanFDerivCoordinates (H i) x

/-- At a zero of a vector-valued factor, differentiating a scalar times its
Euclidean pairing with a moving vector only differentiates that factor. -/
theorem fderiv_scalar_mul_euclideanPairing_of_left_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (rho : E → ℝ) (S tau : E → RealEuclidean n)
    (x v : E)
    (hrho : DifferentiableAt ℝ rho x)
    (hS : DifferentiableAt ℝ S x)
    (htau : DifferentiableAt ℝ tau x)
    (hSx : S x = 0) :
    fderiv ℝ (fun y ↦ rho y * ∑ j, S y j * tau y j) x v =
      rho x * ∑ j,
        fderiv ℝ (fun y ↦ S y j) x v * tau x j := by
  have hScoord : ∀ j, DifferentiableAt ℝ (fun y ↦ S y j) x := by
    intro j
    exact (ContinuousLinearMap.proj j :
      RealEuclidean n →L[ℝ] ℝ).differentiableAt.comp x hS
  have htaucoord : ∀ j, DifferentiableAt ℝ (fun y ↦ tau y j) x := by
    intro j
    exact (ContinuousLinearMap.proj j :
      RealEuclidean n →L[ℝ] ℝ).differentiableAt.comp x htau
  have hterm : ∀ j, DifferentiableAt ℝ
      (fun y ↦ S y j * tau y j) x :=
    fun j ↦ (hScoord j).mul (htaucoord j)
  have hsum : DifferentiableAt ℝ
      (fun y ↦ ∑ j, S y j * tau y j) x :=
    DifferentiableAt.fun_sum (fun j _hj ↦ hterm j)
  rw [fderiv_fun_mul hrho hsum, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    fderiv_fun_sum (fun j _hj ↦ hterm j)]
  have hsumZero : (∑ j, S x j * tau x j) = 0 := by
    simp [hSx]
  rw [hsumZero, zero_smul, add_zero]
  simp only [sum_apply, smul_eq_mul]
  apply congrArg (rho x * ·)
  apply Finset.sum_congr rfl
  intro j _hj
  rw [fderiv_fun_mul (hScoord j) (htaucoord j),
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply]
  simp only [hSx, Pi.zero_apply, zero_mul, zero_smul, zero_apply,
    add_zero, smul_eq_mul]
  ring

/-- A critical determinant is the objective value times the pairing of the
logarithmic Lagrange covector with the cofactor tangent.  The constraint
terms disappear because every cofactor tangent lies in the constraint
kernel. -/
theorem criticalDeterminant_eq_scalar_mul_euclideanPairing_logLagrange
    {n r : ℕ} (H : Fin r → RealEuclideanFunction n)
    (rho : RealEuclideanFunction n) (lambda : RealEuclidean r)
    (basis : Fin (r + 1) → RealEuclidean n) (x : RealEuclidean n)
    (hrho0 : rho x ≠ 0) :
    criticalDeterminant H rho basis x =
      rho x * ∑ j,
        euclideanLogLagrangeStationarityCoordinates H rho lambda x j *
          criticalCofactorTangent H (fun _ ↦ 0) basis x j := by
  let tau : RealEuclidean n :=
    criticalCofactorTangent H (fun _ ↦ 0) basis x
  let B : Module.Basis (Fin n) ℝ (RealEuclidean n) :=
    Pi.basisFun ℝ (Fin n)
  have htau : (∑ j, tau j • B j) = tau := by
    simpa only [B, Pi.basisFun_repr] using B.sum_repr tau
  have hrhoExpand :
      (∑ j, fderiv ℝ rho x (B j) * tau j) = fderiv ℝ rho x tau := by
    calc
      ∑ j, fderiv ℝ rho x (B j) * tau j =
          fderiv ℝ rho x (∑ j, tau j • B j) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = fderiv ℝ rho x tau := by rw [htau]
  have hHExpand : ∀ i,
      (∑ j, fderiv ℝ (H i) x (B j) * tau j) = 0 := by
    intro i
    calc
      ∑ j, fderiv ℝ (H i) x (B j) * tau j =
          fderiv ℝ (H i) x (∑ j, tau j • B j) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = fderiv ℝ (H i) x tau := by rw [htau]
      _ = 0 := fderiv_constraint_criticalCofactorTangent_eq_zero
        H (fun _ ↦ 0) basis x i
  have hsum :
      (∑ j, ((rho x)⁻¹ * fderiv ℝ rho x (B j) -
          ∑ i, lambda i * fderiv ℝ (H i) x (B j)) * tau j) =
        (rho x)⁻¹ * (∑ j, fderiv ℝ rho x (B j) * tau j) -
          ∑ i, lambda i *
            (∑ j, fderiv ℝ (H i) x (B j) * tau j) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _hj
      ring
    · calc
        ∑ j, (∑ i, lambda i * fderiv ℝ (H i) x (B j)) * tau j =
            ∑ j, ∑ i,
              (lambda i * fderiv ℝ (H i) x (B j)) * tau j := by
                apply Finset.sum_congr rfl
                intro j _hj
                rw [Finset.sum_mul]
        _ = ∑ i, ∑ j,
              (lambda i * fderiv ℝ (H i) x (B j)) * tau j :=
                Finset.sum_comm
        _ = ∑ i, lambda i *
              (∑ j, fderiv ℝ (H i) x (B j) * tau j) := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                ring
  rw [criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
    H (fun _ ↦ 0) rho basis x]
  change fderiv ℝ rho x tau = _
  have hsum' := hsum
  rw [hrhoExpand] at hsum'
  simp_rw [hHExpand] at hsum'
  simp only [euclideanLogLagrangeStationarityCoordinates,
    euclideanFDerivCoordinates, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, tau]
  rw [show (∑ j, ((rho x)⁻¹ * fderiv ℝ rho x (Pi.single j 1) -
      ∑ i, lambda i * fderiv ℝ (H i) x (Pi.single j 1)) *
        criticalCofactorTangent H (fun _ ↦ 0) basis x j) =
      (rho x)⁻¹ * fderiv ℝ rho x
          (criticalCofactorTangent H (fun _ ↦ 0) basis x) -
        ∑ i, lambda i * 0 by
    simpa only [B, tau, Pi.basisFun_apply] using hsum']
  simp only [mul_zero, Finset.sum_const_zero, sub_zero]
  field_simp

/-- The cofactor tangent varies `C¹` when its constraint functions are `C²`,
for an arbitrary fixed tuple of directions. -/
theorem contDiffAt_criticalCofactorTangent_directions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} (H : Fin r → E → ℝ)
    (directions : Fin (r + 1) → E) (x : E)
    (hH : ∀ i, ContDiffAt ℝ 2 (H i) x) :
    ContDiffAt ℝ 1
      (fun y ↦ criticalCofactorTangent H (fun _ ↦ 0) directions y) x := by
  unfold criticalCofactorTangent
  apply ContDiffAt.sum
  intro j _hj
  apply (contDiffAt_lastRowCofactor
    (fun y ↦ criticalJacobianMatrix H (fun _ ↦ 0) directions y) x ?_ j).smul
      contDiffAt_const
  intro i k
  refine Fin.lastCases ?_ (fun a ↦ ?_) i
  · simp only [criticalJacobianMatrix, functionTupleSnoc_last]
    fun_prop
  · simp only [criticalJacobianMatrix, functionTupleSnoc_castSucc]
    exact ((hH a).fderiv_right (le_refl 2)).clm_apply contDiffAt_const

/-- At a logarithmic Lagrange point, the derivative of any critical
determinant is the objective value times the derivative of the stationarity
covector paired with the corresponding cofactor tangent. -/
theorem fderiv_criticalDeterminant_eq_stationarityDerivative_pairing
    {n r : ℕ} (H : Fin r → RealEuclideanFunction n)
    (rho : RealEuclideanFunction n) (lambda : RealEuclidean r)
    (basis : Fin (r + 1) → RealEuclidean n) (x v : RealEuclidean n)
    (hH : ∀ i, ContDiffAt ℝ 2 (H i) x)
    (hrho : ContDiffAt ℝ 2 rho x)
    (hrho0 : rho x ≠ 0)
    (hstationary :
      euclideanLogLagrangeStationarityCoordinates H rho lambda x = 0) :
    fderiv ℝ (criticalDeterminant H rho basis) x v =
      rho x * ∑ j,
        fderiv ℝ (fun y ↦
          euclideanLogLagrangeStationarityCoordinates H rho lambda y j)
            x v *
          criticalCofactorTangent H (fun _ ↦ 0) basis x j := by
  let S : RealEuclidean n → RealEuclidean n :=
    euclideanLogLagrangeStationarityCoordinates H rho lambda
  let tau : RealEuclidean n → RealEuclidean n :=
    criticalCofactorTangent H (fun _ ↦ 0) basis
  have hS : ContDiffAt ℝ 1 S x := by
    rw [contDiffAt_pi]
    intro j
    have hrhoValue : ContDiffAt ℝ 1 rho x :=
      hrho.of_le (by norm_num)
    have hrhoDeriv : ContDiffAt ℝ 1
        (fun y ↦ fderiv ℝ rho y (Pi.single j 1)) x :=
      (hrho.fderiv_right (le_refl 2)).clm_apply contDiffAt_const
    have hHDeriv : ∀ i, ContDiffAt ℝ 1
        (fun y ↦ fderiv ℝ (H i) y (Pi.single j 1)) x := by
      intro i
      exact ((hH i).fderiv_right (le_refl 2)).clm_apply contDiffAt_const
    have hcoord : ContDiffAt ℝ 1
      (fun y ↦ (rho y)⁻¹ * fderiv ℝ rho y (Pi.single j 1) -
        ∑ i, lambda i * fderiv ℝ (H i) y (Pi.single j 1)) x := by
      apply ((hrhoValue.inv hrho0).mul hrhoDeriv).sub
      apply ContDiffAt.sum
      intro i _hi
      exact contDiffAt_const.mul (hHDeriv i)
    simpa only [S, euclideanLogLagrangeStationarityCoordinates,
      euclideanFDerivCoordinates, Pi.sub_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul] using hcoord
  have htau : ContDiffAt ℝ 1 tau x := by
    exact contDiffAt_criticalCofactorTangent_directions H basis x hH
  have heq : criticalDeterminant H rho basis =ᶠ[𝓝 x]
      (fun y ↦ rho y * ∑ j, S y j * tau y j) := by
    filter_upwards [hrho.continuousAt.eventually_ne hrho0] with y hy
    exact criticalDeterminant_eq_scalar_mul_euclideanPairing_logLagrange
      H rho lambda basis y hy
  calc
    fderiv ℝ (criticalDeterminant H rho basis) x v =
        fderiv ℝ (fun y ↦ rho y * ∑ j, S y j * tau y j) x v := by
          rw [heq.fderiv_eq]
    _ = rho x * ∑ j, fderiv ℝ (fun y ↦ S y j) x v * tau x j :=
      fderiv_scalar_mul_euclideanPairing_of_left_zero
        rho S tau x v (hrho.differentiableAt (by norm_num))
          (hS.differentiableAt (by norm_num))
          (htau.differentiableAt (by norm_num)) (by
            simpa only [S] using hstationary)
    _ = _ := rfl

/-- A maximal coordinate minor of an appended tuple is the corresponding
critical determinant evaluated on the selected standard coordinate
directions. -/
theorem standardJacobianColumnMinor_functionTupleSnoc_eq_criticalDeterminant
    {n r : ℕ} (H : Fin r → RealEuclideanFunction n)
    (rho : RealEuclideanFunction n) (cols : Fin (r + 1) ↪ Fin n) :
    standardJacobianColumnMinor (fun x i ↦ functionTupleSnoc H rho i x) cols =
      criticalDeterminant H rho (fun j ↦ Pi.single (cols j) 1) := by
  funext x
  unfold standardJacobianColumnMinor criticalDeterminant
  apply congrArg Matrix.det
  funext i j
  simp [standardRectangularJacobian, Pi.basisFun_apply]

/-- Linearization of a family affine in its multiplier variable.  At the
base multiplier the terms involving derivatives of the moving covectors
vanish, leaving only their values at the base point. -/
theorem hasFDerivAt_affineMultiplierFamily
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r : ℕ} (T : X → Y) (V : Fin r → X → Y)
    (x : X) (lambda : RealEuclidean r)
    (hT : DifferentiableAt ℝ T x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) :
    HasFDerivAt
      (fun z : X × RealEuclidean r ↦
        T z.1 - ∑ i, (z.2 i - lambda i) • V i z.1)
      (((fderiv ℝ T x).comp
          (ContinuousLinearMap.fst ℝ X (RealEuclidean r))) -
        ∑ i, (((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ X (RealEuclidean r))).smulRight
            (V i x)))
      (x, lambda) := by
  have hbase : HasFDerivAt (fun z : X × RealEuclidean r ↦ T z.1)
      ((fderiv ℝ T x).comp
        (ContinuousLinearMap.fst ℝ X (RealEuclidean r))) (x, lambda) :=
    hT.hasFDerivAt.comp (x, lambda) hasFDerivAt_fst
  have hterm : ∀ i, HasFDerivAt
      (fun z : X × RealEuclidean r ↦
        (z.2 i - lambda i) • V i z.1)
      (((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ X (RealEuclidean r))).smulRight
          (V i x))
      (x, lambda) := by
    intro i
    have hsnd : HasFDerivAt
        (Prod.snd : X × RealEuclidean r → RealEuclidean r)
        (ContinuousLinearMap.snd ℝ X (RealEuclidean r)) (x, lambda) :=
      hasFDerivAt_snd
    have hcoord : HasFDerivAt
        (fun z : X × RealEuclidean r ↦ z.2 i)
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ X (RealEuclidean r)))
        (x, lambda) := by
      convert (ContinuousLinearMap.proj i).hasFDerivAt.comp
        (x, lambda) hsnd using 1 <;> rfl
    have hscalar : HasFDerivAt
        (fun z : X × RealEuclidean r ↦ z.2 i - lambda i)
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ X (RealEuclidean r)))
        (x, lambda) :=
      hcoord.sub_const (lambda i)
    have hvector : HasFDerivAt
        (fun z : X × RealEuclidean r ↦ V i z.1)
        ((fderiv ℝ (V i) x).comp
          (ContinuousLinearMap.fst ℝ X (RealEuclidean r)))
        (x, lambda) :=
      (hV i).hasFDerivAt.comp (x, lambda) hasFDerivAt_fst
    convert hscalar.smul hvector using 1 <;> try rfl
    simp only [sub_self, zero_smul, zero_add]
  exact hbase.sub (HasFDerivAt.fun_sum fun i _hi ↦ hterm i)

theorem fderiv_affineMultiplierFamily_apply
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r : ℕ} (T : X → Y) (V : Fin r → X → Y)
    (x v : X) (lambda mu : RealEuclidean r)
    (hT : DifferentiableAt ℝ T x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) :
    fderiv ℝ
      (fun z : X × RealEuclidean r ↦
        T z.1 - ∑ i, (z.2 i - lambda i) • V i z.1)
      (x, lambda) (v, mu) =
        fderiv ℝ T x v - ∑ i, mu i • V i x := by
  rw [(hasFDerivAt_affineMultiplierFamily
    T V x lambda hT hV).fderiv]
  simp

/-- If the derivative of a constraint tuple is onto and an objective
covector vanishes on its tangent kernel, then the objective covector is a
linear combination of the constraint covectors. -/
theorem exists_lagrangeMultiplier_of_vanishesOn_constraintKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} (H : Fin r → E → ℝ) (x : E)
    (phi : E →L[ℝ] ℝ)
    (hsurj : Function.Surjective (constraintFDeriv H x))
    (hker : ∀ v, constraintFDeriv H x v = 0 → phi v = 0) :
    ∃ lambda : RealEuclidean r,
      phi = ∑ i, lambda i • fderiv ℝ (H i) x := by
  let A := constraintFDeriv H x
  obtain ⟨Rlin, hRlin⟩ :=
    A.toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj)
  let R : RealEuclidean r →L[ℝ] E :=
    ⟨Rlin, Rlin.continuous_of_finiteDimensional⟩
  let B : Module.Basis (Fin r) ℝ (RealEuclidean r) :=
    Pi.basisFun ℝ (Fin r)
  let lambda : RealEuclidean r := fun i ↦ phi (R (B i))
  refine ⟨lambda, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  have hright_apply : A (R (A v)) = A v := by
    exact congr($hRlin (A v))
  have hdiffKer : A (v - R (A v)) = 0 := by
    rw [map_sub, hright_apply, sub_self]
  have hphiDiff : phi (v - R (A v)) = 0 :=
    hker (v - R (A v)) hdiffKer
  have hphi : phi v = phi (R (A v)) := by
    rw [map_sub] at hphiDiff
    exact sub_eq_zero.mp hphiDiff
  have hrepr : (∑ i, (A v i) • B i) = A v := by
    simpa only [B, Pi.basisFun_repr] using B.sum_repr (A v)
  rw [hphi, ← hrepr, map_sum, map_sum]
  simp only [sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.pi_apply, map_smul, smul_eq_mul,
    lambda, A, B, constraintFDeriv]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A nonzero objective derivative along the tangent kernel completes a
surjective constraint derivative to a surjective appended derivative. -/
theorem fderiv_functionTupleSnoc_surjective_of_tangentDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} (H : Fin r → E → ℝ) (rho : E → ℝ) (x : E)
    (hH : ∀ i, DifferentiableAt ℝ (H i) x)
    (hrho : DifferentiableAt ℝ rho x)
    (hsurj : Function.Surjective (constraintFDeriv H x))
    {v : E} (hv : constraintFDeriv H x v = 0)
    (hrhov : fderiv ℝ rho x v ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun y i ↦ functionTupleSnoc H rho i y) x) := by
  have htuple : DifferentiableAt ℝ
      (fun y i ↦ functionTupleSnoc H rho i y) x := by
    rw [differentiableAt_pi]
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hrho
    · simpa using hH j
  have hcoord : ∀ i : Fin (r + 1), DifferentiableAt ℝ
      (fun y ↦ functionTupleSnoc H rho i y) x :=
    differentiableAt_pi.mp htuple
  have htupleDeriv :
      fderiv ℝ (fun y i ↦ functionTupleSnoc H rho i y) x =
        ContinuousLinearMap.pi (fun i ↦
          fderiv ℝ (fun y ↦ functionTupleSnoc H rho i y) x) :=
    fderiv_pi hcoord
  intro target
  let head : RealEuclidean r := fun i ↦ target i.castSucc
  obtain ⟨u, hu⟩ := hsurj head
  let c : ℝ :=
    (target (Fin.last r) - fderiv ℝ rho x u) /
      fderiv ℝ rho x v
  refine ⟨u + c • v, ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [htupleDeriv]
    simp only [ContinuousLinearMap.pi_apply, functionTupleSnoc_last,
      map_add, map_smul, smul_eq_mul, c]
    field_simp [hrhov]
    ring
  · rw [htupleDeriv]
    simp only [ContinuousLinearMap.pi_apply, functionTupleSnoc_castSucc,
      map_add, map_smul, smul_eq_mul]
    have huj := congrFun hu j
    have hvj := congrFun hv j
    simp only [constraintFDeriv, ContinuousLinearMap.pi_apply,
      Pi.zero_apply] at huj hvj
    rw [huj, hvj, mul_zero, add_zero]

/-- The linearized Lagrange system controls the common kernel of all
critical-minor derivatives.  This is the determinantal elimination step in
Lion's Lemma 4: a primal direction annihilated by the old equations and by
every critical coefficient has a multiplier lift into the kernel of the
fixed-parameter Lagrange derivative. -/
theorem finrank_commonCriticalDeterminantKernel_le_of_regularLagrangeLinearization
    {n q p : ℕ}
    (H : Fin (q + p) → RealEuclideanFunction n)
    (x : RealEuclidean n) (rhoValue : ℝ)
    (A : RealEuclidean n →L[ℝ] RealEuclidean q)
    (P : RealEuclidean n →L[ℝ] RealEuclidean n)
    (B : (Fin ((q + p) + 1) ↪ Fin n) →
      RealEuclidean n →L[ℝ] ℝ)
    (D : (RealEuclidean n × RealEuclidean (q + p)) →L[ℝ]
      (RealEuclidean n × RealEuclidean q))
    (hHdiff : ∀ i, DifferentiableAt ℝ (H i) x)
    (hHsurj : Function.Surjective (constraintFDeriv H x))
    (hDsurj : Function.Surjective D)
    (hrho : rhoValue ≠ 0)
    (hD : ∀ v mu, D (v, mu) =
      (P v - ∑ i, mu i • euclideanFDerivCoordinates (H i) x, A v))
    (hB : ∀ cols v, B cols v =
      rhoValue * ∑ j, P v j *
        criticalCofactorTangent H (fun _ ↦ 0)
          (fun k ↦ Pi.single (cols k) 1) x j) :
    Module.finrank ℝ
      (A.prod (ContinuousLinearMap.pi B)).ker ≤ p := by
  let C : RealEuclidean n →L[ℝ]
      (RealEuclidean q ×
        ((Fin ((q + p) + 1) ↪ Fin n) → ℝ)) :=
    A.prod (ContinuousLinearMap.pi B)
  have hvertical : ∀ mu, D (0, mu) = 0 → mu = 0 := by
    intro mu hmu
    have hblocks := hD 0 mu
    rw [hmu] at hblocks
    have hcoords :
        (∑ i, mu i • euclideanFDerivCoordinates (H i) x) = 0 := by
      have hfirst := congrArg Prod.fst hblocks
      have hneg :
          -(∑ i, mu i • euclideanFDerivCoordinates (H i) x) = 0 := by
        simpa only [map_zero, zero_apply, Pi.zero_apply, zero_smul,
          zero_sub, Prod.fst_zero] using hfirst.symm
      exact neg_eq_zero.mp hneg
    have hcov : (∑ i, mu i • fderiv ℝ (H i) x) = 0 := by
      apply ContinuousLinearMap.coe_injective
      apply (Pi.basisFun ℝ (Fin n)).ext
      intro j
      have hj := congrFun hcoords j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        euclideanFDerivCoordinates, Pi.basisFun_apply,
        smul_eq_mul] at hj
      simpa [Pi.basisFun_apply] using hj
    funext i
    exact (Fintype.linearIndependent_iff.mp
        (linearIndependent_constraintFDeriv_components_of_surjective
          H x (LinearMap.range_eq_top.mpr hHsurj))) mu hcov i
  have hlift : ∀ v ∈ C.ker, ∃ mu, D (v, mu) = 0 := by
    intro v hv
    have hCv : C v = 0 := hv
    have hAv : A v = 0 := by
      exact congrArg Prod.fst hCv
    have hBv : ∀ cols, B cols v = 0 := by
      intro cols
      exact congrFun (congrArg Prod.snd hCv) cols
    let phi : RealEuclidean n →L[ℝ] ℝ :=
      ∑ j, (P v j) • (ContinuousLinearMap.proj j)
    have hphi_apply : ∀ w, phi w = ∑ j, P v j * w j := by
      intro w
      simp only [phi, sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hphiKer : ∀ w, constraintFDeriv H x w = 0 → phi w = 0 := by
      intro w hw
      by_contra hphiw
      let sigma : RealEuclideanFunction n := fun y ↦ phi y
      have hsigmaDiff : DifferentiableAt ℝ sigma x :=
        phi.differentiableAt
      have hsigmaDeriv : fderiv ℝ sigma x = phi :=
        phi.hasFDerivAt.fderiv
      have happended : Function.Surjective
          (fderiv ℝ (fun y i ↦ functionTupleSnoc H sigma i y) x) :=
        fderiv_functionTupleSnoc_surjective_of_tangentDirection
          H sigma x hHdiff hsigmaDiff hHsurj hw (by
            simpa only [hsigmaDeriv] using hphiw)
      have htupleDiff : DifferentiableAt ℝ
          (fun y i ↦ functionTupleSnoc H sigma i y) x := by
        rw [differentiableAt_pi]
        intro i
        refine Fin.lastCases ?_ (fun k ↦ ?_) i
        · simpa using hsigmaDiff
        · simpa using hHdiff k
      obtain ⟨cols, hminor⟩ :=
        (fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
          htupleDiff).mp happended
      have hdet : criticalDeterminant H sigma
          (fun k ↦ Pi.single (cols k) 1) x ≠ 0 := by
        simpa only [
          standardJacobianColumnMinor_functionTupleSnoc_eq_criticalDeterminant]
          using hminor
      have hphiTau : phi (criticalCofactorTangent H (fun _ ↦ 0)
          (fun k ↦ Pi.single (cols k) 1) x) ≠ 0 := by
        simpa only [
          criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
            H (fun _ ↦ 0) sigma (fun k ↦ Pi.single (cols k) 1) x,
          hsigmaDeriv] using hdet
      have hBnonzero : B cols v ≠ 0 := by
        rw [hB cols v]
        have hsumne : (∑ j, P v j *
            criticalCofactorTangent H (fun _ ↦ 0)
              (fun k ↦ Pi.single (cols k) 1) x j) ≠ 0 := by
          simpa only [hphi_apply] using hphiTau
        exact mul_ne_zero hrho hsumne
      exact hBnonzero (hBv cols)
    obtain ⟨mu, hmu⟩ :=
      exists_lagrangeMultiplier_of_vanishesOn_constraintKernel
        H x phi hHsurj hphiKer
    have hcoords :
        P v = ∑ i, mu i • euclideanFDerivCoordinates (H i) x := by
      funext j
      have hj := congrArg
        (fun L : RealEuclidean n →L[ℝ] ℝ ↦ L (Pi.single j 1)) hmu
      simp only [hphi_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sum_apply,
        ContinuousLinearMap.smul_apply, euclideanFDerivCoordinates,
        Pi.smul_apply, smul_eq_mul] at hj ⊢
      simpa [euclideanFDerivCoordinates] using hj
    refine ⟨mu, ?_⟩
    rw [hD, hcoords, sub_self, hAv]
    rfl
  have hkernelBound : Module.finrank ℝ C.ker ≤ Module.finrank ℝ D.ker :=
    finrank_le_finrank_ker_of_primal_lifts D C.ker hvertical hlift
  have hDkernel : Module.finrank ℝ D.ker = p := by
    have hrankNullity := D.toLinearMap.finrank_range_add_finrank_ker
    have hDrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hDsurj
    rw [hDrange, finrank_top, Module.finrank_prod,
      Module.finrank_pi, Fintype.card_fin, Module.finrank_pi,
      Fintype.card_fin, Module.finrank_prod, Module.finrank_pi,
      Fintype.card_fin, Module.finrank_pi, Fintype.card_fin] at hrankNullity
    omega
  simpa only [C, hDkernel] using hkernelBound



theorem euclideanFDerivCoordinates_log_div {n : ℕ}
    (f d : RealEuclideanFunction n) (x : RealEuclidean n)
    (hf : DifferentiableAt ℝ f x) (hd : DifferentiableAt ℝ d x)
    (hfx : f x ≠ 0) (hdx : d x ≠ 0) :
    euclideanFDerivCoordinates (fun y ↦ Real.log (f y / d y)) x =
      (f x)⁻¹ • euclideanFDerivCoordinates f x -
        (d x)⁻¹ • euclideanFDerivCoordinates d x := by
  have hinv : HasFDerivAt (fun y ↦ (d y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(d x ^ 2)⁻¹)).comp
        (fderiv ℝ d x)) x :=
    (hasFDerivAt_inv hdx).comp x hd.hasFDerivAt
  have hquot := hf.hasFDerivAt.mul hinv
  have hlog := hquot.log (div_ne_zero hfx hdx)
  have hfun : (fun y ↦ Real.log (f y / d y)) =
      fun y ↦ Real.log (f y * (d y)⁻¹) := by
    funext y
    rw [div_eq_mul_inv]
  rw [hfun]
  funext j
  change fderiv ℝ (fun y ↦ Real.log ((f * fun z ↦ (d z)⁻¹) y)) x
      (Pi.single j 1) =
    (f x)⁻¹ * fderiv ℝ f x (Pi.single j 1) -
      (d x)⁻¹ * fderiv ℝ d x (Pi.single j 1)
  rw [hlog.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Pi.mul_apply, smul_eq_mul]
  field_simp [hfx, hdx]
  ring

theorem euclideanFDerivCoordinates_lionDenominator {n : ℕ}
    (x center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    (lionLiftedSquaredDistanceDenominator center height x)⁻¹ •
        euclideanFDerivCoordinates
          (lionLiftedSquaredDistanceDenominator center height) x =
      lionRadialLogDenominatorGradient x (center, height) := by
  funext j
  simp only [euclideanFDerivCoordinates, Pi.smul_apply, smul_eq_mul,
    lionRadialLogDenominatorGradient]
  rw [show fderiv ℝ (lionLiftedSquaredDistanceDenominator center height) x
      (Pi.single j 1) = 2 * (x j - center j) by
    have hdist :=
      hasFDerivAt_algebraicSquaredDistance_basis
        (Pi.basisFun ℝ (Fin n)) center x
    have hstdDiff : DifferentiableAt ℝ
        (standardSquaredDistance center) x := by
      simpa [standardSquaredDistance] using hdist.differentiableAt
    unfold lionLiftedSquaredDistanceDenominator
    rw [fderiv_fun_add hstdDiff
      (differentiableAt_const (x := x) (𝕜 := ℝ) (height ^ 2))]
    simp [fderiv_standardSquaredDistance_apply_single]]
  rw [inv_mul_eq_div]

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- The parameter-independent numerator of Lion's critical carpet. -/
def criticalCarpetNumerator
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) : RealEuclideanFunction n :=
  L.regularCarpet g

theorem criticalCarpet_eq_numerator_div
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) :
    L.criticalCarpet g center height = fun x ↦
      L.criticalCarpetNumerator g x /
        lionLiftedSquaredDistanceDenominator center height x := by
  funext x
  simp only [criticalCarpet, lionRadialCarpet, criticalCarpetNumerator,
    regularCarpet, regularityCarpetFactor]
  ring

theorem criticalCarpetNumerator_pos
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    {x : RealEuclidean n} (hx : x ∈ L.regularLocus g) :
    0 < L.criticalCarpetNumerator g x :=
  L.regularCarpet_pos_of_mem_regularLocus hsmooth g hg hx

/-- The logarithmic gradient of Lion's critical carpet. -/
def criticalCarpetLogGradient
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ)
    (x : RealEuclidean n) : RealEuclidean n :=
  euclideanFDerivCoordinates
    (fun y ↦ Real.log (L.criticalCarpet g center height y)) x

/-- The parameter-independent part of the logarithmic critical-carpet
gradient. -/
def criticalCarpetBaseLogGradient
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) : RealEuclidean n :=
  (L.criticalCarpetNumerator g x)⁻¹ •
    euclideanFDerivCoordinates (L.criticalCarpetNumerator g) x

theorem criticalCarpetLogGradient_eq_base_sub_radial
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (x : RealEuclidean n) (hx : x ∈ L.regularLocus g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    L.criticalCarpetLogGradient g center height x =
      L.criticalCarpetBaseLogGradient g x -
        lionRadialLogDenominatorGradient x (center, height) := by
  have hnumDiff : DifferentiableAt ℝ (L.criticalCarpetNumerator g) x := by
    exact (hsmooth n (L.regularCarpet g)
      (L.regularCarpet_mem hG hderiv g hg)).differentiable (by norm_num) x
  have hdenDiff : DifferentiableAt ℝ
      (lionLiftedSquaredDistanceDenominator center height) x := by
    have hdist := hasFDerivAt_algebraicSquaredDistance_basis
      (Pi.basisFun ℝ (Fin n)) center x
    have hstdDiff : DifferentiableAt ℝ
        (standardSquaredDistance center) x := by
      simpa [standardSquaredDistance] using hdist.differentiableAt
    unfold lionLiftedSquaredDistanceDenominator
    exact hstdDiff.add
      (differentiableAt_const (x := x) (𝕜 := ℝ) (height ^ 2))
  have hnum0 : L.criticalCarpetNumerator g x ≠ 0 :=
    ne_of_gt (L.criticalCarpetNumerator_pos hsmooth g hg hx)
  have hden0 := lionLiftedSquaredDistanceDenominator_ne_zero center hheight x
  rw [criticalCarpetLogGradient, criticalCarpet_eq_numerator_div]
  rw [euclideanFDerivCoordinates_log_div
    (L.criticalCarpetNumerator g)
    (lionLiftedSquaredDistanceDenominator center height) x
    hnumDiff hdenDiff hnum0 hden0]
  rw [euclideanFDerivCoordinates_lionDenominator x center hheight]
  rfl

theorem hasFDerivAt_criticalCarpetLogGradient_parameter
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (x : RealEuclidean n) (hx : x ∈ L.regularLocus g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        L.criticalCarpetLogGradient g a.1 a.2 x)
      (-(lionRadialParameterVariation x center height))
      (center, height) := by
  have hposN : {a : RealEuclidean n × ℝ | 0 < a.2} ∈ 𝓝 (center, height) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hheight
  have heq : (fun a : RealEuclidean n × ℝ ↦
      L.criticalCarpetLogGradient g a.1 a.2 x) =ᶠ[𝓝 (center, height)]
      (fun a ↦ L.criticalCarpetBaseLogGradient g x -
        lionRadialLogDenominatorGradient x a) := by
    filter_upwards [hposN] with a ha
    exact L.criticalCarpetLogGradient_eq_base_sub_radial
      hG hsmooth hderiv g hg x hx a.1 ha
  have hbase : HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        L.criticalCarpetBaseLogGradient g x -
          lionRadialLogDenominatorGradient x a)
      (-(lionRadialParameterVariation x center height))
      (center, height) := by
    simpa using (hasFDerivAt_const
      (L.criticalCarpetBaseLogGradient g x) (center, height)).sub
        (hasFDerivAt_lionRadialLogDenominatorGradient_parameter
          x center hheight)
  exact hbase.congr_of_eventuallyEq heq

theorem fderiv_criticalCarpetLogGradient_parameter_surjective
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (x : RealEuclidean n) (hx : x ∈ L.regularLocus g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    Function.Surjective
      (fderiv ℝ
        (fun a : RealEuclidean n × ℝ ↦
          L.criticalCarpetLogGradient g a.1 a.2 x)
        (center, height)) := by
  rw [(L.hasFDerivAt_criticalCarpetLogGradient_parameter
    hG hsmooth hderiv g hg x hx center hheight).fderiv]
  intro y
  obtain ⟨w, hw⟩ :=
    lionRadialParameterVariation_surjective x center hheight (-y)
  refine ⟨w, ?_⟩
  simp only [ContinuousLinearMap.neg_apply, hw, neg_neg]

/-- Every point of Lion's critical trace has a Lagrange multiplier for the
logarithmic critical carpet.  The multiplier is unique because `(f,g)` is a
submersion on the trace. -/
theorem existsUnique_lagrangeMultiplier_criticalCarpetLog_of_mem_criticalTrace
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {x : RealEuclidean n} (hx : x ∈ L.criticalTrace g center height) :
    ∃! lambda : RealEuclidean (q + p),
      lagrangeStationarityCovector
        (fun i y ↦ L.definingTupleAppend g y i)
        (fun y ↦ Real.log (L.criticalCarpet g center height y))
        x lambda = 0 := by
  let H : Fin (q + p) → RealEuclideanFunction n :=
    fun i y ↦ L.definingTupleAppend g y i
  let rho : RealEuclideanFunction n :=
    L.criticalCarpet g center height
  have hxreg : x ∈ L.regularLocus g := hx.1.2
  have hrhoPos : 0 < rho x :=
    (L.criticalCarpet_isLionCarpetOn
      hG hsmooth hderiv center hheight g hg).pos x hxreg
  have hrho0 : rho x ≠ 0 := ne_of_gt hrhoPos
  have hrhoDiff : DifferentiableAt ℝ rho x :=
    (hsmooth n rho
      (L.criticalCarpet_mem hG hderiv center hheight g hg)).differentiable
        (by norm_num) x
  have hH : ∀ i, DifferentiableAt ℝ (H i) x := by
    intro i
    exact (hsmooth n (H i) (L.definingTupleAppend_mem g hg i)).differentiable
      (by norm_num) x
  have htupleDeriv :
      fderiv ℝ (L.definingTupleAppend g) x = constraintFDeriv H x := by
    change fderiv ℝ (fun y i ↦ H i y) x = constraintFDeriv H x
    simpa only [constraintFDeriv] using fderiv_pi hH
  have hsurj : Function.Surjective (constraintFDeriv H x) := by
    rw [← htupleDeriv]
    exact hxreg.2
  have hnonsurj : ¬ Function.Surjective
      (fderiv ℝ (L.criticalAugmentedTuple g center height) x) :=
    (L.mem_criticalLocus_iff_not_surjective
      hG hsmooth hderiv g hg center hheight x).mp hx.2
  have hrhoKer : ∀ v, constraintFDeriv H x v = 0 →
      fderiv ℝ rho x v = 0 := by
    intro v hv
    by_contra hne
    apply hnonsurj
    have happended :=
      fderiv_functionTupleSnoc_surjective_of_tangentDirection
        H rho x hH hrhoDiff hsurj hv hne
    change Function.Surjective
      (fderiv ℝ (fun y i ↦ functionTupleSnoc H rho i y) x)
    exact happended
  have hlogDeriv :
      fderiv ℝ (fun y ↦ Real.log (rho y)) x =
        (rho x)⁻¹ • fderiv ℝ rho x :=
    (hrhoDiff.hasFDerivAt.log hrho0).fderiv
  have hlogKer : ∀ v, constraintFDeriv H x v = 0 →
      fderiv ℝ (fun y ↦ Real.log (rho y)) x v = 0 := by
    intro v hv
    rw [hlogDeriv]
    simp [hrhoKer v hv]
  obtain ⟨lambda, hlambda⟩ :=
    exists_lagrangeMultiplier_of_vanishesOn_constraintKernel
      H x (fderiv ℝ (fun y ↦ Real.log (rho y)) x) hsurj hlogKer
  have hlambdaZero : lagrangeStationarityCovector
      H (fun y ↦ Real.log (rho y)) x lambda = 0 := by
    simp only [lagrangeStationarityCovector, hlambda, sub_self]
  refine ⟨lambda, by simpa only [H, rho] using hlambdaZero, ?_⟩
  · intro mu hmu
    have hmuZero : lagrangeStationarityCovector
        H (fun y ↦ Real.log (rho y)) x mu = 0 := by
      simpa only [H, rho] using hmu
    exact lagrangeStationarityCovector_eq_zero_unique_of_surjective
      H (fun y ↦ Real.log (rho y)) x (lambda := mu) (mu := lambda)
      (LinearMap.range_eq_top.mpr hsurj)
      hmuZero hlambdaZero

/-- The logarithmic Lagrange stationarity equations with Lion's radial
parameter exposed.  The parameter-independent logarithmic numerator is
used directly, so parameter differentiation is exactly the radial variation
computed in `LionRadialParameterTransversality`. -/
def criticalTraceLogStationarityFamily
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) :
    ((RealEuclidean n × RealEuclidean (q + p)) ×
      (RealEuclidean n × ℝ)) → RealEuclidean n :=
  fun z ↦
    L.criticalCarpetBaseLogGradient g z.1.1 -
      lionRadialLogDenominatorGradient z.1.1 z.2 -
        ∑ i, z.1.2 i • euclideanFDerivCoordinates
          (fun y ↦ L.definingTupleAppend g y i) z.1.1

/-- Add the original leaf equations to the logarithmic stationarity rows.
Its fixed-parameter source has dimension `n + q + p` and its target has
dimension `n + q`, hence expected fiber dimension `p`. -/
def criticalTraceLogLagrangeFamily
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) :
    ((RealEuclidean n × RealEuclidean (q + p)) ×
      (RealEuclidean n × ℝ)) →
        (RealEuclidean n × RealEuclidean q) :=
  fun z ↦
    (L.criticalTraceLogStationarityFamily g z, L.equations z.1.1)

/-- Vanishing of the covector Lagrange equation is equivalent to vanishing
of its standard coordinate vector. -/
theorem criticalTraceLogStationarityFamily_eq_zero_iff
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n) (hx : x ∈ L.regularLocus g)
    (lambda : RealEuclidean (q + p))
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hg : FunctionTupleInFamily G g) :
    L.criticalTraceLogStationarityFamily g ((x, lambda), (center, height)) = 0 ↔
      lagrangeStationarityCovector
        (fun i y ↦ L.definingTupleAppend g y i)
        (fun y ↦ Real.log (L.criticalCarpet g center height y))
        x lambda = 0 := by
  have hgradient := L.criticalCarpetLogGradient_eq_base_sub_radial
    hG hsmooth hderiv g hg x hx center hheight
  constructor
  · intro hzero
    apply ContinuousLinearMap.ext
    intro v
    let B : Module.Basis (Fin n) ℝ (RealEuclidean n) :=
      Pi.basisFun ℝ (Fin n)
    have hv : (∑ j, v j • B j) = v := by
      simpa only [B, Pi.basisFun_repr] using B.sum_repr v
    rw [← hv, map_sum]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [map_smul]
    have hj := congrFun hzero j
    simp only [criticalTraceLogStationarityFamily, Pi.zero_apply,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      euclideanFDerivCoordinates, smul_eq_mul] at hj
    have hgradient_j := congrFun hgradient j
    simp only [criticalCarpetLogGradient,
      euclideanFDerivCoordinates, Pi.sub_apply] at hgradient_j
    simp only [lagrangeStationarityCovector, sub_apply, sum_apply,
      smul_apply, smul_eq_mul, B, Pi.basisFun_apply]
    rw [hgradient_j]
    simpa [mul_comm] using congrArg (fun t : ℝ ↦ v j * t) hj
  · intro hcov
    funext j
    have hj := congrArg
      (fun phi : StrongDual ℝ (RealEuclidean n) ↦ phi (Pi.single j 1))
      hcov
    have hgradient_j :
        fderiv ℝ (fun y ↦ Real.log
          (L.criticalCarpet g center height y)) x (Pi.single j 1) =
          L.criticalCarpetBaseLogGradient g x j -
            lionRadialLogDenominatorGradient x (center, height) j := by
      simpa only [criticalCarpetLogGradient,
        euclideanFDerivCoordinates, Pi.sub_apply] using congrFun hgradient j
    simp only [lagrangeStationarityCovector, sub_apply, sum_apply,
      smul_apply, smul_eq_mul, zero_apply] at hj
    simp only [criticalTraceLogStationarityFamily, Pi.zero_apply,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      euclideanFDerivCoordinates, smul_eq_mul]
    rw [← hgradient_j]
    exact hj

/-- Every point of `S_a` lifts to a zero of the concrete logarithmic
Lagrange family. -/
theorem exists_lagrangeLift_mem_criticalTraceLogLagrangeFamily_zero
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {x : RealEuclidean n} (hx : x ∈ L.criticalTrace g center height) :
    ∃ lambda : RealEuclidean (q + p),
      L.criticalTraceLogLagrangeFamily g
        ((x, lambda), (center, height)) = 0 := by
  obtain ⟨lambda, hlambda, _hunique⟩ :=
    L.existsUnique_lagrangeMultiplier_criticalCarpetLog_of_mem_criticalTrace
      hG hsmooth hderiv g hg center hheight hx
  refine ⟨lambda, ?_⟩
  apply Prod.ext
  · exact (L.criticalTraceLogStationarityFamily_eq_zero_iff
      g center hheight x hx.1.2 lambda hG hsmooth hderiv hg).2 hlambda
  · exact hx.1.1.2

/-- At a fixed primal point and multiplier, the radial parameter derivative
of the stationarity family is the negative radial variation. -/
theorem hasFDerivAt_criticalTraceLogStationarityFamily_parameter
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) (lambda : RealEuclidean (q + p))
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        L.criticalTraceLogStationarityFamily g ((x, lambda), a))
      (-(lionRadialParameterVariation x center height))
      (center, height) := by
  let left : RealEuclidean n := L.criticalCarpetBaseLogGradient g x
  let right : RealEuclidean n :=
    ∑ i, lambda i • euclideanFDerivCoordinates
      (fun y ↦ L.definingTupleAppend g y i) x
  have h := ((hasFDerivAt_const left (center, height)).sub
    (hasFDerivAt_lionRadialLogDenominatorGradient_parameter
      x center hheight)).sub_const right
  change HasFDerivAt
    (fun a : RealEuclidean n × ℝ ↦
      left - lionRadialLogDenominatorGradient x a - right)
    (-(lionRadialParameterVariation x center height)) (center, height)
  exact h.congr_fderiv (zero_sub _)

/-- Thus the stationarity rows are jointly submersive in Lion's radial
parameter at every positive height. -/
theorem fderiv_criticalTraceLogStationarityFamily_parameter_surjective
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) (lambda : RealEuclidean (q + p))
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    Function.Surjective
      (fderiv ℝ
        (fun a : RealEuclidean n × ℝ ↦
          L.criticalTraceLogStationarityFamily g ((x, lambda), a))
        (center, height)) := by
  rw [(L.hasFDerivAt_criticalTraceLogStationarityFamily_parameter
    g x lambda center hheight).fderiv]
  intro y
  obtain ⟨w, hw⟩ :=
    lionRadialParameterVariation_surjective x center hheight (-y)
  refine ⟨w, ?_⟩
  simp only [ContinuousLinearMap.neg_apply, hw, neg_neg]

/-- Two derivatives of the family functions give one derivative of the
logarithmic Lagrange family at every positive-height point over the regular
locus. -/
theorem contDiffAt_criticalTraceLogLagrangeFamily
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (x : RealEuclidean n) (hx : x ∈ L.regularLocus g)
    (lambda : RealEuclidean (q + p))
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    ContDiffAt ℝ ∞ (L.criticalTraceLogLagrangeFamily g)
      ((x, lambda), (center, height)) := by
  let N : RealEuclideanFunction n := L.criticalCarpetNumerator g
  let H : Fin (q + p) → RealEuclideanFunction n :=
    fun i y ↦ L.definingTupleAppend g y i
  have hN : ContDiff ℝ ∞ N :=
    hsmooth n N (L.regularCarpet_mem hG hderiv g hg)
  have hH : ∀ i, ContDiff ℝ ∞ (H i) := by
    intro i
    exact hsmooth n (H i) (L.definingTupleAppend_mem g hg i)
  have hN0 : N x ≠ 0 :=
    ne_of_gt (L.criticalCarpetNumerator_pos hsmooth g hg hx)
  have hD0 : lionLiftedSquaredDistanceDenominator center height x ≠ 0 :=
    lionLiftedSquaredDistanceDenominator_ne_zero center hheight x
  have hprimal : ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦ z.1.1)
      ((x, lambda), (center, height)) := by
    fun_prop
  have hNvalue : ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦ N z.1.1)
      ((x, lambda), (center, height)) :=
    (hN.contDiffAt.comp _ hprimal)
  have hNinv : ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦ (N z.1.1)⁻¹)
      ((x, lambda), (center, height)) :=
    hNvalue.inv hN0
  have hNderiv : ∀ j : Fin n, ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦
        fderiv ℝ N z.1.1 (Pi.single j 1))
      ((x, lambda), (center, height)) := by
    intro j
    have hbase : ContDiff ℝ ∞
        (fun y : RealEuclidean n ↦
          fderiv ℝ N y (Pi.single j 1)) :=
      ((hN.fderiv_right (by norm_num)).clm_apply contDiff_const)
    exact hbase.contDiffAt.comp _ hprimal
  have hHderiv : ∀ i : Fin (q + p), ∀ j : Fin n, ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦
        fderiv ℝ (H i) z.1.1 (Pi.single j 1))
      ((x, lambda), (center, height)) := by
    intro i j
    have hbase : ContDiff ℝ ∞
        (fun y : RealEuclidean n ↦
          fderiv ℝ (H i) y (Pi.single j 1)) :=
      (((hH i).fderiv_right (by norm_num)).clm_apply contDiff_const)
    exact hbase.contDiffAt.comp _ hprimal
  have hdenominator : ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦
        lionLiftedSquaredDistanceDenominator z.2.1 z.2.2 z.1.1)
      ((x, lambda), (center, height)) := by
    rw [show (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
          (RealEuclidean n × ℝ) ↦
          lionLiftedSquaredDistanceDenominator z.2.1 z.2.2 z.1.1) =
        fun z ↦ (∑ i : Fin n, (z.1.1 i - z.2.1 i) ^ 2) + z.2.2 ^ 2 by
      funext z
      simp [lionLiftedSquaredDistanceDenominator, standardSquaredDistance]]
    apply (ContDiffAt.sum (fun i _hi ↦ ?_)).add
    · fun_prop
    · fun_prop
  have hradial : ∀ j : Fin n, ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦
        2 * (z.1.1 j - z.2.1 j) /
          lionLiftedSquaredDistanceDenominator z.2.1 z.2.2 z.1.1)
      ((x, lambda), (center, height)) := by
    intro j
    apply (contDiffAt_const.mul ?_).div hdenominator hD0
    fun_prop
  have hmultiplier : ∀ i : Fin (q + p), ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦ z.1.2 i)
      ((x, lambda), (center, height)) := by
    intro i
    fun_prop
  apply ContDiffAt.prodMk
  · rw [contDiffAt_pi]
    intro j
    have hcoord : ContDiffAt ℝ ∞
      (fun z : (RealEuclidean n × RealEuclidean (q + p)) ×
        (RealEuclidean n × ℝ) ↦
        (N z.1.1)⁻¹ * fderiv ℝ N z.1.1 (Pi.single j 1) -
          2 * (z.1.1 j - z.2.1 j) /
            lionLiftedSquaredDistanceDenominator z.2.1 z.2.2 z.1.1 -
          ∑ i, z.1.2 i *
            fderiv ℝ (H i) z.1.1 (Pi.single j 1))
      ((x, lambda), (center, height)) := by
      apply (hNinv.mul (hNderiv j)).sub (hradial j) |>.sub
      apply ContDiffAt.sum
      intro i _hi
      exact (hmultiplier i).mul (hHderiv i j)
    simpa only [criticalTraceLogStationarityFamily,
      criticalCarpetBaseLogGradient, criticalCarpetNumerator,
      euclideanFDerivCoordinates, lionRadialLogDenominatorGradient,
      Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, N, H]
      using hcoord
  · have hequations : ContDiff ℝ ∞ L.equations :=
      L.equations_contDiff hsmooth
    exact hequations.contDiffAt.comp _ hprimal

/-- Elementary block-submersion lemma.  Parameter directions control the
first output block, while fixed-source directions control the second block;
the uncontrolled first component of a fixed-source direction is then
cancelled by a parameter direction. -/
theorem fderiv_prod_family_surjective_of_slice_derivatives
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Phi : X × Y → U × V) (x : X) (y : Y)
    (S : Y →L[ℝ] U) (T : X →L[ℝ] V)
    (hPhi : DifferentiableAt ℝ Phi (x, y))
    (hy : HasFDerivAt (fun b ↦ Phi (x, b))
      (S.prod (0 : Y →L[ℝ] V)) y)
    (hx : HasFDerivAt (fun a ↦ (Phi (a, y)).2) T x)
    (hS : Function.Surjective S) (hT : Function.Surjective T) :
    Function.Surjective (fderiv ℝ Phi (x, y)) := by
  let D := fderiv ℝ Phi (x, y)
  let IX : X →L[ℝ] X × Y :=
    ContinuousLinearMap.inl ℝ X Y
  let IY : Y →L[ℝ] X × Y :=
    ContinuousLinearMap.inr ℝ X Y
  have hIX : HasFDerivAt (fun a : X ↦ (a, y)) IX x :=
    hasFDerivAt_prodMk_left x y
  have hIY : HasFDerivAt (fun b : Y ↦ (x, b)) IY y :=
    hasFDerivAt_prodMk_right x y
  have hparamFull : D.comp IY = S.prod (0 : Y →L[ℝ] V) := by
    apply HasFDerivAt.unique
      (by simpa [D, Function.comp_def] using
        hPhi.hasFDerivAt.comp y hIY)
      hy
  have hfixedSecond :
      (ContinuousLinearMap.snd ℝ U V).comp (D.comp IX) = T := by
    have hfixedFull : HasFDerivAt (fun a ↦ Phi (a, y))
        (D.comp IX) x := by
      simpa [D, Function.comp_def] using hPhi.hasFDerivAt.comp x hIX
    have hsnd : HasFDerivAt (fun a ↦ (Phi (a, y)).2)
        ((ContinuousLinearMap.snd ℝ U V).comp (D.comp IX)) x := by
      exact (ContinuousLinearMap.snd ℝ U V).hasFDerivAt.comp x hfixedFull
    exact hsnd.unique hx
  intro target
  obtain ⟨dx, hdx⟩ := hT target.2
  let w : U × V := D (dx, 0)
  have hwSecond : w.2 = target.2 := by
    have happ := congrArg
      (fun A : X →L[ℝ] V ↦ A dx) hfixedSecond
    simpa [w, D, IX, ContinuousLinearMap.comp_apply] using happ.trans hdx
  obtain ⟨dy, hdy⟩ := hS (target.1 - w.1)
  have hparamApply : D (0, dy) = (target.1 - w.1, 0) := by
    have happ := congrArg
      (fun A : Y →L[ℝ] U × V ↦ A dy) hparamFull
    simpa [IY, ContinuousLinearMap.comp_apply, hdy] using happ
  refine ⟨(dx, dy), ?_⟩
  rw [show (dx, dy) = (dx, 0) + (0, dy) by ext <;> simp, map_add,
    hparamApply]
  change w + (target.1 - w.1, 0) = target
  apply Prod.ext
  · change w.1 + (target.1 - w.1) = target.1
    abel
  · change w.2 + 0 = target.2
    simpa only [add_zero] using hwSecond

/-- The full logarithmic Lagrange family is a joint submersion at every
positive-height point over the regular locus, once its routine local
differentiability is supplied.  The proof uses only the radial parameter
submersion and the original leaf-equation submersion. -/
theorem criticalTraceLogLagrangeFamily_fderiv_surjective
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) (hxU : x ∈ L.U)
    (lambda : RealEuclidean (q + p))
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hequations : DifferentiableAt ℝ L.equations x)
    (hfamily : DifferentiableAt ℝ
      (L.criticalTraceLogLagrangeFamily g)
      ((x, lambda), (center, height))) :
    Function.Surjective
      (fderiv ℝ (L.criticalTraceLogLagrangeFamily g)
        ((x, lambda), (center, height))) := by
  let S : (RealEuclidean n × ℝ) →L[ℝ] RealEuclidean n :=
    -(lionRadialParameterVariation x center height)
  let T : (RealEuclidean n × RealEuclidean (q + p)) →L[ℝ]
      RealEuclidean q :=
    (fderiv ℝ L.equations x).comp
      (ContinuousLinearMap.fst ℝ (RealEuclidean n)
        (RealEuclidean (q + p)))
  have hparamStationarity :=
    L.hasFDerivAt_criticalTraceLogStationarityFamily_parameter
      g x lambda center hheight
  have hparam : HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        L.criticalTraceLogLagrangeFamily g ((x, lambda), a))
      (S.prod (0 : (RealEuclidean n × ℝ) →L[ℝ] RealEuclidean q))
      (center, height) := by
    exact hparamStationarity.prodMk
      (hasFDerivAt_const (L.equations x) (center, height))
  have hfixedSecond :=
    hequations.hasFDerivAt.comp (x, lambda)
      (hasFDerivAt_fst (𝕜 := ℝ)
        (E := RealEuclidean n) (F := RealEuclidean (q + p))
        (p := (x, lambda)))
  have hS : Function.Surjective S := by
    intro y
    obtain ⟨w, hw⟩ :=
      lionRadialParameterVariation_surjective x center hheight (-y)
    refine ⟨w, ?_⟩
    simp only [S, ContinuousLinearMap.neg_apply, hw, neg_neg]
  have hT : Function.Surjective T := by
    intro y
    obtain ⟨dx, hdx⟩ := L.fderiv_surjective x hxU y
    refine ⟨(dx, 0), ?_⟩
    simpa [T, ContinuousLinearMap.comp_apply] using hdx
  exact fderiv_prod_family_surjective_of_slice_derivatives
    (L.criticalTraceLogLagrangeFamily g) (x, lambda) (center, height)
      S T hfamily hparam (by
        simpa only [criticalTraceLogLagrangeFamily, Function.comp_def, T]
          using hfixedSecond) hS hT

/-- Under the standing smooth-family hypotheses, the concrete logarithmic
Lagrange family is a joint submersion at every positive-height point over
Lion's regular locus. -/
theorem criticalTraceLogLagrangeFamily_fderiv_surjective_of_mem_regularLocus
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (x : RealEuclidean n) (hx : x ∈ L.regularLocus g)
    (lambda : RealEuclidean (q + p))
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    Function.Surjective
      (fderiv ℝ (L.criticalTraceLogLagrangeFamily g)
        ((x, lambda), (center, height))) := by
  apply L.criticalTraceLogLagrangeFamily_fderiv_surjective
      g x hx.1 lambda center hheight
  · exact (L.equations_contDiff hsmooth).differentiable
      (by norm_num) x
  · exact (L.contDiffAt_criticalTraceLogLagrangeFamily
      hG hsmooth hderiv g hg x hx lambda center hheight).differentiableAt
        (by norm_num)

/-- Every point of `S_a` has a unique logarithmic Lagrange lift, and the
joint source/parameter system is a submersion at that lift.  This is the
incidence-manifold input for the rectangular parametric Sard step in Lion's
Lemma 4. -/
theorem exists_lagrangeLift_mem_criticalTraceLogLagrangeFamily_zero_and_surjective
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {x : RealEuclidean n} (hx : x ∈ L.criticalTrace g center height) :
    ∃ lambda : RealEuclidean (q + p),
      L.criticalTraceLogLagrangeFamily g
          ((x, lambda), (center, height)) = 0 ∧
        Function.Surjective
          (fderiv ℝ (L.criticalTraceLogLagrangeFamily g)
            ((x, lambda), (center, height))) := by
  obtain ⟨lambda, hzero⟩ :=
    L.exists_lagrangeLift_mem_criticalTraceLogLagrangeFamily_zero
      hG hsmooth hderiv g hg center hheight hx
  refine ⟨lambda, hzero, ?_⟩
  exact L.criticalTraceLogLagrangeFamily_fderiv_surjective_of_mem_regularLocus
    hG hsmooth hderiv g hg x hx.1.2 lambda center hheight

/-- Lion's critical coefficient is the generic critical determinant for the
constraint tuple `(f,g)` and the critical carpet, evaluated on the selected
standard coordinate directions. -/
theorem criticalCoefficient_eq_criticalDeterminant
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ)
    (cols : Fin ((q + p) + 1) ↪ Fin n) :
    L.criticalCoefficient g center height cols =
      criticalDeterminant
        (fun i y ↦ L.definingTupleAppend g y i)
        (L.criticalCarpet g center height)
        (fun j ↦ Pi.single (cols j) 1) := by
  unfold criticalCoefficient criticalAugmentedTuple
  exact
    (standardJacobianColumnMinor_functionTupleSnoc_eq_criticalDeterminant
      (fun i y ↦ L.definingTupleAppend g y i)
      (L.criticalCarpet g center height) cols)

/-- On Lion's regular locus, the exposed radial stationarity vector is
exactly the standard-coordinate logarithmic Lagrange covector. -/
theorem euclideanLogLagrangeStationarityCoordinates_eq_criticalTraceLogStationarityFamily
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (lambda : RealEuclidean (q + p))
    {x : RealEuclidean n} (hx : x ∈ L.regularLocus g) :
    euclideanLogLagrangeStationarityCoordinates
        (fun i y ↦ L.definingTupleAppend g y i)
        (L.criticalCarpet g center height) lambda x =
      L.criticalTraceLogStationarityFamily g
        ((x, lambda), (center, height)) := by
  let rho : RealEuclideanFunction n := L.criticalCarpet g center height
  have hrhoDiff : DifferentiableAt ℝ rho x :=
    (hsmooth n rho
      (L.criticalCarpet_mem hG hderiv center hheight g hg)).differentiable
        (by norm_num) x
  have hrho0 : rho x ≠ 0 := ne_of_gt
    ((L.criticalCarpet_isLionCarpetOn
      hG hsmooth hderiv center hheight g hg).pos x hx)
  have hlogDeriv :
      fderiv ℝ (fun y ↦ Real.log (rho y)) x =
        (rho x)⁻¹ • fderiv ℝ rho x :=
    (hrhoDiff.hasFDerivAt.log hrho0).fderiv
  have hlogCoordinates :
      L.criticalCarpetLogGradient g center height x =
        (rho x)⁻¹ • euclideanFDerivCoordinates rho x := by
    funext j
    simp only [criticalCarpetLogGradient, euclideanFDerivCoordinates,
      Pi.smul_apply, smul_eq_mul, rho]
    rw [hlogDeriv]
    rfl
  have hgradient := L.criticalCarpetLogGradient_eq_base_sub_radial
    hG hsmooth hderiv g hg x hx center hheight
  rw [hlogCoordinates] at hgradient
  simp only [euclideanLogLagrangeStationarityCoordinates,
    criticalTraceLogStationarityFamily]
  rw [hgradient]

/-- The fixed-parameter logarithmic Lagrange derivative splits into the
primal derivative of the stationarity vector, the transpose constraint block
in the multiplier direction, and the old leaf-equation derivative. -/
theorem fderiv_criticalTraceLogLagrangeFamily_fixedParameter_apply
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (lambda : RealEuclidean (q + p))
    {x : RealEuclidean n} (hx : x ∈ L.regularLocus g)
    (v : RealEuclidean n) (mu : RealEuclidean (q + p)) :
    fderiv ℝ
        (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
          L.criticalTraceLogLagrangeFamily g
            (z, (center, height)))
        (x, lambda) (v, mu) =
      (fderiv ℝ
          (fun y ↦ L.criticalTraceLogStationarityFamily g
            ((y, lambda), (center, height))) x v -
          ∑ i, mu i • euclideanFDerivCoordinates
            (fun y ↦ L.definingTupleAppend g y i) x,
        fderiv ℝ L.equations x v) := by
  let H : Fin (q + p) → RealEuclideanFunction n :=
    fun i y ↦ L.definingTupleAppend g y i
  let T : RealEuclidean n → RealEuclidean n := fun y ↦
    L.criticalTraceLogStationarityFamily g
      ((y, lambda), (center, height))
  let V : Fin (q + p) → RealEuclidean n → RealEuclidean n :=
    fun i y ↦ euclideanFDerivCoordinates (H i) y
  let Phi : (RealEuclidean n × RealEuclidean (q + p)) →
      (RealEuclidean n × RealEuclidean q) := fun z ↦
    L.criticalTraceLogLagrangeFamily g (z, (center, height))
  have hfamily : DifferentiableAt ℝ Phi (x, lambda) := by
    have hfull := (L.contDiffAt_criticalTraceLogLagrangeFamily
      hG hsmooth hderiv g hg x hx lambda center hheight).differentiableAt
        (by norm_num)
    have hemb : DifferentiableAt ℝ
        (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
          (z, (center, height))) (x, lambda) := by
      fun_prop
    simpa only [Phi, Function.comp_def] using
      hfull.comp (x, lambda) hemb
  have hTdiff : DifferentiableAt ℝ T x := by
    have hemb : DifferentiableAt ℝ
        (fun y : RealEuclidean n ↦
          ((y, lambda), (center, height))) x := by
      fun_prop
    have hfull := (L.contDiffAt_criticalTraceLogLagrangeFamily
      hG hsmooth hderiv g hg x hx lambda center hheight).differentiableAt
        (by norm_num)
    have hfixed : DifferentiableAt ℝ
        (fun y : RealEuclidean n ↦
          L.criticalTraceLogLagrangeFamily g
            ((y, lambda), (center, height))) x := by
      exact hfull.comp x hemb
    have hfirst : DifferentiableAt ℝ
        (fun y : RealEuclidean n ↦
          (L.criticalTraceLogLagrangeFamily g
            ((y, lambda), (center, height))).1) x :=
      (ContinuousLinearMap.fst ℝ (RealEuclidean n)
        (RealEuclidean q)).differentiableAt.comp x hfixed
    simpa only [T, criticalTraceLogLagrangeFamily] using hfirst
  have hVdiff : ∀ i, DifferentiableAt ℝ (V i) x := by
    intro i
    rw [differentiableAt_pi]
    intro j
    have hHi : ContDiff ℝ ∞ (H i) :=
      hsmooth n (H i) (L.definingTupleAppend_mem g hg i)
    have hcoord : ContDiff ℝ 1
        (fun y ↦ fderiv ℝ (H i) y (Pi.single j 1)) :=
      ((hHi.fderiv_right (by norm_num)).clm_apply contDiff_const)
    simpa only [V, euclideanFDerivCoordinates] using hcoord.differentiable
      (by norm_num) x
  have hstationarityEq : (fun z ↦ (Phi z).1) =
      (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
        T z.1 - ∑ i, (z.2 i - lambda i) • V i z.1) := by
    funext z
    funext j
    simp only [Phi, T, V, H, criticalTraceLogLagrangeFamily,
      criticalTraceLogStationarityFamily, Pi.sub_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  have hstationarityApply :
      fderiv ℝ (fun z ↦ (Phi z).1) (x, lambda) (v, mu) =
        fderiv ℝ T x v - ∑ i, mu i • V i x := by
    rw [hstationarityEq]
    exact fderiv_affineMultiplierFamily_apply
      T V x v lambda mu hTdiff hVdiff
  have hfirstDerivative :
      fderiv ℝ (fun z ↦ (Phi z).1) (x, lambda) =
        (ContinuousLinearMap.fst ℝ (RealEuclidean n)
          (RealEuclidean q)).comp (fderiv ℝ Phi (x, lambda)) :=
    hfamily.hasFDerivAt.fst.fderiv
  have hsecondDerivative :
      fderiv ℝ (fun z ↦ (Phi z).2) (x, lambda) =
        (ContinuousLinearMap.snd ℝ (RealEuclidean n)
          (RealEuclidean q)).comp (fderiv ℝ Phi (x, lambda)) :=
    hfamily.hasFDerivAt.snd.fderiv
  have hequations : DifferentiableAt ℝ L.equations x :=
    (L.equations_contDiff hsmooth).differentiable (by norm_num) x
  have hsecondFixed :
      fderiv ℝ (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
        L.equations z.1) (x, lambda) =
        (fderiv ℝ L.equations x).comp
          (ContinuousLinearMap.fst ℝ (RealEuclidean n)
            (RealEuclidean (q + p))) :=
    (hequations.hasFDerivAt.comp (x, lambda) hasFDerivAt_fst).fderiv
  apply Prod.ext
  · have hfirstApply := congrArg
      (fun Q : (RealEuclidean n × RealEuclidean (q + p)) →L[ℝ]
          RealEuclidean n ↦ Q (v, mu)) hfirstDerivative
    rw [hstationarityApply] at hfirstApply
    change fderiv ℝ T x v - ∑ i, mu i • V i x =
      (fderiv ℝ Phi (x, lambda) (v, mu)).1 at hfirstApply
    change (fderiv ℝ Phi (x, lambda) (v, mu)).1 =
      fderiv ℝ T x v - ∑ i, mu i • V i x
    exact hfirstApply.symm
  · have hsecondApply := congrArg
      (fun Q : (RealEuclidean n × RealEuclidean (q + p)) →L[ℝ]
          RealEuclidean q ↦ Q (v, mu)) hsecondDerivative
    have hPhiSecond : (fun z ↦ (Phi z).2) =
        fun z : RealEuclidean n × RealEuclidean (q + p) ↦
          L.equations z.1 := by
      rfl
    rw [hPhiSecond, hsecondFixed] at hsecondApply
    change fderiv ℝ L.equations x v =
      (fderiv ℝ Phi (x, lambda) (v, mu)).2 at hsecondApply
    change (fderiv ℝ Phi (x, lambda) (v, mu)).2 =
      fderiv ℝ L.equations x v
    exact hsecondApply.symm

/-- The derivative of an appended tuple is the coordinatewise append of its
two derivative blocks.  This version uses the same `Fin.addCases` ordering as
the row-selection linear algebra above. -/
theorem fderiv_definingTupleAppend_eq_coordinateAppendContinuousLinearMap
    (L : LionCarpetedLeaf G n q)
    {k : ℕ} (h : RealEuclidean n → RealEuclidean k)
    {x : RealEuclidean n}
    (hL : DifferentiableAt ℝ L.equations x)
    (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (L.definingTupleAppend h) x =
      coordinateAppendContinuousLinearMap
        (fderiv ℝ L.equations x) (fderiv ℝ h x) := by
  rw [fderiv_pi]
  · apply ContinuousLinearMap.ext
    intro v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [ContinuousLinearMap.pi_apply,
        coordinateAppendContinuousLinearMap_apply_castAdd]
      rw [show (fun y ↦ L.definingTupleAppend h y (Fin.castAdd k j)) =
          (fun y ↦ L.equations y j) by
        funext y
        exact L.definingTupleAppend_castAdd h y j]
      rw [fderiv_apply hL]
      rfl
    · simp only [ContinuousLinearMap.pi_apply,
        coordinateAppendContinuousLinearMap_apply_natAdd]
      rw [show (fun y ↦ L.definingTupleAppend h y (Fin.natAdd q j)) =
          (fun y ↦ h y j) by
        funext y
        exact L.definingTupleAppend_natAdd h y j]
      rw [fderiv_apply hh]
      rfl
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [L.definingTupleAppend_castAdd] using
        (differentiableAt_pi.mp hL j)
    · simpa only [L.definingTupleAppend_natAdd] using
        (differentiableAt_pi.mp hh j)

/-- A regular zero of the fixed-parameter logarithmic Lagrange system yields
an actual selection of Lion's critical coefficients whose derivatives,
together with the original leaf equations, have full rank. -/
theorem exists_criticalCoefficientSelection_of_fixedParameterLogLagrange_surjective
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    {x : RealEuclidean n} (hx : x ∈ L.criticalTrace g center height)
    (lambda : RealEuclidean (q + p))
    (hzero : L.criticalTraceLogLagrangeFamily g
      ((x, lambda), (center, height)) = 0)
    (hfixed : Function.Surjective
      (fderiv ℝ
        (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
          L.criticalTraceLogLagrangeFamily g
            (z, (center, height)))
        (x, lambda))) :
    ∃ selection : CriticalCoefficientSelection n q p,
      Function.Surjective
        (fderiv ℝ
          (L.definingTupleAppend
            (L.selectedCriticalCoefficientTuple
              g center height selection)) x) := by
  classical
  let H : Fin (q + p) → RealEuclideanFunction n :=
    fun i y ↦ L.definingTupleAppend g y i
  let rho : RealEuclideanFunction n :=
    L.criticalCarpet g center height
  let S : RealEuclidean n → RealEuclidean n :=
    euclideanLogLagrangeStationarityCoordinates H rho lambda
  let T : RealEuclidean n → RealEuclidean n := fun y ↦
    L.criticalTraceLogStationarityFamily g
      ((y, lambda), (center, height))
  let A : RealEuclidean n →L[ℝ] RealEuclidean q :=
    fderiv ℝ L.equations x
  let P : RealEuclidean n →L[ℝ] RealEuclidean n :=
    fderiv ℝ T x
  let B : (Fin ((q + p) + 1) ↪ Fin n) →
      RealEuclidean n →L[ℝ] ℝ := fun cols ↦
    fderiv ℝ (L.criticalCoefficient g center height cols) x
  let D : (RealEuclidean n × RealEuclidean (q + p)) →L[ℝ]
      (RealEuclidean n × RealEuclidean q) :=
    fderiv ℝ
      (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
        L.criticalTraceLogLagrangeFamily g
          (z, (center, height)))
      (x, lambda)
  have hxreg : x ∈ L.regularLocus g := hx.1.2
  have hHdiff : ∀ i, DifferentiableAt ℝ (H i) x := by
    intro i
    exact (hsmooth n (H i)
      (L.definingTupleAppend_mem g hg i)).differentiable (by norm_num) x
  have hHtwo : ∀ i, ContDiffAt ℝ 2 (H i) x := by
    intro i
    exact (hsmooth n (H i)
      (L.definingTupleAppend_mem g hg i)).contDiffAt.of_le (by norm_num)
  have hHsurj : Function.Surjective (constraintFDeriv H x) := by
    have htupleDeriv :
        fderiv ℝ (L.definingTupleAppend g) x =
          constraintFDeriv H x := by
      change fderiv ℝ (fun y i ↦ H i y) x = constraintFDeriv H x
      simpa only [constraintFDeriv] using fderiv_pi hHdiff
    rw [← htupleDeriv]
    exact hxreg.2
  have hA : Function.Surjective A := by
    exact L.fderiv_surjective x hxreg.1
  have hrhoTwo : ContDiffAt ℝ 2 rho x :=
    (hsmooth n rho
      (L.criticalCarpet_mem hG hderiv center hheight g hg)).contDiffAt.of_le
        (by norm_num)
  have hrhoPos : 0 < rho x :=
    (L.criticalCarpet_isLionCarpetOn
      hG hsmooth hderiv center hheight g hg).pos x hxreg
  have hrho0 : rho x ≠ 0 := ne_of_gt hrhoPos
  have hstationary : S x = 0 := by
    rw [show S x = L.criticalTraceLogStationarityFamily g
        ((x, lambda), (center, height)) by
      exact L.euclideanLogLagrangeStationarityCoordinates_eq_criticalTraceLogStationarityFamily
        hG hsmooth hderiv g hg center hheight lambda hxreg]
    exact congrArg Prod.fst hzero
  have hTdiff : DifferentiableAt ℝ T x := by
    have hfull := (L.contDiffAt_criticalTraceLogLagrangeFamily
      hG hsmooth hderiv g hg x hxreg lambda center hheight).differentiableAt
        (by norm_num)
    have hemb : DifferentiableAt ℝ
        (fun y : RealEuclidean n ↦
          ((y, lambda), (center, height))) x := by
      fun_prop
    have hfixedFamily : DifferentiableAt ℝ
        (fun y : RealEuclidean n ↦
          L.criticalTraceLogLagrangeFamily g
            ((y, lambda), (center, height))) x :=
      by simpa only [Function.comp_def] using hfull.comp x hemb
    have hfirst : DifferentiableAt ℝ
        (fun y : RealEuclidean n ↦
          (L.criticalTraceLogLagrangeFamily g
            ((y, lambda), (center, height))).1) x :=
      (ContinuousLinearMap.fst ℝ (RealEuclidean n)
        (RealEuclidean q)).differentiableAt.comp x hfixedFamily
    simpa only [T, criticalTraceLogLagrangeFamily] using hfirst
  have hST : S =ᶠ[nhds x] T := by
    filter_upwards [
      (L.regularLocus_isOpen hG hsmooth hderiv g hg).eventually_mem hxreg]
      with y hy
    exact L.euclideanLogLagrangeStationarityCoordinates_eq_criticalTraceLogStationarityFamily
      hG hsmooth hderiv g hg center hheight lambda hy
  have hSdiff : DifferentiableAt ℝ S x :=
    hST.differentiableAt_iff.mpr hTdiff
  have hSTderiv : fderiv ℝ S x = fderiv ℝ T x := hST.fderiv_eq
  have hDformula : ∀ v mu, D (v, mu) =
      (P v - ∑ i, mu i • euclideanFDerivCoordinates (H i) x, A v) := by
    intro v mu
    simpa only [D, P, T, H, A] using
      (L.fderiv_criticalTraceLogLagrangeFamily_fixedParameter_apply
        hG hsmooth hderiv g hg center hheight lambda hxreg v mu)
  have hBformula : ∀ cols v, B cols v =
      rho x * ∑ j, P v j *
        criticalCofactorTangent H (fun _ ↦ 0)
          (fun k ↦ Pi.single (cols k) 1) x j := by
    intro cols v
    have hdet := fderiv_criticalDeterminant_eq_stationarityDerivative_pairing
      H rho lambda (fun k ↦ Pi.single (cols k) 1) x v
      hHtwo hrhoTwo hrho0 hstationary
    change fderiv ℝ
        (L.criticalCoefficient g center height cols) x v = _
    rw [L.criticalCoefficient_eq_criticalDeterminant] at ⊢
    change fderiv ℝ
        (criticalDeterminant H rho
          (fun k ↦ Pi.single (cols k) 1)) x v = _
    rw [hdet]
    apply congrArg (rho x * ·)
    apply Finset.sum_congr rfl
    intro j _hj
    apply congrArg (· * criticalCofactorTangent H (fun _ ↦ 0)
      (fun k ↦ Pi.single (cols k) 1) x j)
    rw [fderiv_apply hSdiff j, ContinuousLinearMap.comp_apply, hSTderiv]
    rfl
  have hcommon : Module.finrank ℝ
      (A.prod (ContinuousLinearMap.pi B)).ker ≤ p :=
    finrank_commonCriticalDeterminantKernel_le_of_regularLagrangeLinearization
      H x (rho x) A P B D hHdiff hHsurj hfixed hrho0 hDformula hBformula
  obtain ⟨selection, hselection⟩ :=
    exists_selectedCovectorMap_append_surjective_of_commonKernel_finrank_le
      A B hA hcommon (by omega : p + q ≤ n)
  have hselectedDiff : DifferentiableAt ℝ
      (L.selectedCriticalCoefficientTuple
        g center height selection) x := by
    rw [differentiableAt_pi]
    intro i
    exact (hsmooth n
      (fun y ↦ L.selectedCriticalCoefficientTuple
        g center height selection y i)
      (L.selectedCriticalCoefficientTuple_mem
        hG hderiv g hg center hheight selection i)).differentiable
          (by norm_num) x
  have hselectedDeriv :
      fderiv ℝ
          (L.selectedCriticalCoefficientTuple
            g center height selection) x =
        selectedCovectorMap B selection := by
    rw [fderiv_pi]
    · rfl
    · exact differentiableAt_pi.mp hselectedDiff
  refine ⟨selection, ?_⟩
  rw [L.fderiv_definingTupleAppend_eq_coordinateAppendContinuousLinearMap
    (L.selectedCriticalCoefficientTuple g center height selection)
    ((L.equations_contDiff hsmooth).differentiable (by norm_num) x)
    hselectedDiff,
    hselectedDeriv]
  exact hselection

end LionCarpetedLeaf

end AbelFormalization
