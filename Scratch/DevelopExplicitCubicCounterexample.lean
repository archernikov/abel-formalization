import AbelFormalization.LionRankPatchLocalRegularSubtupleReduction

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

private def tripleRootPolynomial (x : ℝ) : ℝ :=
  ((x + 1) * x * (x - 1)) ^ 3

private def tripleRootBase (x : ℝ) : ℝ :=
  (x + 1) * x * (x - 1)

private def tripleRootFirstDerivative (x : ℝ) : ℝ :=
  3 * tripleRootBase x ^ 2 * (3 * x ^ 2 - 1)

private def threeTripleRootMap : RealEuclidean 1 → RealEuclidean 1 :=
  fun x _ ↦ tripleRootPolynomial (x 0)

private def rankZeroPatchIndexOne : RankMinorPatchIndex 1 1 :=
  ⟨⟨0, by omega⟩,
    Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩

private def threeRoot (q : Fin 3) : ℝ := (q : ℝ) - 1

private def threeRootLift (q : Fin 3) : RealEuclidean 2 :=
  realEuclideanAppendScalar (fun _ ↦ threeRoot q) 1

example : successorMinorCount 1 1 0 = 1 := by
  simp [successorMinorCount]

example (q : Fin 3) : tripleRootPolynomial (threeRoot q) = 0 := by
  fin_cases q <;> norm_num [tripleRootPolynomial, threeRoot]

example : ContDiff ℝ 2 threeTripleRootMap := by
  unfold threeTripleRootMap tripleRootPolynomial
  fun_prop

private theorem fderiv_tripleRootPolynomial_apply
    (x dx : RealEuclidean 1) :
    fderiv ℝ (fun y : RealEuclidean 1 ↦ tripleRootPolynomial (y 0)) x dx =
      tripleRootFirstDerivative (x 0) * dx 0 := by
  have hcoord : HasFDerivAt (fun y : RealEuclidean 1 ↦ y 0)
      (ContinuousLinearMap.proj 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have hbase := ((hcoord.const_add 1).mul hcoord).mul (hcoord.sub_const 1)
  have hcub := hbase.pow 3
  have hfun :
      (fun y : RealEuclidean 1 ↦ tripleRootPolynomial (y 0)) =
        fun y ↦
          ((((fun z : RealEuclidean 1 ↦ 1 + z 0) *
            fun z : RealEuclidean 1 ↦ z 0) *
              fun z : RealEuclidean 1 ↦ z 0 - 1) y) ^ 3 := by
    funext y
    simp [tripleRootPolynomial, add_comm]
  rw [hfun, hcub.fderiv]
  simp [tripleRootFirstDerivative, tripleRootBase]
  ring

private theorem standardJacobianMinor_threeTripleRootMap_eq
    (rows cols : Fin 1 ↪ Fin 1) :
    standardJacobianMinor threeTripleRootMap rows cols =
      fun x ↦ tripleRootFirstDerivative (x 0) := by
  funext x
  have hrows : rows 0 = 0 := Subsingleton.elim _ _
  have hcols : cols 0 = 0 := Subsingleton.elim _ _
  simp [standardJacobianMinor, standardRectangularJacobian,
    threeTripleRootMap, hrows, hcols,
    fderiv_tripleRootPolynomial_apply]

private theorem fderiv_tripleRootFirstDerivative_at_root
    (q : Fin 3) :
    fderiv ℝ (fun y : RealEuclidean 1 ↦
      tripleRootFirstDerivative (y 0))
      (fun _ ↦ threeRoot q) = 0 := by
  let x : RealEuclidean 1 := fun _ ↦ threeRoot q
  have hcoord : HasFDerivAt (fun y : RealEuclidean 1 ↦ y 0)
      (ContinuousLinearMap.proj 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have hbase := ((hcoord.const_add 1).mul hcoord).mul (hcoord.sub_const 1)
  have hbaseZero : (1 + x 0) * x 0 * (x 0 - 1) = 0 := by
    fin_cases q <;> norm_num [x, threeRoot]
  have hsquare : HasFDerivAt
      (fun y : RealEuclidean 1 ↦
        ((((fun z : RealEuclidean 1 ↦ 1 + z 0) *
          fun z : RealEuclidean 1 ↦ z 0) *
            fun z : RealEuclidean 1 ↦ z 0 - 1) y) ^ 2)
      (0 : RealEuclidean 1 →L[ℝ] ℝ) x := by
    simpa [hbaseZero] using hbase.pow 2
  have hcoefficient : DifferentiableAt ℝ
      (fun y : RealEuclidean 1 ↦ 3 * y 0 ^ 2 - 1) x := by
    fun_prop
  have hproduct := (hsquare.const_mul 3).mul hcoefficient.hasFDerivAt
  have hfunction :
      (fun y : RealEuclidean 1 ↦ tripleRootFirstDerivative (y 0)) =
        fun y ↦ 3 * (((1 + y 0) * y 0 * (y 0 - 1)) ^ 2) *
          (3 * y 0 ^ 2 - 1) := by
    funext y
    simp [tripleRootFirstDerivative, tripleRootBase, add_comm]
  rw [hfunction]
  have hzero : HasFDerivAt
      (fun y : RealEuclidean 1 ↦
        3 * (((1 + y 0) * y 0 * (y 0 - 1)) ^ 2) *
          (3 * y 0 ^ 2 - 1))
      (0 : RealEuclidean 1 →L[ℝ] ℝ) x := by
    simpa only [Pi.mul_apply] using hproduct
  simpa only [x] using hzero.fderiv

private theorem tripleRootPolynomial_hasFDerivAt_zero
    (x : RealEuclidean 1)
    (hx : (x 0 + 1) * x 0 * (x 0 - 1) = 0) :
    HasFDerivAt (fun y : RealEuclidean 1 ↦ tripleRootPolynomial (y 0))
      (0 : RealEuclidean 1 →L[ℝ] ℝ) x := by
  have hcoord : HasFDerivAt (fun y : RealEuclidean 1 ↦ y 0)
      (ContinuousLinearMap.proj 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have hbase := ((hcoord.const_add 1).mul hcoord).mul (hcoord.sub_const 1)
  have hcub := hbase.pow 3
  have hbaseZero : (1 + x 0) * x 0 * (x 0 - 1) = 0 := by
    simpa [add_comm] using hx
  simpa [tripleRootPolynomial, hbaseZero, add_comm] using hcub

example (q : Fin 3) : fderiv ℝ threeTripleRootMap
    (fun _ : Fin 1 ↦ threeRoot q) = 0 := by
  let x : RealEuclidean 1 := fun _ ↦ threeRoot q
  have hx : (x 0 + 1) * x 0 * (x 0 - 1) = 0 := by
    fin_cases q <;> norm_num [x, threeRoot]
  have hs := tripleRootPolynomial_hasFDerivAt_zero x hx
  have hg' : HasFDerivAt threeTripleRootMap
      (ContinuousLinearMap.pi
        (fun _ : Fin 1 ↦ (0 : RealEuclidean 1 →L[ℝ] ℝ))) x := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    simpa [threeTripleRootMap] using hs
  have hg : HasFDerivAt threeTripleRootMap
      (0 : RealEuclidean 1 →L[ℝ] RealEuclidean 1) x := by
    simpa only [ContinuousLinearMap.pi_zero] using hg'
  simpa only [x] using hg.fderiv

end AbelFormalization
