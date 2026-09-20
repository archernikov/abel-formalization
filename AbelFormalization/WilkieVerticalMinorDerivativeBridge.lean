import AbelFormalization.WilkieVerticalMinorLocalProjection
import AbelFormalization.LionGlobalSubmersionFixedSquare

/-!
# A vertical minor supplies the square-map inverse-function chart

The hidden-column minor is the determinant of the derivative of `F` in the
second block of coordinates.  Its nonvanishing makes that derivative block
bijective.  The derivative of `(takeLeft, F)` is then a triangular continuous
linear map with an identity visible block and a bijective hidden block.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- A nonzero fixed hidden-column minor makes the square map recording the
visible coordinates and the fiber value strictly differentiable by a
continuous linear equivalence. -/
theorem wilkieVisibleFiberSquareMap_hasStrictFDerivAt_of_verticalMinor
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) {y : RealEuclidean (n + k)}
    (hminor : standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0) :
    ∃ L : RealEuclidean (n + k) ≃L[ℝ]
        (RealEuclidean n × RealEuclidean k),
      HasStrictFDerivAt (wilkieVisibleFiberSquareMap F)
        (L : RealEuclidean (n + k) →L[ℝ]
          (RealEuclidean n × RealEuclidean k)) y := by
  let D : RealEuclidean (n + k) →L[ℝ] RealEuclidean k := fderiv ℝ F y
  let E : (RealEuclidean n × RealEuclidean k) ≃L[ℝ]
      RealEuclidean (n + k) := realEuclideanAppendContinuousLinearEquiv n k
  let H : RealEuclidean k →L[ℝ] RealEuclidean (n + k) :=
    E.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (RealEuclidean n) (RealEuclidean k))
  let K : RealEuclidean k →L[ℝ] RealEuclidean k := D.comp H
  let A : Matrix (Fin k) (Fin k) ℝ :=
    (standardRectangularJacobian F y).submatrix id (Fin.natAddEmb n)
  have hA : A.det ≠ 0 := hminor
  have hFstrict : HasStrictFDerivAt F D y :=
    hF.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hFdiff : DifferentiableAt ℝ F y := hFstrict.differentiableAt
  have hKapply (z : RealEuclidean k) :
      K z = D (realEuclideanAppend 0 z) := by
    change D (E (0, z)) = D (realEuclideanAppend 0 z)
    rfl
  have hHiddenBasis (j : Fin k) :
      realEuclideanAppend (0 : RealEuclidean n)
        ((Pi.basisFun ℝ (Fin k)) j) =
      ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j)) := by
    funext t
    refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) t
    · have hne : Fin.castAdd k i ≠ Fin.natAdd n j := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      simp [Pi.basisFun_apply, hne]
    · by_cases hq : q = j
      · subst q
        simp
      · have hne : Fin.natAdd n q ≠ Fin.natAdd n j := by
          intro heq
          exact hq ((Fin.natAddEmb n).injective heq)
        simp [Pi.basisFun_apply, hq, hne]
  have hKmatrix :
      LinearMap.toMatrix'
        (K : RealEuclidean k →ₗ[ℝ] RealEuclidean k) = A := by
    ext i j
    have hbasis :
        realEuclideanAppend (0 : RealEuclidean n) (Pi.single j 1) =
        ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j)) := by
      simpa only [Pi.basisFun_apply] using hHiddenBasis j
    simp only [LinearMap.toMatrix'_apply]
    change K (Pi.single j 1) i =
      fderiv ℝ (fun z : RealEuclidean (n + k) ↦ F z i) y
        ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j))
    rw [← hbasis, hKapply, fderiv_apply hFdiff i]
    rfl
  have hKfactor (z : RealEuclidean k) : K z = A.mulVec z := by
    calc
      K z = (LinearMap.toMatrix'
          (K : RealEuclidean k →ₗ[ℝ] RealEuclidean k)).mulVec z :=
        (LinearMap.toMatrix'_mulVec
          (K : RealEuclidean k →ₗ[ℝ] RealEuclidean k) z).symm
      _ = A.mulVec z := by rw [hKmatrix]
  have hKinj : Function.Injective K := by
    intro z w hzw
    apply A.mulVec_injective_of_det_ne_zero hA
    rw [← hKfactor z, ← hKfactor w]
    exact hzw
  have hKsurj : Function.Surjective K :=
    (K : RealEuclidean k →ₗ[ℝ] RealEuclidean k).surjective_of_injective hKinj
  let P : RealEuclidean (n + k) →L[ℝ] RealEuclidean n :=
    realEuclideanTakeLeftContinuousLinearMap n k
  let M : RealEuclidean (n + k) →L[ℝ]
      (RealEuclidean n × RealEuclidean k) := P.prod D
  have hMapply (v : RealEuclidean (n + k)) :
      M v = (realEuclideanTakeLeft v, D v) := rfl
  have hAppendSplit (x : RealEuclidean n) (z : RealEuclidean k) :
      realEuclideanAppend x z =
        realEuclideanAppend x (0 : RealEuclidean k) +
          realEuclideanAppend (0 : RealEuclidean n) z := by
    funext t
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) t <;> simp
  have hDsplit (x : RealEuclidean n) (z : RealEuclidean k) :
      D (realEuclideanAppend x z) =
        D (realEuclideanAppend x 0) + K z := by
    rw [hAppendSplit, D.map_add, ← hKapply]
  have hMinj : Function.Injective M := by
    intro v w hvw
    have hleft : realEuclideanTakeLeft v = realEuclideanTakeLeft w :=
      congrArg Prod.fst (by simpa only [hMapply] using hvw)
    have hderiv : D v = D w :=
      congrArg Prod.snd (by simpa only [hMapply] using hvw)
    let x : RealEuclidean n := realEuclideanTakeLeft v
    let zv : RealEuclidean k := realEuclideanTakeRight v
    let zw : RealEuclidean k := realEuclideanTakeRight w
    have hwleft : realEuclideanTakeLeft w = x := hleft.symm
    have hblocks :
        D (realEuclideanAppend x zv) =
          D (realEuclideanAppend x zw) := by
      calc
        D (realEuclideanAppend x zv) = D v :=
          congrArg D (realEuclideanAppend_takeLeft_takeRight v)
        _ = D w := hderiv
        _ = D (realEuclideanAppend x zw) := by
          simpa only [hwleft] using
            (congrArg D (realEuclideanAppend_takeLeft_takeRight w)).symm
    have hKblocks : K zv = K zw := by
      have hs : D (realEuclideanAppend x 0) + K zv =
          D (realEuclideanAppend x 0) + K zw := by
        calc
          D (realEuclideanAppend x 0) + K zv =
              D (realEuclideanAppend x zv) := (hDsplit x zv).symm
          _ = D (realEuclideanAppend x zw) := hblocks
          _ = D (realEuclideanAppend x 0) + K zw := hDsplit x zw
      exact add_left_cancel hs
    have hz : zv = zw := hKinj hKblocks
    calc
      v = realEuclideanAppend x zv :=
        (realEuclideanAppend_takeLeft_takeRight v).symm
      _ = realEuclideanAppend x zw := by rw [hz]
      _ = w := by
        simpa only [hwleft] using
          (realEuclideanAppend_takeLeft_takeRight w)
  have hMsurj : Function.Surjective M := by
    intro p
    obtain ⟨z, hz⟩ :=
      hKsurj (p.2 - D (realEuclideanAppend p.1 (0 : RealEuclidean k)))
    refine ⟨realEuclideanAppend p.1 z, ?_⟩
    apply Prod.ext
    · exact realEuclideanTakeLeft_append p.1 z
    · change D (realEuclideanAppend p.1 z) = p.2
      rw [hDsplit, hz]
      abel
  have hPstrict : HasStrictFDerivAt realEuclideanTakeLeft P y :=
    P.hasStrictFDerivAt
  have hSquareStrict :
      HasStrictFDerivAt (wilkieVisibleFiberSquareMap F) M y := by
    change HasStrictFDerivAt
      (fun z ↦ (realEuclideanTakeLeft z, F z)) (P.prod D) y
    exact hPstrict.prodMk hFstrict
  have hKer : M.ker = ⊥ := LinearMap.ker_eq_bot.mpr hMinj
  have hRange : M.range = ⊤ := LinearMap.range_eq_top.mpr hMsurj
  let L : RealEuclidean (n + k) ≃L[ℝ]
      (RealEuclidean n × RealEuclidean k) :=
    ContinuousLinearEquiv.ofBijective M hKer hRange
  refine ⟨L, ?_⟩
  simpa only [L, ContinuousLinearEquiv.coe_ofBijective] using hSquareStrict

/-- This is the `hSquare` premise of
`wilkieVerticalMinor_component_projection_eq_of_squareChart`, obtained
pointwise from the fixed hidden-column minor. -/
theorem wilkieVerticalMinor_squareChart_of_verticalMinor
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} {x : RealEuclidean (n + k)} :
    ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 →
        ∃ L : RealEuclidean (n + k) ≃L[ℝ]
          (RealEuclidean n × RealEuclidean k),
          HasStrictFDerivAt (wilkieVisibleFiberSquareMap F)
            (L : RealEuclidean (n + k) →L[ℝ]
              (RealEuclidean n × RealEuclidean k)) y := by
  intro y _ hyMinor
  exact wilkieVisibleFiberSquareMap_hasStrictFDerivAt_of_verticalMinor hF hyMinor

/-- A bounded regular fiber component whose fixed hidden-column minor stays
nonzero projects onto the entire connected open visible target.  The missing
part of Wilkie's alternative is to force a zero of this minor on a bounded
component when a visible point is missed. -/
theorem wilkieVerticalMinor_component_projection_eq_of_nonzeroMinor
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hU : IsPreconnected U)
    (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    {x : RealEuclidean (n + k)}
    (hx : x ∈ wilkieFiberOver F a U)
    (hminor : ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0) :
    realEuclideanTakeLeft '' wilkieFiberComponent F a U x = U := by
  exact wilkieVerticalMinor_component_projection_eq_of_squareChart
    hF a hU hUopen hregular hbounded hx hminor
    (wilkieVerticalMinor_squareChart_of_verticalMinor hF a)

end AbelFormalization
