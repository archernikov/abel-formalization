import AbelFormalization.LionLemma4CriticalCarpet

/-!
# Radial-parameter transversality in Lion's Lemma 4

For fixed `x`, write

`D_(c,s)(x) = ∑ i, (x_i - c_i)^2 + s^2`.

The `x`-gradient of `log D_(c,s)(x)` has coordinates
`2 * (x_i - c_i) / D_(c,s)(x)`.  This file computes its derivative in the
parameter `(c,s)` and proves that the derivative is surjective whenever
`s > 0`.  This is the analytic parameter-variation input in Lion's
transversality argument for Lemma 4.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The scalar pairing that occurs in the parameter derivative of Lion's
radial logarithmic gradient. -/
def lionRadialParameterPairing {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ) :
    (RealEuclidean n × ℝ) →L[ℝ] ℝ :=
  (∑ j : Fin n, (x j - center j) •
      ((ContinuousLinearMap.proj j : RealEuclidean n →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (RealEuclidean n) ℝ))) -
    height • ContinuousLinearMap.snd ℝ (RealEuclidean n) ℝ

@[simp]
theorem lionRadialParameterPairing_apply {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ)
    (w : RealEuclidean n × ℝ) :
    lionRadialParameterPairing x center height w =
      (∑ j : Fin n, (x j - center j) * w.1 j) - height * w.2 := by
  simp [lionRadialParameterPairing]

/-- Coordinate expression for the derivative of the radial denominator in
the parameter variables. -/
def lionRadialDenominatorParameterDerivative {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ) :
    (RealEuclidean n × ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin n, (2 * (x i - center i)) • (-
      ((ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (RealEuclidean n) ℝ)))) +
    (2 * height) • ContinuousLinearMap.snd ℝ (RealEuclidean n) ℝ

theorem lionRadialDenominatorParameterDerivative_eq_pairing {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ) :
    lionRadialDenominatorParameterDerivative x center height =
      (-2 : ℝ) • lionRadialParameterPairing x center height := by
  apply ContinuousLinearMap.ext
  intro w
  simp [lionRadialDenominatorParameterDerivative,
    lionRadialParameterPairing]
  have hsum :
      (∑ i : Fin n, 2 * (x i - center i) * w.1 i) =
        2 * ∑ i : Fin n, (x i - center i) * w.1 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsum]
  ring

/-- The derivative of the radial denominator with respect to `(center,
height)` is `-2` times the radial parameter pairing. -/
theorem hasFDerivAt_lionLiftedSquaredDistanceDenominator_parameter
    {n : ℕ} (x center : RealEuclidean n) (height : ℝ) :
    HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        lionLiftedSquaredDistanceDenominator a.1 a.2 x)
      (lionRadialDenominatorParameterDerivative x center height)
      (center, height) := by
  let P : Fin n → (RealEuclidean n × ℝ) →L[ℝ] ℝ := fun i ↦
    (ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (RealEuclidean n) ℝ)
  have hcoord : ∀ i, HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦ a.1 i) (P i) (center, height) := by
    intro i
    change HasFDerivAt
      ((ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ) ∘ Prod.fst)
      (P i) (center, height)
    exact (ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).hasFDerivAt.comp
      (center, height) hasFDerivAt_fst
  rw [show (fun a : RealEuclidean n × ℝ ↦
      lionLiftedSquaredDistanceDenominator a.1 a.2 x) =
      fun a ↦ (∑ i : Fin n, (x i - a.1 i) ^ 2) + a.2 ^ 2 by
    funext a
    simp only [lionLiftedSquaredDistanceDenominator,
      standardSquaredDistance, algebraicSquaredDistance_apply,
      Pi.basisFun_equivFun, LinearEquiv.refl_apply]]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦ (x i - a.1 i) ^ 2)
      ((2 * (x i - center i)) • (-(P i)))
      (center, height) := by
    intro i _hi
    simpa only [Nat.reduceSubDiff, pow_one, nsmul_eq_mul, Nat.cast_ofNat] using
      ((hcoord i).const_sub (x i)).pow 2
  have hsum := HasFDerivAt.fun_sum hterm
  have hheightCoord : HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦ a.2)
      (ContinuousLinearMap.snd ℝ (RealEuclidean n) ℝ)
      (center, height) :=
    (ContinuousLinearMap.snd ℝ (RealEuclidean n) ℝ).hasFDerivAt
  have hheight : HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦ a.2 ^ 2)
      ((2 * height) • ContinuousLinearMap.snd ℝ (RealEuclidean n) ℝ)
      (center, height) := by
    simpa only [Nat.reduceSubDiff, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
      using hheightCoord.pow 2
  change HasFDerivAt
    ((fun a : RealEuclidean n × ℝ ↦
        ∑ i : Fin n, (x i - a.1 i) ^ 2) +
      (fun a : RealEuclidean n × ℝ ↦ a.2 ^ 2))
    (lionRadialDenominatorParameterDerivative x center height)
    (center, height)
  simpa only [lionRadialDenominatorParameterDerivative, P] using
    hsum.add hheight

/-- Pairing form of the same denominator derivative. -/
theorem hasFDerivAt_lionLiftedSquaredDistanceDenominator_parameter_pairing
    {n : ℕ} (x center : RealEuclidean n) (height : ℝ) :
    HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        lionLiftedSquaredDistanceDenominator a.1 a.2 x)
      ((-2 : ℝ) • lionRadialParameterPairing x center height)
      (center, height) :=
  (hasFDerivAt_lionLiftedSquaredDistanceDenominator_parameter
    x center height).congr_fderiv
      (lionRadialDenominatorParameterDerivative_eq_pairing x center height)

/-- The normalized parameter variation from Lion's radial formula.  The
actual derivative below is the nonzero scalar `-2 / D` times this map. -/
def lionRadialNormalizedParameterVariation {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ) :
    (RealEuclidean n × ℝ) →L[ℝ] RealEuclidean n :=
  ContinuousLinearMap.pi fun i ↦
    ((ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (RealEuclidean n) ℝ)) -
      ((2 / lionLiftedSquaredDistanceDenominator center height x) *
        (x i - center i)) •
          lionRadialParameterPairing x center height

@[simp]
theorem lionRadialNormalizedParameterVariation_apply {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ)
    (w : RealEuclidean n × ℝ) (i : Fin n) :
    lionRadialNormalizedParameterVariation x center height w i =
      w.1 i -
        (2 / lionLiftedSquaredDistanceDenominator center height x) *
          (x i - center i) *
            ((∑ j : Fin n, (x j - center j) * w.1 j) -
              height * w.2) := by
  simp [lionRadialNormalizedParameterVariation, mul_assoc]

/-- Positive height makes the normalized parameter variation onto.  The
height direction cancels its only rank-one correction. -/
theorem lionRadialNormalizedParameterVariation_surjective {n : ℕ}
    (x center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    Function.Surjective
      (lionRadialNormalizedParameterVariation x center height) := by
  intro y
  let pairing : ℝ := ∑ j : Fin n, (x j - center j) * y j
  refine ⟨(y, pairing / height), ?_⟩
  funext i
  rw [lionRadialNormalizedParameterVariation_apply]
  have hheight0 : height ≠ 0 := ne_of_gt hheight
  have hpairing :
      (∑ j : Fin n, (x j - center j) * y j) -
          height * (pairing / height) = 0 := by
    dsimp only [pairing]
    field_simp
    ring
  rw [hpairing]
  ring

/-- The `x`-gradient of the logarithm of Lion's radial denominator, viewed
as a function of the radial parameter `(center,height)` at fixed `x`. -/
def lionRadialLogDenominatorGradient {n : ℕ}
    (x : RealEuclidean n) (a : RealEuclidean n × ℝ) :
    RealEuclidean n :=
  fun i ↦ 2 * (x i - a.1 i) /
    lionLiftedSquaredDistanceDenominator a.1 a.2 x

/-- The displayed parameter derivative of the radial logarithmic gradient.
It is `-2 / D` times the normalized variation. -/
def lionRadialParameterVariation {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ) :
    (RealEuclidean n × ℝ) →L[ℝ] RealEuclidean n :=
  (-2 / lionLiftedSquaredDistanceDenominator center height x) •
    lionRadialNormalizedParameterVariation x center height

@[simp]
theorem lionRadialParameterVariation_apply {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ)
    (w : RealEuclidean n × ℝ) (i : Fin n) :
    lionRadialParameterVariation x center height w i =
      (-2 / lionLiftedSquaredDistanceDenominator center height x) *
        (w.1 i -
          (2 / lionLiftedSquaredDistanceDenominator center height x) *
            (x i - center i) *
              ((∑ j : Fin n, (x j - center j) * w.1 j) -
                height * w.2)) := by
  simp [lionRadialParameterVariation]

theorem lionRadialParameterVariation_eq_pi {n : ℕ}
    (x center : RealEuclidean n) (height : ℝ) :
    lionRadialParameterVariation x center height =
      ContinuousLinearMap.pi (fun i ↦
        (-2 / lionLiftedSquaredDistanceDenominator center height x) •
          (((ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).comp
              (ContinuousLinearMap.fst ℝ (RealEuclidean n) ℝ)) -
            ((2 / lionLiftedSquaredDistanceDenominator center height x) *
              (x i - center i)) •
                lionRadialParameterPairing x center height)) := by
  apply ContinuousLinearMap.ext
  intro w
  funext i
  simp [lionRadialParameterVariation,
    lionRadialNormalizedParameterVariation]

/-- The displayed variation map is the actual Fréchet derivative, in the
radial parameter, of the `x`-gradient of the logarithmic denominator. -/
theorem hasFDerivAt_lionRadialLogDenominatorGradient_parameter {n : ℕ}
    (x center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    HasFDerivAt (lionRadialLogDenominatorGradient x)
      (lionRadialParameterVariation x center height) (center, height) := by
  rw [lionRadialParameterVariation_eq_pi]
  apply hasFDerivAt_pi.mpr
  intro i
  let P : (RealEuclidean n × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (RealEuclidean n) ℝ)
  let D : ℝ := lionLiftedSquaredDistanceDenominator center height x
  have hD : D ≠ 0 :=
    lionLiftedSquaredDistanceDenominator_ne_zero center hheight x
  have hcoord : HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦ a.1 i) P (center, height) := by
    change HasFDerivAt
      ((ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ) ∘ Prod.fst)
      P (center, height)
    exact (ContinuousLinearMap.proj i : RealEuclidean n →L[ℝ] ℝ).hasFDerivAt.comp
      (center, height) hasFDerivAt_fst
  have hnum := ((hcoord.const_sub (x i)).const_mul 2)
  have hden :=
    hasFDerivAt_lionLiftedSquaredDistanceDenominator_parameter_pairing
      x center height
  have hinv : HasFDerivAt
      (fun a : RealEuclidean n × ℝ ↦
        (lionLiftedSquaredDistanceDenominator a.1 a.2 x)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(D ^ 2)⁻¹)).comp
        ((-2 : ℝ) • lionRadialParameterPairing x center height))
      (center, height) := by
    change HasFDerivAt
      ((fun z : ℝ ↦ z⁻¹) ∘
        (fun a : RealEuclidean n × ℝ ↦
          lionLiftedSquaredDistanceDenominator a.1 a.2 x))
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(D ^ 2)⁻¹)).comp
        ((-2 : ℝ) • lionRadialParameterPairing x center height))
      (center, height)
    exact (hasFDerivAt_inv hD).comp (center, height) hden
  change HasFDerivAt
    (fun a : RealEuclidean n × ℝ ↦
      2 * (x i - a.1 i) /
        lionLiftedSquaredDistanceDenominator a.1 a.2 x)
    ((-2 / D) •
      (P - ((2 / D) * (x i - center i)) •
        lionRadialParameterPairing x center height))
    (center, height)
  convert hnum.mul hinv using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro w
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    neg_apply, sub_apply,
    smul_eq_mul, P, lionRadialParameterPairing_apply]
  rw [show lionLiftedSquaredDistanceDenominator center height x = D by rfl]
  field_simp [hD]
  ring

theorem fderiv_lionRadialLogDenominatorGradient_parameter {n : ℕ}
    (x center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    fderiv ℝ (lionRadialLogDenominatorGradient x) (center, height) =
      lionRadialParameterVariation x center height :=
  (hasFDerivAt_lionRadialLogDenominatorGradient_parameter
    x center hheight).fderiv

/-- The actual radial-gradient parameter derivative is surjective at every
positive height. -/
theorem lionRadialParameterVariation_surjective {n : ℕ}
    (x center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    Function.Surjective (lionRadialParameterVariation x center height) := by
  let D := lionLiftedSquaredDistanceDenominator center height x
  have hD : D ≠ 0 :=
    lionLiftedSquaredDistanceDenominator_ne_zero center hheight x
  have hscalar : (-2 / D : ℝ) ≠ 0 := by
    exact div_ne_zero (by norm_num) hD
  intro y
  obtain ⟨w, hw⟩ := lionRadialNormalizedParameterVariation_surjective
    x center hheight ((-2 / D)⁻¹ • y)
  refine ⟨w, ?_⟩
  change (-2 / D) •
      lionRadialNormalizedParameterVariation x center height w = y
  rw [hw]
  exact smul_inv_smul₀ hscalar y

/-- In derivative form, the radial logarithmic gradient is a submersion in
the parameter variables at every positive height. -/
theorem fderiv_lionRadialLogDenominatorGradient_parameter_surjective
    {n : ℕ} (x center : RealEuclidean n) {height : ℝ}
    (hheight : 0 < height) :
    Function.Surjective
      (fderiv ℝ (lionRadialLogDenominatorGradient x) (center, height)) := by
  rw [fderiv_lionRadialLogDenominatorGradient_parameter x center hheight]
  exact lionRadialParameterVariation_surjective x center hheight

/-- Surjectivity survives every surjective linear quotient of the ambient
gradient coordinates.  This is the form used after passing to tangent or
normal coordinates in the `z`-transversality argument. -/
theorem lionRadialLogDenominatorGradient_parameter_quotient_surjective
    {n m : ℕ} (x center : RealEuclidean n) {height : ℝ}
    (hheight : 0 < height)
    (Q : RealEuclidean n →L[ℝ] RealEuclidean m)
    (hQ : Function.Surjective Q) :
    Function.Surjective
      (Q.comp
        (fderiv ℝ (lionRadialLogDenominatorGradient x)
          (center, height))) := by
  rw [fderiv_lionRadialLogDenominatorGradient_parameter x center hheight]
  intro y
  obtain ⟨z, hz⟩ := hQ y
  obtain ⟨w, hw⟩ :=
    lionRadialParameterVariation_surjective x center hheight z
  refine ⟨w, ?_⟩
  simp only [ContinuousLinearMap.comp_apply, hw, hz]

end AbelFormalization
