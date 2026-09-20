import AbelFormalization.CharbonnelSardianProjectionOneCoordinate
import AbelFormalization.RectangularMorseSard

/-!
# Reduction of the Sardian projection constructor to rectangular Morse--Sard

The local and compact parts of Wilkie's projection argument are complete in
the preceding modules.  This file identifies the remaining analytic theorem
at its standard statement: `C^(a-b+1)` rectangular critical values are null.
From that statement it derives empty interior for the exact-depth finite bad
family and hence the full arbitrary-block Sardian projection constructor.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- The classical rectangular Morse--Sard conclusion at its sharp finite
smoothness order, exposed as the sole analytic input to this reduction. -/
def RectangularMorseSardInput : Prop :=
  ∀ {a b : ℕ} (_hba : b ≤ a)
    (g : RealEuclidean a → RealEuclidean b),
      ContDiff ℝ (a - b + 1 : ℕ) g →
        volume (standardJacobianCriticalValueSet g) = 0

/-- Rectangular Morse--Sard makes the finite union of exact-depth critical
parameter values null. -/
theorem CharbonnelFiniteSardianFamily.volume_exactDepthProjectionCriticalParameterSet_eq_zero
    (hMS : RectangularMorseSardInput)
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    volume (family.exactDepthProjectionCriticalParameterSet hG hsmooth) = 0 := by
  let exacts := sardianProjectionOldExactDepthList hG hsmooth family
  change volume {epsilon | ∃ exactOld ∈ exacts,
    epsilon ∈ standardJacobianCriticalValueSet
      (sardianProjectionOldTuple exactOld)} = 0
  induction exacts with
  | nil => simp
  | cons exactOld exacts ih =>
      have hset :
          {epsilon | ∃ other ∈ exactOld :: exacts,
            epsilon ∈ standardJacobianCriticalValueSet
              (sardianProjectionOldTuple other)} =
            standardJacobianCriticalValueSet
                (sardianProjectionOldTuple exactOld) ∪
              {epsilon | ∃ other ∈ exacts,
                epsilon ∈ standardJacobianCriticalValueSet
                  (sardianProjectionOldTuple other)} := by
        ext epsilon
        simp
      rw [hset]
      apply measure_union_null
      · apply hMS (by omega)
        have hsmoothTuple :=
          contDiff_morseSardOrder_sardianProjectionOldTuple
            hG hsmooth exactOld
        simpa [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one] using
          hsmoothTuple
      · exact ih

/-- The finite exact-depth critical-parameter set is null without an
external Morse--Sard premise: every old tuple is `C^∞`, so the proved smooth
rectangular theorem applies to each member of the finite union. -/
theorem CharbonnelFiniteSardianFamily.volume_exactDepthProjectionCriticalParameterSet_eq_zero_of_smoothFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    volume (family.exactDepthProjectionCriticalParameterSet hG hsmooth) = 0 := by
  let exacts := sardianProjectionOldExactDepthList hG hsmooth family
  change volume {epsilon | ∃ exactOld ∈ exacts,
    epsilon ∈ standardJacobianCriticalValueSet
      (sardianProjectionOldTuple exactOld)} = 0
  induction exacts with
  | nil => simp
  | cons exactOld exacts ih =>
      have hset :
          {epsilon | ∃ other ∈ exactOld :: exacts,
            epsilon ∈ standardJacobianCriticalValueSet
              (sardianProjectionOldTuple other)} =
            standardJacobianCriticalValueSet
                (sardianProjectionOldTuple exactOld) ∪
              {epsilon | ∃ other ∈ exacts,
                epsilon ∈ standardJacobianCriticalValueSet
                  (sardianProjectionOldTuple other)} := by
        ext epsilon
        simp
      rw [hset]
      apply measure_union_null
      · exact volume_standardJacobianCriticalValueSet_eq_zero_of_contDiff_top
          (by omega)
          (contDiff_top_sardianProjectionOldTuple_of_smoothFamily
            hG hsmooth exactOld)
      · exact ih

/-- The same finite exact-depth bad set therefore has empty interior. -/
theorem CharbonnelFiniteSardianFamily.interior_exactDepthProjectionCriticalParameterSet_eq_empty
    (hMS : RectangularMorseSardInput)
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    interior (family.exactDepthProjectionCriticalParameterSet hG hsmooth) =
      ∅ :=
  (volume : Measure (RealEuclidean (K + 1))).interior_eq_empty_of_null
    (family.volume_exactDepthProjectionCriticalParameterSet_eq_zero
      hMS hG hsmooth)

/-- Smoothness of the geometric family therefore gives empty interior of
the exact-depth critical-parameter set directly. -/
theorem CharbonnelFiniteSardianFamily.interior_exactDepthProjectionCriticalParameterSet_eq_empty_of_smoothFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    interior (family.exactDepthProjectionCriticalParameterSet hG hsmooth) =
      ∅ :=
  (volume : Measure (RealEuclidean (K + 1))).interior_eq_empty_of_null
    (family.volume_exactDepthProjectionCriticalParameterSet_eq_zero_of_smoothFamily
      hG hsmooth)

/-- For an Abel family, rectangular Morse--Sard now discharges the complete
positive-hidden-arity projection constructor. -/
theorem IsAbel.charbonnelSardianProjectionConstructorInput_of_rectangularMorseSard
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hMS : RectangularMorseSardInput) :
    CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily f) := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  apply hf.charbonnelSardianProjectionConstructorInput_of_criticalValues
    hUFF h21 h22
  intro order n _horder _hn A old
  exact old.family.interior_exactDepthProjectionCriticalParameterSet_eq_empty
    hMS hG hsmooth

/-- The proved smooth rectangular Morse--Sard theorem discharges the
critical-value step internally. -/
theorem IsAbel.charbonnelSardianProjectionConstructorInput_of_smoothCriticalValues
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f)))) :
    CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily f) := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  apply hf.charbonnelSardianProjectionConstructorInput_of_criticalValues
    hUFF h21 h22
  intro order n _horder _hn A old
  exact old.family.interior_exactDepthProjectionCriticalParameterSet_eq_empty_of_smoothFamily
    hG hsmooth

end AbelFormalization
