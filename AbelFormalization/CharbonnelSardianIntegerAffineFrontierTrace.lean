import AbelFormalization.CharbonnelSardianIntegerAffineFamilySectionBridge
import AbelFormalization.CharbonnelIntegerAffineSignCellFrontier

/-!
# The frontier-trace modulus for a Sardian integer-affine slice

This module constructs the nested-modulus splice used when two new radial
and affine-level parameters are inserted before the old finite Sardian
family parameters.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## A uniform error scale for the affine level -/

/-- A positive Lipschitz constant for the displayed integer-affine form in
the finite-coordinate maximum metric. -/
def integerAffineSliceLipschitzConstant {n : ℕ}
    (coeff : Fin n → ℤ) : ℝ :=
  1 + ∑ i : Fin n, |(coeff i : ℝ)|

theorem integerAffineSliceLipschitzConstant_pos {n : ℕ}
    (coeff : Fin n → ℤ) :
    0 < integerAffineSliceLipschitzConstant coeff := by
  unfold integerAffineSliceLipschitzConstant
  have hsum : 0 ≤ ∑ i : Fin n, |(coeff i : ℝ)| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  linarith

theorem abs_integerAffineSliceLinearForm_sub_le
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (x y : RealEuclidean n) :
    |integerAffineSliceLinearForm coeff constant y -
        integerAffineSliceLinearForm coeff constant x| ≤
      integerAffineSliceLipschitzConstant coeff * dist x y := by
  have hsub :
      integerAffineSliceLinearForm coeff constant y -
          integerAffineSliceLinearForm coeff constant x =
        ∑ i : Fin n, (coeff i : ℝ) * (y i - x i) := by
    simp only [integerAffineSliceLinearForm]
    calc
      (∑ j : Fin n, (coeff j : ℝ) * y j) + (constant : ℝ) -
          ((∑ j : Fin n, (coeff j : ℝ) * x j) + (constant : ℝ)) =
          (∑ j : Fin n, (coeff j : ℝ) * y j) -
            ∑ j : Fin n, (coeff j : ℝ) * x j := by ring
      _ = ∑ i : Fin n,
          ((coeff i : ℝ) * y i - (coeff i : ℝ) * x i) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin n, (coeff i : ℝ) * (y i - x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hcoord : ∀ i : Fin n, |y i - x i| ≤ dist x y := by
    intro i
    have hi := (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).mp
      (le_refl (dist x y)) i
    simpa only [Real.dist_eq, abs_sub_comm] using hi
  rw [hsub]
  calc
    |∑ i : Fin n, (coeff i : ℝ) * (y i - x i)| ≤
        ∑ i : Fin n, |(coeff i : ℝ) * (y i - x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |(coeff i : ℝ)| * |y i - x i| := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_mul _ _
    _ ≤ ∑ i : Fin n, |(coeff i : ℝ)| * dist x y := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
    _ = (∑ i : Fin n, |(coeff i : ℝ)|) * dist x y := by
      rw [Finset.sum_mul]
    _ ≤ integerAffineSliceLipschitzConstant coeff * dist x y := by
      unfold integerAffineSliceLipschitzConstant
      exact mul_le_mul_of_nonneg_right
        (by linarith :
          (∑ i : Fin n, |(coeff i : ℝ)|) ≤
            1 + ∑ i : Fin n, |(coeff i : ℝ)|)
        dist_nonneg

/-- An old approximation error below this cap forces the approximating point
into the prescribed positive squared affine-level band. -/
def integerAffineSliceErrorCap {n : ℕ}
    (coeff : Fin n → ℤ) (slice : ℝ) : ℝ :=
  Real.sqrt slice /
    (2 * integerAffineSliceLipschitzConstant coeff)

theorem integerAffineSliceErrorCap_pos {n : ℕ}
    (coeff : Fin n → ℤ) {slice : ℝ} (hslice : 0 < slice) :
    0 < integerAffineSliceErrorCap coeff slice := by
  unfold integerAffineSliceErrorCap
  exact div_pos (Real.sqrt_pos.2 hslice)
    (mul_pos (by norm_num) (integerAffineSliceLipschitzConstant_pos coeff))

theorem integerAffineSlice_sq_le_of_dist_lt_errorCap
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    {slice : ℝ} (hslice : 0 < slice)
    {x y : RealEuclidean n}
    (hx : x ∈ integerAffineSliceHyperplane coeff constant)
    (hxy : dist x y < integerAffineSliceErrorCap coeff slice) :
    (integerAffineSliceLinearForm coeff constant y) ^ 2 ≤ slice := by
  let C := integerAffineSliceLipschitzConstant coeff
  have hC : 0 < C := integerAffineSliceLipschitzConstant_pos coeff
  have hxzero : integerAffineSliceLinearForm coeff constant x = 0 := hx
  have habs : |integerAffineSliceLinearForm coeff constant y| ≤
      C * dist x y := by
    simpa only [hxzero, sub_zero, C] using
      abs_integerAffineSliceLinearForm_sub_le coeff constant x y
  have hsqrt : 0 < Real.sqrt slice := Real.sqrt_pos.2 hslice
  have hcap : C * integerAffineSliceErrorCap coeff slice =
      Real.sqrt slice / 2 := by
    change C * (Real.sqrt slice / (2 * C)) = Real.sqrt slice / 2
    field_simp [ne_of_gt hC]
  have habsLt : |integerAffineSliceLinearForm coeff constant y| <
      Real.sqrt slice := by
    calc
      |integerAffineSliceLinearForm coeff constant y| ≤
          C * dist x y := habs
      _ < C * integerAffineSliceErrorCap coeff slice :=
        mul_lt_mul_of_pos_left hxy hC
      _ = Real.sqrt slice / 2 := hcap
      _ < Real.sqrt slice := by linarith
  have hsqrtSq : (Real.sqrt slice) ^ 2 = slice :=
    Real.sq_sqrt hslice.le
  have habsSq : |integerAffineSliceLinearForm coeff constant y| ^ 2 =
      (integerAffineSliceLinearForm coeff constant y) ^ 2 :=
    sq_abs _
  have hsquares : |integerAffineSliceLinearForm coeff constant y| ^ 2 <
      (Real.sqrt slice) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg _)
      (Real.sqrt_nonneg _)).2 habsLt
  rw [habsSq, hsqrtSq] at hsquares
  exact hsquares.le

/-! ## Splicing two parameters after the approximation error -/

/-- The first three coordinates of a parameter vector: approximation error,
radial level, and affine-slice level. -/
def wilkieAffineSliceFirstThree {k : ℕ}
    (epsilon : RealEuclidean (k + 3)) : RealEuclidean 3 :=
  fun i ↦ epsilon ⟨i.val, by omega⟩

@[simp]
theorem wilkieAffineSliceFirstThree_init {k : ℕ}
    (epsilon : RealEuclidean ((k + 1) + 3)) :
    wilkieAffineSliceFirstThree (Fin.init epsilon) =
      wilkieAffineSliceFirstThree epsilon := by
  rfl

/-- Replace the three new leading coordinates by one chosen old error,
retaining all old family parameters which follow them. -/
def wilkieAffineSliceOldPrefix {k : ℕ}
    (oldError : RealEuclidean 3 → ℝ)
    (epsilon : RealEuclidean (k + 3)) : RealEuclidean (k + 1) :=
  Fin.cases (oldError (wilkieAffineSliceFirstThree epsilon))
    (fun i ↦ epsilon ⟨i.val + 3, by omega⟩)

@[simp]
theorem wilkieAffineSliceOldPrefix_zero {k : ℕ}
    (oldError : RealEuclidean 3 → ℝ)
    (epsilon : RealEuclidean (k + 3)) :
    wilkieAffineSliceOldPrefix oldError epsilon 0 =
      oldError (wilkieAffineSliceFirstThree epsilon) :=
  rfl

theorem wilkieAffineSliceOldPrefix_pos {k : ℕ}
    (oldError : RealEuclidean 3 → ℝ)
    (holdError : ∀ epsilon : RealEuclidean 3,
      (∀ i, 0 < epsilon i) → 0 < oldError epsilon)
    (epsilon : RealEuclidean (k + 3))
    (hepsilon : ∀ i, 0 < epsilon i) :
    ∀ i, 0 < wilkieAffineSliceOldPrefix oldError epsilon i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · apply holdError
    intro j
    exact hepsilon ⟨j.val, by omega⟩
  · exact hepsilon ⟨j.val + 3, by omega⟩

theorem wilkieAffineSliceOldPrefix_init {k : ℕ}
    (oldError : RealEuclidean 3 → ℝ)
    (epsilon : RealEuclidean ((k + 1) + 3)) :
    wilkieAffineSliceOldPrefix oldError (Fin.init epsilon) =
      Fin.init (wilkieAffineSliceOldPrefix oldError epsilon) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

theorem wilkieAffineSliceOldPrefix_last {k : ℕ}
    (oldError : RealEuclidean 3 → ℝ)
    (epsilon : RealEuclidean ((k + 1) + 3)) :
    wilkieAffineSliceOldPrefix oldError epsilon (Fin.last (k + 1)) =
      epsilon (Fin.last (k + 3)) := by
  rfl

namespace CharbonnelModulus

/-- The first, approximation-error bound of a nested modulus. -/
def firstBound : {k : ℕ} → CharbonnelModulus k → ℝ
  | 0, .base bound _ => bound
  | _ + 1, .step initial _ _ => firstBound initial

theorem firstBound_pos : ∀ {k : ℕ} (mu : CharbonnelModulus k),
    0 < mu.firstBound := by
  intro k mu
  induction mu with
  | base bound hbound => simpa only [firstBound] using hbound
  | step initial lastBound hlast ih => simpa only [firstBound] using ih

/-- Insert radial and slice parameters after the approximation error and
before all old family parameters.  The old error is reconstructed as a
positive function of the new first three coordinates. -/
def insertTwoAfterError
    (initialThree : CharbonnelModulus 2)
    (oldError : RealEuclidean 3 → ℝ)
    (holdError : ∀ epsilon : RealEuclidean 3,
      (∀ i, 0 < epsilon i) → 0 < oldError epsilon) :
    {K : ℕ} → CharbonnelModulus (K + 1) →
      CharbonnelModulus (K + 3)
  | 0, .step (.base _ _) lastBound hlast =>
      .step initialThree
        (fun epsilon ↦
          lastBound (wilkieAffineSliceOldPrefix oldError epsilon))
        (fun epsilon hepsilon ↦
          hlast _ (wilkieAffineSliceOldPrefix_pos
            oldError holdError epsilon hepsilon))
  | K + 1, .step initial lastBound hlast =>
      .step (insertTwoAfterError initialThree oldError holdError initial)
        (fun epsilon ↦
          lastBound (wilkieAffineSliceOldPrefix oldError epsilon))
        (fun epsilon hepsilon ↦
          hlast _ (wilkieAffineSliceOldPrefix_pos
            oldError holdError epsilon hepsilon))

/-- Boundedness for the spliced modulus gives boundedness for the old
modulus after reconstructing the old approximation error. -/
theorem isBounded_insertTwoAfterError_oldPrefix
    (initialThree : CharbonnelModulus 2)
    (oldError : RealEuclidean 3 → ℝ)
    (holdError : ∀ epsilon : RealEuclidean 3,
      (∀ i, 0 < epsilon i) → 0 < oldError epsilon) :
    ∀ {K : ℕ} (old : CharbonnelModulus (K + 1))
      (epsilon : RealEuclidean ((K + 3) + 1)),
      (insertTwoAfterError initialThree oldError holdError old).IsBounded epsilon →
      oldError (wilkieAffineSliceFirstThree epsilon) < old.firstBound →
      old.IsBounded (wilkieAffineSliceOldPrefix oldError epsilon) := by
  intro K
  induction K with
  | zero =>
      intro old epsilon hbounded hfirst
      cases old with
      | step initial lastBound hlast =>
          cases initial with
          | base bound hbound =>
              refine ⟨?_, hbounded.2.1, ?_⟩
              · exact ⟨holdError _ (fun i ↦
                    IsBounded.coord_pos hbounded ⟨i.val, by omega⟩),
                  hfirst⟩
              · rw [wilkieAffineSliceOldPrefix_last,
                  ← wilkieAffineSliceOldPrefix_init]
                exact hbounded.2.2
  | succ K ih =>
      intro old epsilon hbounded hfirst
      cases old with
      | step initial lastBound hlast =>
          refine ⟨?_, ?_, ?_⟩
          · rw [← wilkieAffineSliceOldPrefix_init]
            apply ih initial (Fin.init epsilon) hbounded.1
            rw [wilkieAffineSliceFirstThree_init]
            simpa only [firstBound] using hfirst
          · simpa only [wilkieAffineSliceOldPrefix_last] using hbounded.2.1
          · simpa only [insertTwoAfterError,
              wilkieAffineSliceOldPrefix_init,
              wilkieAffineSliceOldPrefix_last] using hbounded.2.2

/-- Boundedness for the spliced modulus retains boundedness of its initial
three-coordinate modulus. -/
theorem isBounded_insertTwoAfterError_firstThree
    (initialThree : CharbonnelModulus 2)
    (oldError : RealEuclidean 3 → ℝ)
    (holdError : ∀ epsilon : RealEuclidean 3,
      (∀ i, 0 < epsilon i) → 0 < oldError epsilon) :
    ∀ {K : ℕ} (old : CharbonnelModulus (K + 1))
      (epsilon : RealEuclidean ((K + 3) + 1)),
      (insertTwoAfterError initialThree oldError holdError old).IsBounded
        epsilon →
      initialThree.IsBounded (wilkieAffineSliceFirstThree epsilon) := by
  intro K
  induction K with
  | zero =>
      intro old epsilon hbounded
      cases old with
      | step initial lastBound hlast =>
          cases initial with
          | base bound hbound =>
              have hprefix := hbounded.1
              change initialThree.IsBounded (Fin.init epsilon) at hprefix
              convert hprefix using 1
              funext i
              rfl
  | succ K ih =>
      intro old epsilon hbounded
      cases old with
      | step initial lastBound hlast =>
          have hprefix := ih initial (Fin.init epsilon) hbounded.1
          simpa only [wilkieAffineSliceFirstThree_init] using hprefix

end CharbonnelModulus

/-! ## Quantitative bounds used by the frontier-trace modulus -/

/-- The radial-level bound ensuring that a displacement of size less than
`delta` from the `delta⁻¹` ball remains inside the radial section. -/
noncomputable def wilkieAffineSliceRadialBound
    (n : ℕ) (delta : ℝ) : ℝ :=
  if hdelta : 0 < delta then
    Classical.choose (exists_literalZeroRadial_first_level_bound n hdelta)
  else 1

theorem wilkieAffineSliceRadialBound_pos
    (n : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    0 < wilkieAffineSliceRadialBound n delta := by
  rw [wilkieAffineSliceRadialBound, dif_pos hdelta]
  exact (Classical.choose_spec
    (exists_literalZeroRadial_first_level_bound n hdelta)).1

theorem wilkieAffineSliceRadialBound_spec
    (n : ℕ) {delta radial : ℝ}
    (hdelta : 0 < delta) (hradial : 0 < radial)
    (hradialBound : radial < wilkieAffineSliceRadialBound n delta)
    (x y : RealEuclidean n)
    (hxnorm : ‖x‖ < delta⁻¹) (hxy : dist x y < delta) :
    literalZeroVisibleRadialDenominator y < radial⁻¹ := by
  have hspec := (Classical.choose_spec
    (exists_literalZeroRadial_first_level_bound n hdelta)).2
      (ε₁ := radial)
  apply hspec hradial
  · simpa only [wilkieAffineSliceRadialBound, dif_pos hdelta]
      using hradialBound
  · exact hxnorm
  · exact hxy

private theorem exists_wilkieAffineSliceBelowBounds
    {n : ℕ} (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    {delta radial : ℝ} (hdelta : 0 < delta) (hradial : 0 < radial) :
    ∃ bounds : ℝ × ℝ,
      0 < bounds.1 ∧ 0 < bounds.2 ∧
        ∀ x : RealEuclidean n,
          literalZeroVisibleRadialDenominator x ≤ radial⁻¹ →
          (∃ y ∈ A, dist x y < bounds.1) →
          (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ bounds.2 →
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta := by
  obtain ⟨etaOld, etaSlice, hetaOld, hetaSlice, hcontrol⟩ :=
    exists_compactRadial_integerAffineSlice_below_scales
      A hA coeff constant radial hradial hdelta
  exact ⟨(etaOld, etaSlice), hetaOld, hetaSlice, hcontrol⟩

/-- The old-error and slice-level scales selected by compactness for the
given new error and radial level. -/
noncomputable def wilkieAffineSliceBelowBounds
    {n : ℕ} (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (delta radial : ℝ) : ℝ × ℝ :=
  if h : 0 < delta ∧ 0 < radial then
    Classical.choose
      (exists_wilkieAffineSliceBelowBounds
        A hA coeff constant h.1 h.2)
  else (1, 1)

theorem wilkieAffineSliceBelowBounds_spec
    {n : ℕ} (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    {delta radial : ℝ} (hdelta : 0 < delta) (hradial : 0 < radial) :
    0 < (wilkieAffineSliceBelowBounds
        A hA coeff constant delta radial).1 ∧
      0 < (wilkieAffineSliceBelowBounds
        A hA coeff constant delta radial).2 ∧
      ∀ x : RealEuclidean n,
        literalZeroVisibleRadialDenominator x ≤ radial⁻¹ →
        (∃ y ∈ A, dist x y <
          (wilkieAffineSliceBelowBounds
            A hA coeff constant delta radial).1) →
        (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤
          (wilkieAffineSliceBelowBounds
            A hA coeff constant delta radial).2 →
          ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
            dist x z < delta := by
  rw [wilkieAffineSliceBelowBounds, dif_pos ⟨hdelta, hradial⟩]
  exact Classical.choose_spec
    (exists_wilkieAffineSliceBelowBounds
      A hA coeff constant hdelta hradial)

/-- The initial modulus controls the new approximation error, radial level,
and affine-slice level. -/
noncomputable def wilkieAffineSliceInitialModulus
    {n : ℕ} (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ) : CharbonnelModulus 2 :=
  .step
    (.step (.base 1 zero_lt_one)
      (fun epsilon : RealEuclidean 1 ↦
        wilkieAffineSliceRadialBound n (epsilon 0))
      (fun epsilon hpositive ↦
        wilkieAffineSliceRadialBound_pos n (hpositive 0)))
    (fun epsilon : RealEuclidean 2 ↦
      (wilkieAffineSliceBelowBounds A hA coeff constant
        (epsilon 0) (epsilon 1)).2)
    (fun epsilon hpositive ↦
      (wilkieAffineSliceBelowBounds_spec A hA coeff constant
        (hpositive 0) (hpositive 1)).2.1)

/-- Reconstructed old approximation error.  It is simultaneously below the
old modulus's first bound, the compact-intersection old-error scale, the new
error, and the affine-level error cap. -/
noncomputable def wilkieAffineSliceOldError
    {K n : ℕ} (old : CharbonnelModulus (K + 1))
    (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (epsilon : RealEuclidean 3) : ℝ :=
  min (old.firstBound / 2)
    (min ((wilkieAffineSliceBelowBounds A hA coeff constant
        (epsilon 0) (epsilon 1)).1 / 2)
      (min (epsilon 0 / 2)
        (integerAffineSliceErrorCap coeff (epsilon 2) / 2)))

theorem wilkieAffineSliceOldError_pos
    {K n : ℕ} (old : CharbonnelModulus (K + 1))
    (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (epsilon : RealEuclidean 3) (hpositive : ∀ i, 0 < epsilon i) :
    0 < wilkieAffineSliceOldError old A hA coeff constant epsilon := by
  have hbelow := wilkieAffineSliceBelowBounds_spec A hA coeff constant
    (hpositive 0) (hpositive 1)
  unfold wilkieAffineSliceOldError
  have hfirst : 0 < old.firstBound / 2 :=
    div_pos old.firstBound_pos (by norm_num)
  have hbelowOld :
      0 < (wilkieAffineSliceBelowBounds A hA coeff constant
        (epsilon 0) (epsilon 1)).1 / 2 :=
    div_pos hbelow.1 (by norm_num)
  have hdelta : 0 < epsilon 0 / 2 :=
    div_pos (hpositive 0) (by norm_num)
  have hcap :
      0 < integerAffineSliceErrorCap coeff (epsilon 2) / 2 :=
    div_pos (integerAffineSliceErrorCap_pos coeff (hpositive 2))
      (by norm_num)
  exact lt_min hfirst (lt_min hbelowOld (lt_min hdelta hcap))

/-- The complete nested modulus for the lifted affine-slice family. -/
noncomputable def wilkieAffineSliceFrontierModulus
    {K n : ℕ} (old : CharbonnelModulus (K + 1))
    (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    CharbonnelModulus (K + 3) :=
  CharbonnelModulus.insertTwoAfterError
    (wilkieAffineSliceInitialModulus A hA coeff constant)
    (wilkieAffineSliceOldError old A hA coeff constant)
    (wilkieAffineSliceOldError_pos old A hA coeff constant)
    old

/-! ## Coordinate consequences of the spliced modulus -/

@[simp]
theorem parameterTail_wilkieAffineSliceOldPrefix
    {K : ℕ} (oldError : RealEuclidean 3 → ℝ)
    (epsilon : RealEuclidean ((K + 3) + 1)) :
    CharbonnelModulus.parameterTail epsilon =
      wilkiePrependTwoParameters (epsilon 1) (epsilon 2)
        (CharbonnelModulus.parameterTail
          (wilkieAffineSliceOldPrefix oldError epsilon)) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · rfl

/-- The reconstructed old error is strictly below every quantitative cap
used in the two approximation directions. -/
theorem wilkieAffineSliceOldError_lt_bounds
    {K n : ℕ} (old : CharbonnelModulus (K + 1))
    (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (epsilon : RealEuclidean 3) (hpositive : ∀ i, 0 < epsilon i) :
    wilkieAffineSliceOldError old A hA coeff constant epsilon <
        old.firstBound ∧
      wilkieAffineSliceOldError old A hA coeff constant epsilon <
        (wilkieAffineSliceBelowBounds A hA coeff constant
          (epsilon 0) (epsilon 1)).1 ∧
      wilkieAffineSliceOldError old A hA coeff constant epsilon <
        epsilon 0 ∧
      wilkieAffineSliceOldError old A hA coeff constant epsilon <
        integerAffineSliceErrorCap coeff (epsilon 2) := by
  have hbelow := wilkieAffineSliceBelowBounds_spec A hA coeff constant
    (hpositive 0) (hpositive 1)
  unfold wilkieAffineSliceOldError
  constructor
  · calc
      min (old.firstBound / 2)
          (min ((wilkieAffineSliceBelowBounds A hA coeff constant
              (epsilon 0) (epsilon 1)).1 / 2)
            (min (epsilon 0 / 2)
              (integerAffineSliceErrorCap coeff (epsilon 2) / 2))) ≤
          old.firstBound / 2 := min_le_left _ _
      _ < old.firstBound := by linarith [old.firstBound_pos]
  constructor
  · calc
      min (old.firstBound / 2)
          (min ((wilkieAffineSliceBelowBounds A hA coeff constant
              (epsilon 0) (epsilon 1)).1 / 2)
            (min (epsilon 0 / 2)
              (integerAffineSliceErrorCap coeff (epsilon 2) / 2))) ≤
          (wilkieAffineSliceBelowBounds A hA coeff constant
            (epsilon 0) (epsilon 1)).1 / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      _ < (wilkieAffineSliceBelowBounds A hA coeff constant
          (epsilon 0) (epsilon 1)).1 := by linarith [hbelow.1]
  constructor
  · calc
      min (old.firstBound / 2)
          (min ((wilkieAffineSliceBelowBounds A hA coeff constant
              (epsilon 0) (epsilon 1)).1 / 2)
            (min (epsilon 0 / 2)
              (integerAffineSliceErrorCap coeff (epsilon 2) / 2))) ≤
          epsilon 0 / 2 :=
        le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))
      _ < epsilon 0 := by linarith [hpositive 0]
  · calc
      min (old.firstBound / 2)
          (min ((wilkieAffineSliceBelowBounds A hA coeff constant
              (epsilon 0) (epsilon 1)).1 / 2)
            (min (epsilon 0 / 2)
              (integerAffineSliceErrorCap coeff (epsilon 2) / 2))) ≤
          integerAffineSliceErrorCap coeff (epsilon 2) / 2 :=
        le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _))
      _ < integerAffineSliceErrorCap coeff (epsilon 2) := by
        linarith [integerAffineSliceErrorCap_pos coeff (hpositive 2)]

/-- Boundedness for the full modulus exposes the positivity and three
quantitative bounds on its leading error, radial, and affine-level
coordinates. -/
theorem isBounded_wilkieAffineSliceFrontierModulus_firstThree
    {K n : ℕ} (old : CharbonnelModulus (K + 1))
    (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (epsilon : RealEuclidean ((K + 3) + 1))
    (hbounded :
      (wilkieAffineSliceFrontierModulus old A hA coeff constant).IsBounded
        epsilon) :
    0 < epsilon 0 ∧ epsilon 0 < 1 ∧
      0 < epsilon 1 ∧
        epsilon 1 < wilkieAffineSliceRadialBound n (epsilon 0) ∧
      0 < epsilon 2 ∧
        epsilon 2 < (wilkieAffineSliceBelowBounds A hA coeff constant
          (epsilon 0) (epsilon 1)).2 := by
  have hfirst :=
    CharbonnelModulus.isBounded_insertTwoAfterError_firstThree
      (wilkieAffineSliceInitialModulus A hA coeff constant)
      (wilkieAffineSliceOldError old A hA coeff constant)
      (wilkieAffineSliceOldError_pos old A hA coeff constant)
      old epsilon hbounded
  change
    ((CharbonnelModulus.base 1 zero_lt_one).IsBounded
          (Fin.init (Fin.init (wilkieAffineSliceFirstThree epsilon))) ∧
        0 < (Fin.init (wilkieAffineSliceFirstThree epsilon))
          (Fin.last 1) ∧
        (Fin.init (wilkieAffineSliceFirstThree epsilon)) (Fin.last 1) <
          wilkieAffineSliceRadialBound n
            ((Fin.init (Fin.init
              (wilkieAffineSliceFirstThree epsilon))) 0)) ∧
      0 < (wilkieAffineSliceFirstThree epsilon) (Fin.last 2) ∧
      (wilkieAffineSliceFirstThree epsilon) (Fin.last 2) <
        (wilkieAffineSliceBelowBounds A hA coeff constant
          ((Fin.init (wilkieAffineSliceFirstThree epsilon)) 0)
          ((Fin.init (wilkieAffineSliceFirstThree epsilon)) 1)).2 at hfirst
  rcases hfirst with ⟨⟨⟨h0pos, h0lt⟩, h1pos, h1lt⟩, h2pos, h2lt⟩
  exact ⟨h0pos, h0lt, h1pos, h1lt, h2pos, h2lt⟩

/-! ## The exact one-hyperplane frontier-trace approximation -/

/-- If a closed-base trace on one integer-affine hyperplane is exactly a
frontier trace, then the Wilkie affine-slice lift of an old Sardian family
approximates that trace.  Both approximation directions are inherited from
the old certificate: compact radial control gives the from-below direction,
while the old boundary approximation, radial padding, and affine Lipschitz
cap give the from-above direction. -/
theorem isClosureBoundaryApproximation_wilkieAffineSliceLift_of_frontierTrace
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily G order n K)
    (old : CharbonnelModulus (K + 1))
    {S : Set (RealEuclidean n)}
    (hold : CharbonnelModulus.IsClosureBoundaryApproximation
      old family.carrier S)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (htrace :
      closure S ∩ integerAffineSliceHyperplane coeff constant =
        frontier (closure S) ∩
          integerAffineSliceHyperplane coeff constant) :
    CharbonnelModulus.IsClosureBoundaryApproximation
      (wilkieAffineSliceFrontierModulus
        old (closure S) isClosed_closure coeff constant)
      (family.wilkieAffineSliceLift hG hsmooth coeff constant).carrier
      (closure S ∩ integerAffineSliceHyperplane coeff constant) := by
  let H := integerAffineSliceHyperplane coeff constant
  have htargetClosed : IsClosed (closure S ∩ H) :=
    isClosed_closure.inter
      (isClosed_integerAffineSliceHyperplane coeff constant)
  apply (CharbonnelModulus.isClosureBoundaryApproximation_iff_of_isClosed
    htargetClosed).2
  constructor
  · intro epsilon hbounded x hxNew
    have hfirst :=
      isBounded_wilkieAffineSliceFrontierModulus_firstThree
        old (closure S) isClosed_closure coeff constant epsilon hbounded
    rcases hfirst with
      ⟨hdelta, _hdeltaOne, hradial, hradialBound,
        hslice, hsliceBound⟩
    have hpositive : ∀ i, 0 < epsilon i := hbounded.coord_pos
    have hpositiveThree :
        ∀ i, 0 < wilkieAffineSliceFirstThree epsilon i := by
      intro i
      exact hpositive ⟨i.val, by omega⟩
    let oldError := wilkieAffineSliceOldError
      old (closure S) isClosed_closure coeff constant
    let oldEpsilon := wilkieAffineSliceOldPrefix oldError epsilon
    have herrorPos :
        0 < oldError (wilkieAffineSliceFirstThree epsilon) :=
      wilkieAffineSliceOldError_pos old (closure S) isClosed_closure
        coeff constant (wilkieAffineSliceFirstThree epsilon) hpositiveThree
    have herrorBounds :=
      wilkieAffineSliceOldError_lt_bounds
        old (closure S) isClosed_closure coeff constant
        (wilkieAffineSliceFirstThree epsilon) hpositiveThree
    have holdBounded : old.IsBounded oldEpsilon := by
      apply CharbonnelModulus.isBounded_insertTwoAfterError_oldPrefix
        (wilkieAffineSliceInitialModulus
          (closure S) isClosed_closure coeff constant)
        oldError
        (wilkieAffineSliceOldError_pos
          old (closure S) isClosed_closure coeff constant)
        old epsilon hbounded
      exact herrorBounds.1
    have hxNew' :
        realEuclideanAppend x
            (wilkiePrependTwoParameters (epsilon 1) (epsilon 2)
              (CharbonnelModulus.parameterTail oldEpsilon)) ∈
          (family.wilkieAffineSliceLift
            hG hsmooth coeff constant).carrier := by
      rw [← parameterTail_wilkieAffineSliceOldPrefix oldError epsilon]
      exact hxNew
    have hsection := wilkieAffineSliceFiniteFamily_section_lifts_old
      hG hsmooth coeff constant family x (epsilon 1) (epsilon 2)
      (CharbonnelModulus.parameterTail oldEpsilon) hxNew'
    obtain ⟨y, hyS, hxy⟩ :=
      hold.approximatesFromBelow oldEpsilon holdBounded x hsection.2.2.1
    have hxyOld :
        dist x y < oldError (wilkieAffineSliceFirstThree epsilon) := by
      simpa only [oldEpsilon, wilkieAffineSliceOldPrefix_zero] using hxy
    have hbelow := wilkieAffineSliceBelowBounds_spec
      (closure S) isClosed_closure coeff constant hdelta hradial
    exact hbelow.2.2 x hsection.2.2.2.1
      ⟨y, hyS, hxyOld.trans herrorBounds.2.1⟩
      (hsection.2.2.2.2.trans hsliceBound.le)
  · intro epsilon hbounded x hxFrontier hxnorm
    have hfirst :=
      isBounded_wilkieAffineSliceFrontierModulus_firstThree
        old (closure S) isClosed_closure coeff constant epsilon hbounded
    rcases hfirst with
      ⟨hdelta, _hdeltaOne, hradial, hradialBound,
        hslice, _hsliceBound⟩
    have hpositive : ∀ i, 0 < epsilon i := hbounded.coord_pos
    have hpositiveThree :
        ∀ i, 0 < wilkieAffineSliceFirstThree epsilon i := by
      intro i
      exact hpositive ⟨i.val, by omega⟩
    let oldError := wilkieAffineSliceOldError
      old (closure S) isClosed_closure coeff constant
    let oldEpsilon := wilkieAffineSliceOldPrefix oldError epsilon
    have herrorPos :
        0 < oldError (wilkieAffineSliceFirstThree epsilon) :=
      wilkieAffineSliceOldError_pos old (closure S) isClosed_closure
        coeff constant (wilkieAffineSliceFirstThree epsilon) hpositiveThree
    have herrorBounds :=
      wilkieAffineSliceOldError_lt_bounds
        old (closure S) isClosed_closure coeff constant
        (wilkieAffineSliceFirstThree epsilon) hpositiveThree
    have holdBounded : old.IsBounded oldEpsilon := by
      apply CharbonnelModulus.isBounded_insertTwoAfterError_oldPrefix
        (wilkieAffineSliceInitialModulus
          (closure S) isClosed_closure coeff constant)
        oldError
        (wilkieAffineSliceOldError_pos
          old (closure S) isClosed_closure coeff constant)
        old epsilon hbounded
      exact herrorBounds.1
    have hxTarget : x ∈ closure S ∩ H :=
      htargetClosed.frontier_subset hxFrontier
    have hxOldTrace :
        x ∈ frontier (closure S) ∩ H := by
      rw [← htrace]
      exact hxTarget
    have hnormOld : ‖x‖ < (oldEpsilon 0)⁻¹ := by
      have hinv :
          (epsilon 0)⁻¹ <
            (oldError (wilkieAffineSliceFirstThree epsilon))⁻¹ :=
        (inv_lt_inv₀ hdelta herrorPos).2 herrorBounds.2.2.1
      simpa only [oldEpsilon, wilkieAffineSliceOldPrefix_zero] using
        hxnorm.trans hinv
    obtain ⟨y, hxy, hyOld⟩ :=
      hold.approximatesBoundaryFromAbove oldEpsilon holdBounded
        x hxOldTrace.1 hnormOld
    have hxyOld :
        dist x y < oldError (wilkieAffineSliceFirstThree epsilon) := by
      simpa only [oldEpsilon, wilkieAffineSliceOldPrefix_zero] using hxy
    have hxyDelta : dist x y < epsilon 0 :=
      hxyOld.trans herrorBounds.2.2.1
    have hyradial :
        literalZeroVisibleRadialDenominator y ≤ (epsilon 1)⁻¹ :=
      (wilkieAffineSliceRadialBound_spec n hdelta hradial hradialBound
        x y hxnorm hxyDelta).le
    have hylevel :
        (integerAffineSliceLinearForm coeff constant y) ^ 2 ≤ epsilon 2 :=
      integerAffineSlice_sq_le_of_dist_lt_errorCap coeff constant hslice
        hxTarget.2 (hxyOld.trans herrorBounds.2.2.2)
    have hyNew := mem_wilkieAffineSliceFiniteFamily_of_old_section
      hG hsmooth coeff constant family y (epsilon 1) (epsilon 2)
      (CharbonnelModulus.parameterTail oldEpsilon)
      hradial hslice hyOld hyradial hylevel
    refine ⟨y, hxyDelta, ?_⟩
    rw [parameterTail_wilkieAffineSliceOldPrefix oldError epsilon]
    exact hyNew

/-- Certificate-level packaging of the exact frontier-trace lift. -/
noncomputable def wilkieAffineSliceFrontierTraceCertificate
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {S : Set (RealEuclidean n)}
    (old : CharbonnelSardianApproximationCertificate G order n S)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (htrace :
      closure S ∩ integerAffineSliceHyperplane coeff constant =
        frontier (closure S) ∩
          integerAffineSliceHyperplane coeff constant) :
    CharbonnelSardianApproximationCertificate G order n
      (closure S ∩ integerAffineSliceHyperplane coeff constant) := by
  exact
    { order_pos := old.order_pos
      commonHiddenArity := old.commonHiddenArity + 2
      family := old.family.wilkieAffineSliceLift
        hG hsmooth coeff constant
      modulus := wilkieAffineSliceFrontierModulus old.modulus
        (closure S) isClosed_closure coeff constant
      approximates :=
        isClosureBoundaryApproximation_wilkieAffineSliceLift_of_frontierTrace
          hG hsmooth old.family old.modulus old.approximates
          coeff constant htrace }

/-- The positive sign-cell trace has a Sardian approximation certificate
obtained automatically from a certificate for the sign cell itself. -/
noncomputable def positiveIntegerAffineFrontierTraceCertificate
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} (B : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    (old : CharbonnelSardianApproximationCertificate G order n
      (B ∩ integerAffineSlicePositiveSide coeff constant)) :
    CharbonnelSardianApproximationCertificate G order n
      (closure (B ∩ integerAffineSlicePositiveSide coeff constant) ∩
        integerAffineSliceHyperplane coeff constant) :=
  wilkieAffineSliceFrontierTraceCertificate hG hsmooth old coeff constant
    (oneSidedIntegerAffineClosure_frontier_traces
      B coeff constant hnonzero).1

/-- The negative sign-cell trace has a Sardian approximation certificate
obtained automatically from a certificate for the sign cell itself. -/
noncomputable def negativeIntegerAffineFrontierTraceCertificate
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} (B : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    (old : CharbonnelSardianApproximationCertificate G order n
      (B ∩ integerAffineSliceNegativeSide coeff constant)) :
    CharbonnelSardianApproximationCertificate G order n
      (closure (B ∩ integerAffineSliceNegativeSide coeff constant) ∩
        integerAffineSliceHyperplane coeff constant) :=
  wilkieAffineSliceFrontierTraceCertificate hG hsmooth old coeff constant
    (oneSidedIntegerAffineClosure_frontier_traces
      B coeff constant hnonzero).2

end AbelFormalization
