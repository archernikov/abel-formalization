import AbelFormalization.CharbonnelClosureComponentBound
import AbelFormalization.MaxwellCompactComponentSeparation
import AbelFormalization.SquaredDistanceProper

/-!
# The geometric Maxwell comparison for Charbonnel closure nodes

This file specializes `MaxwellCompactComponentSeparation` to the universal
semialgebraic thickening constructed in `CharbonnelClosureComponentBound`.
For fixed affine-system, radius, and defect parameters, concatenation with
the parameter tuple identifies a strict tube in the visible variables with
an affine section of the Maxwell replacement carrier.  The generic compact
separation theorem then transfers one uniform affine-section component bound
from the replacement carrier to `closure B`.

The last theorem combines this geometric comparison with
`exists_maxwellClosureReplacement`.  It is exactly the topological-closure
constructor step in the rank induction for WS5.  No complement closure is
asserted here.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## The visible radius and affine defect -/

/-- The squared-coordinate radius occurring in Maxwell's ball inequality. -/
def maxwellVisibleNormSqValue {n : ℕ} (x : RealEuclidean n) : ℝ :=
  ∑ i : Fin n, (x i) ^ 2

theorem maxwellVisibleNormSqValue_nonneg {n : ℕ}
    (x : RealEuclidean n) :
    0 ≤ maxwellVisibleNormSqValue x := by
  exact Finset.sum_nonneg fun i _hi ↦ sq_nonneg (x i)

theorem continuous_maxwellVisibleNormSqValue {n : ℕ} :
    Continuous (@maxwellVisibleNormSqValue n) := by
  exact continuous_finsetSum Finset.univ fun i _hi ↦
    (continuous_apply i).pow 2

/-- Every sublevel of the visible squared-coordinate radius is compact. -/
theorem isCompact_maxwellVisibleNormSqValue_sublevel
    {n : ℕ} (R : ℝ) :
    IsCompact {x : RealEuclidean n | maxwellVisibleNormSqValue x ≤ R} := by
  simpa [maxwellVisibleNormSqValue, algebraicSquaredDistance_apply] using
    (isCompact_algebraicSquaredDistance_basis_sublevel
      (E := RealEuclidean n) (Pi.basisFun ℝ (Fin n))
      (0 : Fin n → ℝ) R)

/-- The nonnegative sum of squares measuring failure of `Mx = b`. -/
def maxwellAffineDefect {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (x : RealEuclidean n) : ℝ :=
  ∑ i : Fin n, (flatSquareMatrixMulVec M x i - b i) ^ 2

theorem maxwellAffineDefect_nonneg {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (x : RealEuclidean n) :
    0 ≤ maxwellAffineDefect M b x := by
  exact Finset.sum_nonneg fun i _hi ↦
    sq_nonneg (flatSquareMatrixMulVec M x i - b i)

theorem continuous_maxwellAffineDefect {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n) :
    Continuous (maxwellAffineDefect M b) := by
  unfold maxwellAffineDefect flatSquareMatrixMulVec
  exact continuous_finsetSum Finset.univ fun i _hi ↦
    ((continuous_finsetSum Finset.univ fun j _hj ↦
      continuous_const.mul (continuous_apply j)).sub continuous_const).pow 2

@[simp]
theorem maxwellAffineDefect_eq_zero_iff {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (x : RealEuclidean n) :
    maxwellAffineDefect M b x = 0 ↔
      flatSquareMatrixMulVec M x = b := by
  rw [maxwellAffineDefect, Finset.sum_sq_eq_zero_iff]
  constructor
  · intro h
    funext i
    exact sub_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _hi
    exact sub_eq_zero.mpr (congrFun h i)

@[simp]
theorem abs_maxwellAffineDefect {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (x : RealEuclidean n) :
    |maxwellAffineDefect M b x| = maxwellAffineDefect M b x :=
  abs_of_nonneg (maxwellAffineDefect_nonneg M b x)

/-! ## Evaluation of the universal thickening -/

@[simp]
theorem maxwellRadiusIndex_append
    {n : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean 2) :
    (realEuclideanAppend x
      (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellRadiusIndex n) = t 0 := by
  simp [maxwellRadiusIndex, maxwellAffineParameterCount]

@[simp]
theorem maxwellEpsilonIndex_append
    {n : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean 2) :
    (realEuclideanAppend x
      (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellEpsilonIndex n) = t 1 := by
  simp [maxwellEpsilonIndex, maxwellAffineParameterCount]

@[simp]
theorem maxwellVisibleNormSqPolynomial_eval_append
    {n : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean 2) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellVisibleNormSqPolynomial n) =
      maxwellVisibleNormSqValue x := by
  classical
  change (MvPolynomial.eval
      (realEuclideanAppend x
        (realEuclideanAppend (realEuclideanAppend M b) t)))
      (∑ j : Fin n, MvPolynomial.X (maxwellAffineXIndex n 2 j) ^ 2) =
        ∑ j : Fin n, (x j) ^ 2
  rw [map_sum]
  simp only [MvPolynomial.eval_pow, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [maxwellAffineXIndex]

@[simp]
theorem maxwellThickeningUpperPolynomial_eval_append
    {n : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean 2) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellThickeningUpperPolynomial n) =
      (t 1) ^ 2 - maxwellAffineDefect M b x := by
  rw [maxwellThickeningUpperPolynomial, map_sub,
    MvPolynomial.eval_pow, MvPolynomial.eval_X,
    maxwellEpsilonIndex_append,
    maxwellUniversalAffinePolynomial_eval_append]
  rfl

@[simp]
theorem maxwellThickeningLowerPolynomial_eval_append
    {n : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean 2) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellThickeningLowerPolynomial n) =
      (t 1) ^ 2 + maxwellAffineDefect M b x := by
  rw [maxwellThickeningLowerPolynomial, map_add,
    MvPolynomial.eval_pow, MvPolynomial.eval_X,
    maxwellEpsilonIndex_append,
    maxwellUniversalAffinePolynomial_eval_append]
  rfl

@[simp]
theorem maxwellThickeningBallPolynomial_eval_append
    {n : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean 2) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellThickeningBallPolynomial n) =
      (t 0) ^ 2 - maxwellVisibleNormSqValue x := by
  rw [maxwellThickeningBallPolynomial, map_sub,
    MvPolynomial.eval_pow, MvPolynomial.eval_X,
    maxwellRadiusIndex_append,
    maxwellVisibleNormSqPolynomial_eval_append]

/-- The fixed parameter tuple `(M,b,√R,√ε)` used to realize one strict
tube as an affine section of the universal replacement. -/
def maxwellFixedTubeParameters {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (R ε : ℝ) :
    RealEuclidean (maxwellAffineParameterCount n + 2) :=
  realEuclideanAppend (realEuclideanAppend M b)
    ![Real.sqrt R, Real.sqrt ε]

theorem maxwellFixed_append_mem_thickening_iff
    {n : ℕ} (M : FlatSquareMatrix n) (b : RealEuclidean n)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x : RealEuclidean n) :
    realEuclideanAppend x (maxwellFixedTubeParameters M b R ε) ∈
        maxwellThickening n ↔
      maxwellVisibleNormSqValue x < R ∧
        |maxwellAffineDefect M b x| < ε := by
  have hdefect := maxwellAffineDefect_nonneg M b x
  have hsqrtR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.le
  have hsqrtε : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  simp only [maxwellThickening, Set.mem_inter_iff, Set.mem_setOf_eq,
    maxwellFixedTubeParameters,
    maxwellThickeningUpperPolynomial_eval_append,
    maxwellThickeningLowerPolynomial_eval_append,
    maxwellThickeningBallPolynomial_eval_append,
    Matrix.cons_val_zero, Matrix.cons_val_one, hsqrtR, hsqrtε,
    abs_of_nonneg hdefect]
  constructor
  · rintro ⟨⟨hupper, _hlower⟩, hball⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hball, hupper⟩
    refine ⟨⟨by linarith, ?_⟩, by linarith⟩
    linarith

/-! ## Fixed-parameter affine sections -/

/-- The affine subspace on which the entire Maxwell parameter block is fixed
to `(M,b,√R,√ε)`. -/
def maxwellFixedParameterSlice {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (R ε : ℝ) :
    AffineSubspace ℝ
      (RealEuclidean (n + (maxwellAffineParameterCount n + 2))) :=
  ({maxwellFixedTubeParameters M b R ε} :
      AffineSubspace ℝ
        (RealEuclidean (maxwellAffineParameterCount n + 2))).comap
    (realEuclideanTakeRightLinearMap n
      (maxwellAffineParameterCount n + 2)).toAffineMap

@[simp]
theorem mem_maxwellFixedParameterSlice_iff
    {n : ℕ} (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (R ε : ℝ)
    (v : RealEuclidean (n + (maxwellAffineParameterCount n + 2))) :
    v ∈ maxwellFixedParameterSlice M b R ε ↔
      realEuclideanTakeRight v =
        maxwellFixedTubeParameters M b R ε := by
  simp [maxwellFixedParameterSlice]

/-- The canonical carrier produced by the algebraic Maxwell replacement. -/
def maxwellClosureReplacementCarrier {n : ℕ}
    (B : Set (RealEuclidean n)) :
    Set (RealEuclidean (n + (maxwellAffineParameterCount n + 2))) :=
  realEuclideanSetProduct B Set.univ ∩ maxwellThickening n

/-- One fixed-parameter affine section of the canonical replacement. -/
def maxwellFixedParameterSection {n : ℕ}
    (B : Set (RealEuclidean n))
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (R ε : ℝ) :
    Set (RealEuclidean (n + (maxwellAffineParameterCount n + 2))) :=
  maxwellClosureReplacementCarrier B ∩
    (maxwellFixedParameterSlice M b R ε : Set
      (RealEuclidean (n + (maxwellAffineParameterCount n + 2))))

theorem maxwell_append_mem_fixedParameterSection_iff
    {n : ℕ} (B : Set (RealEuclidean n))
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x : RealEuclidean n) :
    realEuclideanAppend x (maxwellFixedTubeParameters M b R ε) ∈
        maxwellFixedParameterSection B M b R ε ↔
      x ∈ maxwellStrictTube B maxwellVisibleNormSqValue
        (maxwellAffineDefect M b) R ε := by
  constructor
  · rintro ⟨⟨hproduct, hthickening⟩, _hslice⟩
    have hxB : x ∈ B := by
      change
        realEuclideanTakeLeft
            (realEuclideanAppend x
              (maxwellFixedTubeParameters M b R ε)) ∈ B ∧
          realEuclideanTakeRight
            (realEuclideanAppend x
              (maxwellFixedTubeParameters M b R ε)) ∈ Set.univ at hproduct
      simpa only [realEuclideanTakeLeft_append] using hproduct.1
    obtain ⟨hradius, hdefect⟩ :=
      (maxwellFixed_append_mem_thickening_iff M b hR hε x).mp hthickening
    exact mem_maxwellStrictTube.mpr ⟨hxB, hradius, hdefect⟩
  · intro hx
    obtain ⟨hxB, hradius, hdefect⟩ := mem_maxwellStrictTube.mp hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change
        realEuclideanTakeLeft
            (realEuclideanAppend x
              (maxwellFixedTubeParameters M b R ε)) ∈ B ∧
          realEuclideanTakeRight
            (realEuclideanAppend x
              (maxwellFixedTubeParameters M b R ε)) ∈ Set.univ
      exact ⟨by simpa only [realEuclideanTakeLeft_append] using hxB,
        Set.mem_univ _⟩
    · exact
        (maxwellFixed_append_mem_thickening_iff M b hR hε x).mpr
          ⟨hradius, hdefect⟩
    · apply (mem_maxwellFixedParameterSlice_iff M b R ε _).mpr
      exact realEuclideanTakeRight_append x
        (maxwellFixedTubeParameters M b R ε)

theorem maxwell_takeLeft_mem_strictTube_of_mem_fixedParameterSection
    {n : ℕ} {B : Set (RealEuclidean n)}
    {M : FlatSquareMatrix n} {b : RealEuclidean n}
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    {v : RealEuclidean (n + (maxwellAffineParameterCount n + 2))}
    (hv : v ∈ maxwellFixedParameterSection B M b R ε) :
    realEuclideanTakeLeft v ∈
      maxwellStrictTube B maxwellVisibleNormSqValue
        (maxwellAffineDefect M b) R ε := by
  have hright :
      realEuclideanTakeRight v =
        maxwellFixedTubeParameters M b R ε :=
    (mem_maxwellFixedParameterSlice_iff M b R ε v).mp hv.2
  apply
    (maxwell_append_mem_fixedParameterSection_iff
      B M b hR hε (realEuclideanTakeLeft v)).mp
  have hreconstruct :
      realEuclideanAppend (realEuclideanTakeLeft v)
          (maxwellFixedTubeParameters M b R ε) = v := by
    rw [← hright]
    exact realEuclideanAppend_take v
  rwa [hreconstruct]

/-- Exact carrier identity between the fixed affine section and the image of
the corresponding visible strict tube under parameter concatenation. -/
theorem maxwellFixedParameterSection_eq_append_image
    {n : ℕ} (B : Set (RealEuclidean n))
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    maxwellFixedParameterSection B M b R ε =
      (fun x : RealEuclidean n ↦
        realEuclideanAppend x
          (maxwellFixedTubeParameters M b R ε)) ''
        maxwellStrictTube B maxwellVisibleNormSqValue
          (maxwellAffineDefect M b) R ε := by
  ext v
  constructor
  · intro hv
    have hright :
        realEuclideanTakeRight v =
          maxwellFixedTubeParameters M b R ε :=
      (mem_maxwellFixedParameterSlice_iff M b R ε v).mp hv.2
    refine ⟨realEuclideanTakeLeft v,
      maxwell_takeLeft_mem_strictTube_of_mem_fixedParameterSection
        hR hε hv, ?_⟩
    rw [← hright]
    exact realEuclideanAppend_take v
  · rintro ⟨x, hx, rfl⟩
    exact
      (maxwell_append_mem_fixedParameterSection_iff
        B M b hR hε x).mpr hx

/-- Concatenation with the fixed parameter tuple is a homeomorphism from the
strict tube onto the corresponding affine section of the replacement. -/
def maxwellStrictTubeHomeomorphFixedParameterSection
    {n : ℕ} (B : Set (RealEuclidean n))
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    maxwellStrictTube B maxwellVisibleNormSqValue
        (maxwellAffineDefect M b) R ε ≃ₜ
      maxwellFixedParameterSection B M b R ε where
  toFun x :=
    ⟨realEuclideanAppend x
        (maxwellFixedTubeParameters M b R ε),
      (maxwell_append_mem_fixedParameterSection_iff
        B M b hR hε x).mpr x.property⟩
  invFun v :=
    ⟨realEuclideanTakeLeft v,
      maxwell_takeLeft_mem_strictTube_of_mem_fixedParameterSection
        hR hε v.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simpa only using
      (realEuclideanTakeLeft_append (x : RealEuclidean n)
        (maxwellFixedTubeParameters M b R ε))
  right_inv := by
    intro v
    apply Subtype.ext
    have hright :
        realEuclideanTakeRight (v :
            RealEuclidean (n + (maxwellAffineParameterCount n + 2))) =
          maxwellFixedTubeParameters M b R ε :=
      (mem_maxwellFixedParameterSlice_iff M b R ε v).mp v.property.2
    change
      realEuclideanAppend (realEuclideanTakeLeft (v :
          RealEuclidean (n + (maxwellAffineParameterCount n + 2))))
          (maxwellFixedTubeParameters M b R ε) = v
    calc
      _ = realEuclideanAppend (realEuclideanTakeLeft (v :
            RealEuclidean (n + (maxwellAffineParameterCount n + 2))))
          (realEuclideanTakeRight (v :
            RealEuclidean (n + (maxwellAffineParameterCount n + 2)))) := by
        exact congrArg
          (fun z ↦ realEuclideanAppend
            (realEuclideanTakeLeft (v :
              RealEuclidean (n + (maxwellAffineParameterCount n + 2)))) z)
          hright.symm
      _ = v := realEuclideanAppend_take
        (v : RealEuclidean
          (n + (maxwellAffineParameterCount n + 2)))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [realEuclideanAppend_castAdd, Function.comp_def] using
        ((continuous_apply j).comp continuous_subtype_val)
    · simpa only [realEuclideanAppend_natAdd] using
        (continuous_const : Continuous
          (fun _ : maxwellStrictTube B maxwellVisibleNormSqValue
              (maxwellAffineDefect M b) R ε ↦
            maxwellFixedTubeParameters M b R ε j))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      (realEuclideanTakeLeftContinuousLinearMap n
          (maxwellAffineParameterCount n + 2)).continuous.comp
        continuous_subtype_val

theorem enatCard_connectedComponents_maxwellStrictTube_eq_fixedParameterSection
    {n : ℕ} (B : Set (RealEuclidean n))
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ENat.card (ConnectedComponents
      (maxwellStrictTube B maxwellVisibleNormSqValue
        (maxwellAffineDefect M b) R ε)) =
      ENat.card (ConnectedComponents
        (maxwellFixedParameterSection B M b R ε)) := by
  let e :=
    maxwellStrictTubeHomeomorphFixedParameterSection B M b hR hε
  apply le_antisymm
  · exact enatCard_connectedComponents_le_of_continuous_surjective
      e.symm.continuous e.symm.surjective
  · exact enatCard_connectedComponents_le_of_continuous_surjective
      e.continuous e.surjective

/-! ## The closure comparison -/

theorem maxwellLimitFiber_affineDefect
    {n : ℕ} (B : Set (RealEuclidean n))
    (M : FlatSquareMatrix n) (b : RealEuclidean n) :
    maxwellLimitFiber B (maxwellAffineDefect M b) =
      closure B ∩ {x | flatSquareMatrixMulVec M x = b} := by
  ext x
  simp only [mem_maxwellLimitFiber, Set.mem_inter_iff, Set.mem_setOf_eq,
    maxwellAffineDefect_eq_zero_iff]

/--
The geometric part of Maxwell's closure comparison.  A uniform bound for
affine sections of the single canonical replacement carrier bounds every
affine section of `closure B`.
-/
theorem enatCard_connectedComponents_closure_affineSection_le_of_maxwellReplacement
    {n : ℕ} (hn : 0 < n) (B : Set (RealEuclidean n)) (N : ℕ)
    (hreplacement :
      ∀ W : AffineSubspace ℝ
          (RealEuclidean (n + (maxwellAffineParameterCount n + 2))),
        ENat.card (ConnectedComponents
          ((maxwellClosureReplacementCarrier B ∩
              (W : Set
                (RealEuclidean
                  (n + (maxwellAffineParameterCount n + 2))))) :
            Set (RealEuclidean
              (n + (maxwellAffineParameterCount n + 2))))) ≤ (N : ℕ∞)) :
    ∀ V : AffineSubspace ℝ (RealEuclidean n),
      ENat.card (ConnectedComponents
        ((closure B ∩ (V : Set (RealEuclidean n))) :
          Set (RealEuclidean n))) ≤ (N : ℕ∞) := by
  intro V
  obtain ⟨M, b, hV⟩ := exists_flatSquareMatrix_eq_affineSubspace hn V
  have hlimit :
      maxwellLimitFiber B (maxwellAffineDefect M b) =
        closure B ∩ (V : Set (RealEuclidean n)) := by
    rw [maxwellLimitFiber_affineDefect, hV]
  rw [← hlimit]
  apply enatCard_connectedComponents_maxwellLimitFiber_le
    B maxwellVisibleNormSqValue (maxwellAffineDefect M b)
    continuous_maxwellVisibleNormSqValue
    (continuous_maxwellAffineDefect M b)
    isCompact_maxwellVisibleNormSqValue_sublevel N
  intro R ε hε
  by_cases hR : 0 < R
  · calc
      ENat.card (ConnectedComponents
          (maxwellStrictTube B maxwellVisibleNormSqValue
            (maxwellAffineDefect M b) R ε)) =
          ENat.card (ConnectedComponents
            (maxwellFixedParameterSection B M b R ε)) :=
        enatCard_connectedComponents_maxwellStrictTube_eq_fixedParameterSection
          B M b hR hε
      _ ≤ (N : ℕ∞) := by
        exact hreplacement (maxwellFixedParameterSlice M b R ε)
  · have hRle : R ≤ 0 := le_of_not_gt hR
    have hTubeEmpty :
        maxwellStrictTube B maxwellVisibleNormSqValue
            (maxwellAffineDefect M b) R ε = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxradius := (mem_maxwellStrictTube.mp hx).2.1
      exact
        (not_lt_of_ge
          (hRle.trans (maxwellVisibleNormSqValue_nonneg x))) hxradius
    letI : IsEmpty
        (maxwellStrictTube B maxwellVisibleNormSqValue
          (maxwellAffineDefect M b) R ε) :=
      Set.isEmpty_coe_sort.mpr hTubeEmpty
    have hcomponents : IsEmpty (ConnectedComponents
        (maxwellStrictTube B maxwellVisibleNormSqValue
          (maxwellAffineDefect M b) R ε)) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
    rw [(ENat.card_eq_zero_iff_empty _).mpr hcomponents]
    exact zero_le

/-! ## The closure-node step in the description-rank induction -/

/-- A description has one uniform component bound over all affine sections. -/
def CharbonnelDescription.HasAffineSectionComponentBound
    {S : EuclideanSetFamily} {n : ℕ}
    (description : CharbonnelDescription S n) : Prop :=
  ∃ N : ℕ, ∀ V : AffineSubspace ℝ (RealEuclidean n),
    ENat.card (ConnectedComponents
      ((description.carrier ∩ (V : Set (RealEuclidean n))) :
        Set (RealEuclidean n))) ≤ (N : ℕ∞)

/--
The exact topological-closure constructor case of the WS5 rank induction.
The algebraic replacement has lower rank, so a lower-rank WS5 hypothesis for
it supplies the tube bound required by the geometric Maxwell comparison.
-/
theorem CharbonnelDescription.hasAffineSectionComponentBound_topologicalClosure
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ}
    (inner : CharbonnelDescription (literalZeroSetFamily G) n)
    (hlower :
      ∀ {m : ℕ}
        (description :
          CharbonnelDescription (literalZeroSetFamily G) m),
        description.rank <
            (CharbonnelDescription.topologicalClosure inner).rank →
          description.HasAffineSectionComponentBound) :
    CharbonnelDescription.HasAffineSectionComponentBound
      (CharbonnelDescription.topologicalClosure inner) := by
  obtain ⟨replacement, hreplacementCarrier, hreplacementRank⟩ :=
    exists_maxwellClosureReplacement hG hsmooth inner
  obtain ⟨N, hN⟩ := hlower replacement hreplacementRank
  refine ⟨N, ?_⟩
  apply
    enatCard_connectedComponents_closure_affineSection_le_of_maxwellReplacement
      inner.positiveArity inner.carrier N
  intro W
  have hcarrier :
      replacement.carrier = maxwellClosureReplacementCarrier inner.carrier := by
    simpa only [maxwellClosureReplacementCarrier] using hreplacementCarrier
  rw [← hcarrier]
  exact hN W

end AbelFormalization
