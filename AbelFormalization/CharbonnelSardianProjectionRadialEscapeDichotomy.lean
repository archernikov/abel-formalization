import AbelFormalization.CharbonnelSardianProjectionBoundaryLocalization
import AbelFormalization.CharbonnelSardianProjectionRadialFiniteCover

/-!
# Bounded fiber or reciprocal-radial escape

In Wilkie 3.10 the old fixed-level fiber over a bounded visible ball has two
possibilities.  If it is bounded, the regular-value Case 2 theorem applies.
If it is unbounded, the hidden block is unbounded and the reciprocal radial
function accumulates at zero.  This file proves that metric dichotomy and
feeds its escape branch to the maintained WS5 radial-level theorem.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A positive lower bound for the reciprocal-radial value bounds the whole
old tuple fiber whenever its visible base is bounded. -/
theorem isBounded_sardianProjectionOldTupleFiber_of_radial_lowerBound
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hU : Bornology.IsBounded U)
    {delta : ℝ} (hdelta : 0 < delta)
    (hlower : ∀ v ∈ sardianProjectionOldTupleFiber old U e,
      delta ≤ sardianProjectionRadialReciprocal n q v) :
    Bornology.IsBounded (sardianProjectionOldTupleFiber old U e) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hU
  let R : ℝ := Real.sqrt (delta⁻¹ - 1)
  let M : ℝ := max (max 0 C) R
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M, ?_⟩
  intro v hv
  have hxNorm : ‖realEuclideanTakeLeft v‖ ≤ C := hC _ hv.1
  have hradial : delta ≤ sardianProjectionRadialReciprocal n q
      (realEuclideanAppend (realEuclideanTakeLeft v)
        (realEuclideanTakeRight v)) := by
    simpa only [realEuclideanAppend_take] using hlower v hv
  have hyNorm : ‖realEuclideanTakeRight v‖ ≤ R := by
    exact sardianProjectionRadialReciprocal_hidden_norm_le
      n q (realEuclideanTakeLeft v) (realEuclideanTakeRight v)
      delta hdelta hradial
  apply (pi_norm_le_iff_of_nonneg ?_).mpr
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · have hcoord : ‖realEuclideanTakeLeft v j‖ ≤
          ‖realEuclideanTakeLeft v‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mp (le_refl _) j
      exact hcoord.trans (hxNorm.trans
        ((le_max_right 0 C).trans (le_max_left (max 0 C) R)))
    · have hcoord : ‖realEuclideanTakeRight v j‖ ≤
          ‖realEuclideanTakeRight v‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mp (le_refl _) j
      exact hcoord.trans (hyNorm.trans (le_max_right (max 0 C) R))
  · exact (le_max_left 0 C).trans (le_max_left (max 0 C) R)

/-- If the old tuple fiber over a bounded visible base is unbounded, zero is
in the closure of its reciprocal-radial range. -/
theorem zero_mem_closure_radialRange_of_not_isBounded_oldTupleFiber
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hU : Bornology.IsBounded U)
    (hunbounded : ¬ Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e)) :
    (0 : ℝ) ∈ closure
      (sardianProjectionRadialReciprocal n q ''
        sardianProjectionOldTupleFiber old U e) := by
  by_contra hzero
  rw [Metric.mem_closure_iff] at hzero
  push Not at hzero
  obtain ⟨delta, hdelta, hlowerDist⟩ := hzero
  apply hunbounded
  apply isBounded_sardianProjectionOldTupleFiber_of_radial_lowerBound
    old U e hU hdelta
  intro v hv
  have hdist := hlowerDist
    (sardianProjectionRadialReciprocal n q v) ⟨v, hv, rfl⟩
  have hpositive : 0 < sardianProjectionRadialReciprocal n q v := by
    change 0 < (sardianProjectionRadialDenominator n q v)⁻¹
    exact inv_pos.mpr (sardianProjectionRadialDenominator_pos n q v)
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpositive] at hdist
  exact hdist

/-- The dichotomy in the form consumed by the projection construction. -/
theorem sardianProjectionOldTupleFiber_bounded_or_zero_mem_radialRange_closure
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (sardianProjectionOldTupleFiber old U e) ∨
      (0 : ℝ) ∈ closure
        (realEuclideanOneCoordinateImage
          (sardianProjectionRadialValueImage old U e)) := by
  by_cases hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e)
  · exact Or.inl hbounded
  · apply Or.inr
    rw [sardianProjectionRadialValueImage_coordinate_eq_image]
    exact zero_mem_closure_radialRange_of_not_isBounded_oldTupleFiber
      old U e hU hbounded

/-- In the unbounded branch, WS5 immediately supplies every sufficiently
small positive projected radial level. -/
theorem exists_small_projected_radial_levels_of_not_isBounded_oldTupleFiber
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hUmem : U ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (hUbounded : Bornology.IsBounded U)
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hunbounded : ¬ Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e)) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : ℝ, 0 < t → t < eta →
        ∃ x ∈ U,
          realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
            (sardianProjectionAlgebraicFamily
              hG hsmooth hderiv hn old).carrier := by
  have hzero : (0 : ℝ) ∈ closure
      (realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old U e)) := by
    rw [sardianProjectionRadialValueImage_coordinate_eq_image]
    exact zero_mem_closure_radialRange_of_not_isBounded_oldTupleFiber
      old U e hUbounded hunbounded
  exact sardianProjectionRadialValueImage_projectedFamily_all_small_levels
    hG hsmooth hderiv hUFF hn old U hUmem e hepos hzero

/-- Once full projection of the localized fiber has been ruled out, the
bounded Case-2 branch and the unbounded reciprocal-radial branch give the
same small-level conclusion.  This is the pointwise form used after taking
a finite minimum of the boundary-separation thresholds. -/
theorem sardianProjection_smallLevels_of_notProjection_bounded_or_radial
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily f) (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hUmem : U ∈ charbonnelClosure
      (literalZeroSetFamily (abelGeometricFamily f)) n)
    (hUbounded : Bornology.IsBounded U)
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hregular : ∀ v, sardianProjectionOldTuple old v = e →
      Function.Surjective
        (fderiv ℝ (sardianProjectionOldTuple old) v))
    (hnonempty : (sardianProjectionOldTupleFiber old U e).Nonempty)
    (hnotProjection :
      realEuclideanTakeLeft ''
        sardianProjectionOldTupleFiber old U e ≠ U) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : ℝ, 0 < t → t < eta →
        ∃ x ∈ U,
          realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
            (sardianProjectionAlgebraicFamily
              hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
              hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
              hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
              hn old).carrier := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  by_cases hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e)
  · rcases sardianProjection_projection_or_smallLevels_of_theorems21_22
        hf hUFF hn old U e hepos h21 h22 hUopen hUconvex
        hregular hbounded hnonempty with
      hprojection | hsmallLevels
    · exact (hnotProjection hprojection).elim
    · exact hsmallLevels
  · exact
      exists_small_projected_radial_levels_of_not_isBounded_oldTupleFiber
        hG hsmooth hderiv hUFF hn old U hUmem hUbounded e hepos hbounded

/-- The same bounded-or-radial dichotomy with direct category weak
selection; Maxwell almost-everywhere smoothness is the only Case 2 input. -/
theorem sardianProjection_smallLevels_of_notProjection_bounded_or_radial_of_MaxwellAlmostEverywhereSmoothness
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily f) (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hUmem : U ∈ charbonnelClosure
      (literalZeroSetFamily (abelGeometricFamily f)) n)
    (hUbounded : Bornology.IsBounded U)
    (hMaxwell : MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hregular : ∀ v, sardianProjectionOldTuple old v = e →
      Function.Surjective
        (fderiv ℝ (sardianProjectionOldTuple old) v))
    (hnonempty : (sardianProjectionOldTupleFiber old U e).Nonempty)
    (hnotProjection :
      realEuclideanTakeLeft ''
        sardianProjectionOldTupleFiber old U e ≠ U) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : ℝ, 0 < t → t < eta →
        ∃ x ∈ U,
          realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
            (sardianProjectionAlgebraicFamily
              hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
              hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
              hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
              hn old).carrier := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  by_cases hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e)
  · rcases
        sardianProjection_projection_or_smallLevels_of_MaxwellAlmostEverywhereSmoothness
          hf hUFF hn old U e hepos hMaxwell hUopen hUconvex
          hregular hbounded hnonempty with
      hprojection | hsmallLevels
    · exact (hnotProjection hprojection).elim
    · exact hsmallLevels
  · exact
      exists_small_projected_radial_levels_of_not_isBounded_oldTupleFiber
        hG hsmooth hderiv hUFF hn old U hUmem hUbounded e hepos hbounded

/-- Boundary localization and the radial escape dichotomy remove the
boundedness premise from the source-shaped Case 2 step.  A bounded localized
fiber uses the fixed-minor alternative; an unbounded one uses its
reciprocal-radial range. -/
theorem
    exists_threshold_sardianProjection_smallLevels_of_boundary_bounded_or_radial
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily f) (order + 1) (n + 1) q)
    (A : Set (RealEuclidean (n + 1)))
    (T : Set (RealEuclidean ((n + 1) + (q + 1))))
    (oldModulus : CharbonnelModulus (q + 1))
    (U : Set (RealEuclidean n))
    (hUmem : U ∈ charbonnelClosure
      (literalZeroSetFamily (abelGeometricFamily f)) n)
    (hUbounded : Bornology.IsBounded U)
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus T (closure A))
    (hcarrier : old.carrier ⊆ T)
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ epsilon : RealEuclidean ((q + 1) + 1),
        oldModulus.IsBounded epsilon → epsilon 0 < delta →
        (∀ v, sardianProjectionOldTuple old v =
              CharbonnelModulus.parameterTail epsilon →
          Function.Surjective
            (fderiv ℝ (sardianProjectionOldTuple old) v)) →
        (sardianProjectionOldTupleFiber old U
          (CharbonnelModulus.parameterTail epsilon)).Nonempty →
        ∃ eta : ℝ, 0 < eta ∧
          ∀ t : ℝ, 0 < t → t < eta →
            ∃ x ∈ U,
              realEuclideanAppend x
                  (charbonnelAppendLastParameter
                    (CharbonnelModulus.parameterTail epsilon) t) ∈
                (sardianProjectionAlgebraicFamily
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
                  hn old).carrier := by
  obtain ⟨delta, hdelta, hnotProjection⟩ :=
    exists_threshold_takeLeft_image_oldTupleFiber_ne_of_boundary_of_carrier_subset
      old A T oldModulus U hbelow hcarrier hUopen hboundary
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon hepsilon hepsilonDelta hregular hnonempty
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hepos : ∀ i, 0 < CharbonnelModulus.parameterTail epsilon i := by
    intro i
    exact hepsilon.coord_pos i.succ
  by_cases hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U
        (CharbonnelModulus.parameterTail epsilon))
  · rcases sardianProjection_projection_or_smallLevels_of_theorems21_22
        hf hUFF hn old U (CharbonnelModulus.parameterTail epsilon) hepos
        h21 h22 hUopen hUconvex hregular hbounded hnonempty with
      hprojection | hsmallLevels
    · exact (hnotProjection epsilon hepsilon hepsilonDelta hprojection).elim
    · exact hsmallLevels
  · exact
      exists_small_projected_radial_levels_of_not_isBounded_oldTupleFiber
        hG hsmooth hderiv hUFF hn old U hUmem hUbounded
          (CharbonnelModulus.parameterTail epsilon) hepos hbounded

end AbelFormalization
