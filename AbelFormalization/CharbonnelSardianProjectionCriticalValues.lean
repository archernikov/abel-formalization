import AbelFormalization.CharbonnelSardianProjectionCase2Bridge
import AbelFormalization.CharbonnelSardianProjectionPaddedFamilyPrefixLift
import AbelFormalization.CharbonnelSardianEmptyInterior
import AbelFormalization.LionUpperNumbersCenterControl

/-!
# Critical parameter values of a finite padded Sardian family

For a rectangular tuple `g : ℝᵃ → ℝᵇ`, the algebraic critical-value set is
the image under `g` of the common zero locus of all maximal Jacobian minors.
This module gives that set one literal-zero projection residual, specializes
it to every padded constituent in the one-coordinate Sardian projection
step, and takes the finite union over the old family.

The resulting finite-family bad set belongs to the Charbonnel closure over
literal zero sets.  Outside it, every constituent old-tuple level is regular
at every point of the level.  We also record the available analytic
smallness facts: the singular incidence set is Hausdorff-null in the joint
value/source space, and the critical-value set is null in the square-map
case.  Passing nullity through the rectangular value projection is precisely
the general Morse--Sard step still absent from the current library.
-/

noncomputable section

open Set Function MeasureTheory
open scoped BigOperators ContDiff MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## A projected-zero description of rectangular critical values -/

/-- Values attained on the common zero locus of all maximal Jacobian minors. -/
def standardJacobianCriticalValueSet {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean b) :=
  g '' standardJacobianSingularLocus g

theorem mem_standardJacobianCriticalValueSet_iff
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (e : RealEuclidean b) :
    e ∈ standardJacobianCriticalValueSet g ↔
      ∃ x : RealEuclidean a, g x = e ∧
        ∀ cols : Fin b ↪ Fin a,
          standardJacobianColumnMinor g cols x = 0 := by
  simp only [standardJacobianCriticalValueSet, Set.mem_image,
    standardJacobianSingularLocus, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, hx, hsingular⟩
    exact ⟨x, hsingular, hx⟩

/-- For a differentiable tuple, the minor definition is exactly the usual
set of values attained at points with nonsurjective derivative. -/
theorem mem_standardJacobianCriticalValueSet_iff_nonsurjective
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) (e : RealEuclidean b) :
    e ∈ standardJacobianCriticalValueSet g ↔
      ∃ x : RealEuclidean a, g x = e ∧
        ¬Function.Surjective (fderiv ℝ g x) := by
  rw [mem_standardJacobianCriticalValueSet_iff]
  apply exists_congr
  intro x
  rw [and_congr_right_iff]
  intro _hx
  rw [fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
    (hg x)]
  simp

/-- Avoiding the critical-value set makes the whole attained level regular. -/
theorem fderiv_surjective_of_not_mem_standardJacobianCriticalValueSet
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) {e : RealEuclidean b}
    (he : e ∉ standardJacobianCriticalValueSet g)
    {x : RealEuclidean a} (hx : g x = e) :
    Function.Surjective (fderiv ℝ g x) := by
  by_contra hsingular
  exact he ((mem_standardJacobianCriticalValueSet_iff_nonsurjective
    g hg e).2 ⟨x, hx, hsingular⟩)

/-- One sum of squares cuts out the value equation and every maximal-minor
equation in coordinates `(e,x)`. -/
def standardJacobianCriticalValueResidual {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) :
    RealEuclideanFunction (b + a) :=
  fun w ↦
    (∑ i : Fin b,
      (g (realEuclideanTakeRight w) i - realEuclideanTakeLeft w i) ^ 2) +
    (∑ cols : Fin b ↪ Fin a,
      standardJacobianColumnMinor g cols
        (realEuclideanTakeRight w) ^ 2)

theorem standardJacobianCriticalValueResidual_append_eq_zero_iff
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (e : RealEuclidean b) (x : RealEuclidean a) :
    standardJacobianCriticalValueResidual g
        (realEuclideanAppend e x) = 0 ↔
      g x = e ∧
        ∀ cols : Fin b ↪ Fin a,
          standardJacobianColumnMinor g cols x = 0 := by
  classical
  simp only [standardJacobianCriticalValueResidual,
    realEuclideanTakeRight_append, realEuclideanTakeLeft_append]
  let A : ℝ := ∑ i : Fin b, (g x i - e i) ^ 2
  let M : ℝ := ∑ cols : Fin b ↪ Fin a,
    standardJacobianColumnMinor g cols x ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg
    (fun i _ ↦ sq_nonneg (g x i - e i))
  have hM : 0 ≤ M := Finset.sum_nonneg
    (fun cols _ ↦ sq_nonneg
      (standardJacobianColumnMinor g cols x))
  change A + M = 0 ↔
    g x = e ∧
      ∀ cols : Fin b ↪ Fin a,
        standardJacobianColumnMinor g cols x = 0
  constructor
  · intro hzero
    have hAzero : A = 0 := by linarith
    have hMzero : M = 0 := by linarith
    constructor
    · funext i
      have hi := ((Finset.sum_sq_eq_zero_iff Finset.univ
        (fun j : Fin b ↦ g x j - e j)).mp hAzero) i
        (Finset.mem_univ i)
      exact sub_eq_zero.mp hi
    · intro cols
      exact ((Finset.sum_sq_eq_zero_iff Finset.univ
        (fun c : Fin b ↪ Fin a ↦
          standardJacobianColumnMinor g c x)).mp hMzero) cols
        (Finset.mem_univ cols)
  · rintro ⟨hvalue, hminor⟩
    have hAzero : A = 0 := by
      apply (Finset.sum_sq_eq_zero_iff Finset.univ
        (fun i : Fin b ↦ g x i - e i)).2
      intro i _
      exact sub_eq_zero.mpr (congrFun hvalue i)
    have hMzero : M = 0 := by
      apply (Finset.sum_sq_eq_zero_iff Finset.univ
        (fun cols : Fin b ↪ Fin a ↦
          standardJacobianColumnMinor g cols x)).2
      intro cols _
      exact hminor cols
    simp only [hAzero, hMzero, add_zero]

/-- Geometric closure and coordinate-derivative closure keep the complete
critical-value residual inside the original function family. -/
theorem standardJacobianCriticalValueResidual_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    standardJacobianCriticalValueResidual g ∈ G (b + a) := by
  classical
  let L := realEuclideanTakeLeftLinearMap b a
  let R := realEuclideanTakeRightLinearMap b a
  have hvalue : ∀ i : Fin b,
      (fun w : RealEuclidean (b + a) ↦
        g (realEuclideanTakeRight w) i -
          realEuclideanTakeLeft w i) ∈ G (b + a) := by
    intro i
    have hpulled := hG.affine_comp (hg i) R.toAffineMap
    let coordinate : Fin (b + a) := Fin.castAdd a i
    have hcoordinate :
        (fun w : RealEuclidean (b + a) ↦ w coordinate) ∈ G (b + a) := by
      simpa [coordinate] using hG.polynomial (MvPolynomial.X coordinate)
    have hsub := hG.sub_mem hpulled hcoordinate
    convert hsub using 1
    funext w
    rfl
  have hminor : ∀ cols : Fin b ↪ Fin a,
      (fun w : RealEuclidean (b + a) ↦
        standardJacobianColumnMinor g cols
          (realEuclideanTakeRight w)) ∈ G (b + a) := by
    intro cols
    have hm := hG.standardJacobianColumnMinor_mem hderiv g hg cols
    convert hG.affine_comp hm R.toAffineMap using 1
    funext w
    rfl
  have hvalueSum :
      (fun w : RealEuclidean (b + a) ↦
        ∑ i : Fin b,
          (g (realEuclideanTakeRight w) i -
            realEuclideanTakeLeft w i) ^ 2) ∈ G (b + a) := by
    have hsum := hG.finset_sum_mem (Finset.univ : Finset (Fin b))
      (fun i ↦ fun w : RealEuclidean (b + a) ↦
        (g (realEuclideanTakeRight w) i -
          realEuclideanTakeLeft w i) ^ 2)
      (by intro i _; exact hG.sq_mem (hvalue i))
    convert hsum using 1
    funext w
    simp only [Finset.sum_apply]
  have hminorSum :
      (fun w : RealEuclidean (b + a) ↦
        ∑ cols : Fin b ↪ Fin a,
          standardJacobianColumnMinor g cols
            (realEuclideanTakeRight w) ^ 2) ∈ G (b + a) := by
    have hsum := hG.finset_sum_mem
      (Finset.univ : Finset (Fin b ↪ Fin a))
      (fun cols ↦ fun w : RealEuclidean (b + a) ↦
        standardJacobianColumnMinor g cols
          (realEuclideanTakeRight w) ^ 2)
      (by intro cols _; exact hG.sq_mem (hminor cols))
    convert hsum using 1
    funext w
    simp only [Finset.sum_apply]
  have htotal := hG.add hvalueSum hminorSum
  convert htotal using 1
  funext w
  rfl

/-- Rectangular critical values are a projection of one literal zero set. -/
theorem standardJacobianCriticalValueSet_isProjectedZeroSet
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    IsProjectedZeroSet G (standardJacobianCriticalValueSet g) := by
  refine ⟨a, standardJacobianCriticalValueResidual g,
    standardJacobianCriticalValueResidual_mem hG hderiv g hg, ?_⟩
  ext e
  simp only [Set.mem_ofPred]
  rw [mem_standardJacobianCriticalValueSet_iff]
  exact exists_congr (fun x ↦
    (standardJacobianCriticalValueResidual_append_eq_zero_iff
      g e x).symm)

/-- Positive-dimensional critical-value sets therefore belong to the
literal-zero Charbonnel closure. -/
theorem standardJacobianCriticalValueSet_mem_literalZeroCharbonnel
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (hb : 0 < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    standardJacobianCriticalValueSet g ∈
      charbonnelClosure (literalZeroSetFamily G) b :=
  (standardJacobianCriticalValueSet_isProjectedZeroSet
    hG hderiv g hg).mem_literalZeroSet_charbonnelClosure hb

/-! ## Analytic smallness available without rectangular Morse--Sard -/

/-- The joint value/source incidence cut out by the critical residual. -/
def standardJacobianCriticalIncidenceSet {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) :
    Set (RealEuclidean (b + a)) :=
  {w | standardJacobianCriticalValueResidual g w = 0}

/-- The graph that records both a tuple value and its source point. -/
def standardJacobianValueSourceGraph {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) :
    RealEuclidean a → RealEuclidean (b + a) :=
  fun x ↦ realEuclideanAppend (g x) x

theorem differentiable_standardJacobianValueSourceGraph
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) :
    Differentiable ℝ (standardJacobianValueSourceGraph g) := by
  rw [differentiable_pi]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa only [standardJacobianValueSourceGraph,
      realEuclideanAppend_castAdd] using
      (differentiable_pi.mp hg j)
  · simpa only [standardJacobianValueSourceGraph,
      realEuclideanAppend_natAdd] using
      ((contDiff_apply ℝ ℝ j : ContDiff ℝ 1
        (fun x : RealEuclidean a ↦ x j)).differentiable (by norm_num))

/-- The critical incidence is contained in the ordinary value/source graph. -/
theorem standardJacobianCriticalIncidenceSet_subset_range
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) :
    standardJacobianCriticalIncidenceSet g ⊆
      Set.range (standardJacobianValueSourceGraph g) := by
  intro w hw
  let e := realEuclideanTakeLeft w
  let x := realEuclideanTakeRight w
  have hcritical :=
    (standardJacobianCriticalValueResidual_append_eq_zero_iff
      g e x).1 (by
        rw [show realEuclideanAppend e x = w by
          exact realEuclideanAppend_take w]
        exact hw)
  refine ⟨x, ?_⟩
  rw [standardJacobianValueSourceGraph, hcritical.1]
  exact realEuclideanAppend_take w

/-- Although its projection need not preserve nullity, the full singular
witness incidence is Hausdorff-null in the joint value/source space. -/
theorem standardJacobianCriticalIncidenceSet_hausdorffMeasure_eq_zero
    {a b : ℕ} (hb : 0 < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) :
    (μH[Module.finrank ℝ (RealEuclidean (b + a))] :
        Measure (RealEuclidean (b + a)))
      (standardJacobianCriticalIncidenceSet g) = 0 := by
  apply measure_mono_null
    (standardJacobianCriticalIncidenceSet_subset_range g)
  have hnull := hausdorffMeasure_image_eq_zero_of_finrank_lt
    (s := Set.univ)
    (differentiable_standardJacobianValueSourceGraph g hg).differentiableOn
    (by
      simp only [Module.finrank_fin_fun]
      omega)
  simpa only [image_univ] using hnull

theorem standardJacobianCriticalIncidenceSet_interior_eq_empty
    {a b : ℕ} (hb : 0 < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) :
    interior (standardJacobianCriticalIncidenceSet g) = ∅ :=
  (μH[Module.finrank ℝ (RealEuclidean (b + a))] :
      Measure (RealEuclidean (b + a))).interior_eq_empty_of_null
    (standardJacobianCriticalIncidenceSet_hausdorffMeasure_eq_zero
      hb g hg)

/-- Critical values are contained in the full range of the tuple. -/
theorem standardJacobianCriticalValueSet_subset_range
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) :
    standardJacobianCriticalValueSet g ⊆ Set.range g := by
  intro e he
  obtain ⟨x, _hxsingular, rfl⟩ := he
  exact ⟨x, rfl⟩

/-- When the source dimension is already smaller than the target dimension,
the available low-to-high-dimensional Sard lemma makes the critical values
Hausdorff-null (indeed the entire range is null). -/
theorem standardJacobianCriticalValueSet_hausdorffMeasure_eq_zero_of_lt
    {a b : ℕ} (hab : a < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) :
    (μH[Module.finrank ℝ (RealEuclidean b)] :
        Measure (RealEuclidean b))
      (standardJacobianCriticalValueSet g) = 0 := by
  apply measure_mono_null
    (standardJacobianCriticalValueSet_subset_range g)
  have hnull := hausdorffMeasure_image_eq_zero_of_finrank_lt
    (s := Set.univ) hg.differentiableOn (by
      simpa only [Module.finrank_fin_fun] using hab)
  simpa only [image_univ] using hnull

theorem standardJacobianCriticalValueSet_interior_eq_empty_of_lt
    {a b : ℕ} (hab : a < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : Differentiable ℝ g) :
    interior (standardJacobianCriticalValueSet g) = ∅ :=
  (μH[Module.finrank ℝ (RealEuclidean b)] :
      Measure (RealEuclidean b)).interior_eq_empty_of_null
    (standardJacobianCriticalValueSet_hausdorffMeasure_eq_zero_of_lt
      hab g hg)

/-- In equal source and target dimensions, mathlib's fixed-dimensional Sard
lemma does give nullity of the actual critical-value set. -/
theorem volume_standardJacobianCriticalValueSet_eq_zero_of_contDiff
    {a : ℕ} (g : RealEuclidean a → RealEuclidean a)
    (hg : ContDiff ℝ 1 g) :
    (volume : Measure (RealEuclidean a))
      (standardJacobianCriticalValueSet g) = 0 := by
  have hset : standardJacobianCriticalValueSet g =
      g '' {x | ¬Function.Surjective (fderiv ℝ g x)} := by
    ext e
    rw [mem_standardJacobianCriticalValueSet_iff_nonsurjective
      g hg.differentiable_one e]
    constructor
    · rintro ⟨x, hx, hsingular⟩
      exact ⟨x, hsingular, hx⟩
    · rintro ⟨x, hsingular, hx⟩
      exact ⟨x, hx, hsingular⟩
  rw [hset]
  exact volume_criticalValues_eq_zero_of_contDiff hg

theorem interior_standardJacobianCriticalValueSet_eq_empty_of_contDiff
    {a : ℕ} (g : RealEuclidean a → RealEuclidean a)
    (hg : ContDiff ℝ 1 g) :
    interior (standardJacobianCriticalValueSet g) = ∅ :=
  (volume : Measure (RealEuclidean a)).interior_eq_empty_of_null
    (volume_standardJacobianCriticalValueSet_eq_zero_of_contDiff g hg)

/-- The current mathlib Sard and Hausdorff-dimension APIs cover all maps
whose source dimension is at most their target dimension.  Equality uses
the fixed-dimensional Sard lemma; strict inequality makes the whole range
Hausdorff-null.  The opposite strict inequality is the genuinely missing
rectangular Morse--Sard case. -/
theorem standardJacobianCriticalValueSet_interior_eq_empty_of_le
    {a b : ℕ} (hab : a ≤ b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : ContDiff ℝ 1 g) :
    interior (standardJacobianCriticalValueSet g) = ∅ := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    exact interior_standardJacobianCriticalValueSet_eq_empty_of_contDiff g hg
  · exact standardJacobianCriticalValueSet_interior_eq_empty_of_lt
      hab g hg.differentiable_one

/-! ## Smoothness at the exact rectangular Morse--Sard order -/

/-- An old tuple from an everywhere-smooth geometric family is itself
`C^∞`, independently of the finite differentiability order recorded in its
Sardian constituent. -/
theorem contDiff_top_sardianProjectionOldTuple_of_smoothFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    ContDiff ℝ ∞ (sardianProjectionOldTuple old) := by
  rw [contDiff_pi]
  intro i
  exact hsmooth _ _ (sardianProjectionOldTuple_inFamily hG old i)

/-- For a tuple `ℝ^(n + (q+1)) → ℝ^(q+1)`, classical rectangular
Morse--Sard asks for integer differentiability order strictly larger than
the dimension gap `n`, namely `C^(n+1)`.  The Sardian old tuple satisfies
that order (indeed it is `C^∞`). -/
theorem contDiff_morseSardOrder_sardianProjectionOldTuple
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    ContDiff ℝ (n + 1) (sardianProjectionOldTuple old) :=
  (contDiff_top_sardianProjectionOldTuple_of_smoothFamily
    hG hsmooth old).of_le (by simp)

/-! ## Padded constituent parameter values -/

namespace CharbonnelPaddedSardianConstituent

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Retain the parameter prefix actually used by a padded constituent. -/
def projectionParameterPrefixLinearMap
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K) :
    RealEuclidean (K + 1) →ₗ[ℝ]
      RealEuclidean (piece.hiddenArity + 1) where
  toFun epsilon := fun i ↦ epsilon
    (Fin.castLE (Nat.succ_le_succ piece.hiddenArity_le) i)
  map_add' := by
    intro epsilon eta
    rfl
  map_smul' := by
    intro c epsilon
    rfl

@[simp]
theorem projectionParameterPrefixLinearMap_apply
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K)
    (epsilon : RealEuclidean (K + 1))
    (i : Fin (piece.hiddenArity + 1)) :
    piece.projectionParameterPrefixLinearMap epsilon i =
      epsilon (Fin.castLE
        (Nat.succ_le_succ piece.hiddenArity_le) i) :=
  rfl

/-- Common-depth parameter vectors whose used prefix is a critical value of
this constituent's old tuple map.  Unused trailing coordinates are free. -/
def projectionCriticalParameterSet
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K) :
    Set (RealEuclidean (K + 1)) :=
  piece.projectionParameterPrefixLinearMap ⁻¹'
    standardJacobianCriticalValueSet
      (sardianProjectionOldTuple piece.constituent)

/-- Semantic form: a parameter is bad exactly when its used prefix is
attained at a point where the old tuple derivative is nonsurjective. -/
theorem mem_projectionCriticalParameterSet_iff
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K)
    (epsilon : RealEuclidean (K + 1)) :
    epsilon ∈ piece.projectionCriticalParameterSet ↔
      ∃ v : RealEuclidean (n + (piece.hiddenArity + 1)),
        sardianProjectionOldTuple piece.constituent v =
          piece.projectionParameterPrefixLinearMap epsilon ∧
        ¬Function.Surjective
          (fderiv ℝ (sardianProjectionOldTuple piece.constituent) v) := by
  have hdiff : Differentiable ℝ
      (sardianProjectionOldTuple piece.constituent) :=
    (contDiff_sardianProjectionOldTuple
      (order := order) (n := n) piece.constituent).differentiable
      (by simp)
  exact mem_standardJacobianCriticalValueSet_iff_nonsurjective
    (sardianProjectionOldTuple piece.constituent) hdiff
    (piece.projectionParameterPrefixLinearMap epsilon)

/-- The bad common-depth parameter set of one padded constituent is still a
projected zero set. -/
theorem projectionCriticalParameterSet_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K) :
    IsProjectedZeroSet G piece.projectionCriticalParameterSet := by
  have hcritical := standardJacobianCriticalValueSet_isProjectedZeroSet
    hG hderiv (sardianProjectionOldTuple piece.constituent)
      (sardianProjectionOldTuple_inFamily hG piece.constituent)
  exact hcritical.linear_preimage hG
    piece.projectionParameterPrefixLinearMap

theorem projectionCriticalParameterSet_mem_literalZeroCharbonnel
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K) :
    piece.projectionCriticalParameterSet ∈
      charbonnelClosure (literalZeroSetFamily G) (K + 1) :=
  (piece.projectionCriticalParameterSet_isProjectedZeroSet hG hderiv)
    |>.mem_literalZeroSet_charbonnelClosure (by omega)

/-- Every point of the selected old-tuple level is regular when the common
parameter vector avoids this constituent's bad set. -/
theorem oldTuple_fderiv_surjective_of_not_mem_projectionCriticalParameterSet
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) K)
    {epsilon : RealEuclidean (K + 1)}
    (hepsilon : epsilon ∉ piece.projectionCriticalParameterSet)
    {v : RealEuclidean (n + (piece.hiddenArity + 1))}
    (hv : sardianProjectionOldTuple piece.constituent v =
      piece.projectionParameterPrefixLinearMap epsilon) :
    Function.Surjective
      (fderiv ℝ (sardianProjectionOldTuple piece.constituent) v) := by
  have hdiff : Differentiable ℝ
      (sardianProjectionOldTuple piece.constituent) :=
    (contDiff_sardianProjectionOldTuple
      (order := order) (n := n) piece.constituent).differentiable
      (by simp)
  exact fderiv_surjective_of_not_mem_standardJacobianCriticalValueSet
    (sardianProjectionOldTuple piece.constituent) hdiff hepsilon hv

end CharbonnelPaddedSardianConstituent

/-! ## The finite-family bad parameter set -/

namespace CharbonnelFiniteSardianFamily

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- A common parameter vector is bad when it is critical for at least one
constituent prefix in the old finite padded family. -/
def projectionCriticalParameterSet
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    Set (RealEuclidean (K + 1)) :=
  {epsilon | ∃ piece ∈ family.constituents,
    epsilon ∈ piece.projectionCriticalParameterSet}

theorem mem_projectionCriticalParameterSet_iff
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    (epsilon : RealEuclidean (K + 1)) :
    epsilon ∈ family.projectionCriticalParameterSet ↔
      ∃ piece ∈ family.constituents,
        ∃ v : RealEuclidean (n + (piece.hiddenArity + 1)),
          sardianProjectionOldTuple piece.constituent v =
            piece.projectionParameterPrefixLinearMap epsilon ∧
          ¬Function.Surjective
            (fderiv ℝ (sardianProjectionOldTuple piece.constituent) v) := by
  simp only [projectionCriticalParameterSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨piece, hpiece, hbad⟩
    exact ⟨piece, hpiece,
      (piece.mem_projectionCriticalParameterSet_iff epsilon).1 hbad⟩
  · rintro ⟨piece, hpiece, hbad⟩
    exact ⟨piece, hpiece,
      (piece.mem_projectionCriticalParameterSet_iff epsilon).2 hbad⟩

/-- Finite union preserves the projected-zero description of the bad set. -/
theorem projectionCriticalParameterSet_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    IsProjectedZeroSet G family.projectionCriticalParameterSet := by
  change IsProjectedZeroSet G
    {epsilon | ∃ piece ∈ family.constituents,
      epsilon ∈ piece.projectionCriticalParameterSet}
  induction family.constituents with
  | nil =>
      simpa using
        (isProjectedZeroSet_empty (G := G) hG :
          IsProjectedZeroSet G (∅ : Set (RealEuclidean (K + 1))))
  | cons piece pieces ih =>
      have hpiece := piece.projectionCriticalParameterSet_isProjectedZeroSet
        hG hderiv
      have hunion := hpiece.union hG ih
      rw [show
        {epsilon | ∃ other ∈ piece :: pieces,
          epsilon ∈ other.projectionCriticalParameterSet} =
            piece.projectionCriticalParameterSet ∪
              {epsilon | ∃ other ∈ pieces,
                epsilon ∈ other.projectionCriticalParameterSet} by
        ext epsilon
        simp]
      exact hunion

/-- The finite bad-value set belongs to the literal-zero Charbonnel closure
in the common parameter arity. -/
theorem projectionCriticalParameterSet_mem_literalZeroCharbonnel
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    family.projectionCriticalParameterSet ∈
      charbonnelClosure (literalZeroSetFamily G) (K + 1) :=
  (family.projectionCriticalParameterSet_isProjectedZeroSet hG hderiv)
    |>.mem_literalZeroSet_charbonnelClosure (by omega)

/-- Exact finite-family regularity conclusion: outside the one finite bad
set, every old tuple is a submersion at every point of its selected level. -/
theorem not_mem_projectionCriticalParameterSet_iff_all_regular
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    (epsilon : RealEuclidean (K + 1)) :
    epsilon ∉ family.projectionCriticalParameterSet ↔
      ∀ piece ∈ family.constituents,
        ∀ v : RealEuclidean (n + (piece.hiddenArity + 1)),
          sardianProjectionOldTuple piece.constituent v =
              piece.projectionParameterPrefixLinearMap epsilon →
            Function.Surjective
              (fderiv ℝ
                (sardianProjectionOldTuple piece.constituent) v) := by
  constructor
  · intro hepsilon piece hpiece v hv
    apply piece.oldTuple_fderiv_surjective_of_not_mem_projectionCriticalParameterSet
      (epsilon := epsilon) ?_ hv
    intro hbad
    exact hepsilon ⟨piece, hpiece, hbad⟩
  · intro hregular hbad
    rw [family.mem_projectionCriticalParameterSet_iff epsilon] at hbad
    obtain ⟨piece, hpiece, v, hv, hsingular⟩ := hbad
    exact hsingular (hregular piece hpiece v hv)

/-- Indexed form of the simultaneous finite-family regularity conclusion. -/
theorem indexedConstituent_oldTuple_fderiv_surjective_of_not_mem
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    {epsilon : RealEuclidean (K + 1)}
    (hepsilon : epsilon ∉ family.projectionCriticalParameterSet)
    (i : family.ConstituentIndex)
    (v : RealEuclidean
      (n + ((family.indexedConstituent i).hiddenArity + 1)))
    (hv : sardianProjectionOldTuple
        (family.indexedConstituent i).constituent v =
      (family.indexedConstituent i).projectionParameterPrefixLinearMap
        epsilon) :
    Function.Surjective
      (fderiv ℝ
        (sardianProjectionOldTuple
          (family.indexedConstituent i).constituent) v) := by
  exact (family.not_mem_projectionCriticalParameterSet_iff_all_regular
    epsilon).1 hepsilon (family.indexedConstituent i)
      (List.get_mem family.constituents i) v hv

/-! ## Critical parameters after exact-depth normalization -/

/-- Bad full parameter vectors for the exact-depth old constituents used by
the mixed-depth projection constructor.  Unlike `projectionCriticalParameterSet`,
this set tests the normalized tuple at the entire common `K + 1` parameter
vector, exactly as required by the Case 2 assembly. -/
def exactDepthProjectionCriticalParameterSet
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    Set (RealEuclidean (K + 1)) :=
  {epsilon | ∃ exactOld ∈
      sardianProjectionOldExactDepthList hG hsmooth family,
    epsilon ∈ standardJacobianCriticalValueSet
      (sardianProjectionOldTuple exactOld)}

/-- Every normalized tuple occurring in the exact-depth list has the
`C^(n+1)` regularity required by the classical Morse--Sard threshold for its
dimension gap `n`. -/
theorem exactDepthOldTuple_contDiff_morseSardOrder
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    (exactOld : CharbonnelSardianConstituent
      G (order + 1) (n + 1) K)
    (_hexactOld :
      exactOld ∈ sardianProjectionOldExactDepthList hG hsmooth family) :
    ContDiff ℝ (n + 1) (sardianProjectionOldTuple exactOld) :=
  contDiff_morseSardOrder_sardianProjectionOldTuple hG hsmooth exactOld

/-- Semantic form of the full-tail bad set. -/
theorem mem_exactDepthProjectionCriticalParameterSet_iff
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    (epsilon : RealEuclidean (K + 1)) :
    epsilon ∈ family.exactDepthProjectionCriticalParameterSet hG hsmooth ↔
      ∃ exactOld ∈ sardianProjectionOldExactDepthList hG hsmooth family,
        ∃ v : RealEuclidean (n + (K + 1)),
          sardianProjectionOldTuple exactOld v = epsilon ∧
          ¬Function.Surjective
            (fderiv ℝ (sardianProjectionOldTuple exactOld) v) := by
  simp only [exactDepthProjectionCriticalParameterSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨exactOld, hexactOld, hbad⟩
    have hdiff : Differentiable ℝ (sardianProjectionOldTuple exactOld) :=
      (contDiff_sardianProjectionOldTuple exactOld).differentiable (by simp)
    exact ⟨exactOld, hexactOld,
      (mem_standardJacobianCriticalValueSet_iff_nonsurjective
        (sardianProjectionOldTuple exactOld) hdiff epsilon).1 hbad⟩
  · rintro ⟨exactOld, hexactOld, hbad⟩
    have hdiff : Differentiable ℝ (sardianProjectionOldTuple exactOld) :=
      (contDiff_sardianProjectionOldTuple exactOld).differentiable (by simp)
    exact ⟨exactOld, hexactOld,
      (mem_standardJacobianCriticalValueSet_iff_nonsurjective
        (sardianProjectionOldTuple exactOld) hdiff epsilon).2 hbad⟩

/-- The exact-depth finite bad set is again one projected-zero set. -/
theorem exactDepthProjectionCriticalParameterSet_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    IsProjectedZeroSet G
      (family.exactDepthProjectionCriticalParameterSet hG hsmooth) := by
  change IsProjectedZeroSet G
    {epsilon | ∃ exactOld ∈
        sardianProjectionOldExactDepthList hG hsmooth family,
      epsilon ∈ standardJacobianCriticalValueSet
        (sardianProjectionOldTuple exactOld)}
  induction sardianProjectionOldExactDepthList hG hsmooth family with
  | nil =>
      simpa using
        (isProjectedZeroSet_empty (G := G) hG :
          IsProjectedZeroSet G (∅ : Set (RealEuclidean (K + 1))))
  | cons exactOld exactOlds ih =>
      have hpiece := standardJacobianCriticalValueSet_isProjectedZeroSet
        hG hderiv (sardianProjectionOldTuple exactOld)
          (sardianProjectionOldTuple_inFamily hG exactOld)
      have hunion := hpiece.union hG ih
      rw [show
        {epsilon | ∃ other ∈ exactOld :: exactOlds,
          epsilon ∈ standardJacobianCriticalValueSet
            (sardianProjectionOldTuple other)} =
            standardJacobianCriticalValueSet
                (sardianProjectionOldTuple exactOld) ∪
              {epsilon | ∃ other ∈ exactOlds,
                epsilon ∈ standardJacobianCriticalValueSet
                  (sardianProjectionOldTuple other)} by
        ext epsilon
        simp]
      exact hunion

/-- The full-tail exact-depth bad set belongs to the literal-zero
Charbonnel closure in the common parameter arity. -/
theorem exactDepthProjectionCriticalParameterSet_mem_literalZeroCharbonnel
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    family.exactDepthProjectionCriticalParameterSet hG hsmooth ∈
      charbonnelClosure (literalZeroSetFamily G) (K + 1) :=
  (family.exactDepthProjectionCriticalParameterSet_isProjectedZeroSet
    hG hsmooth hderiv).mem_literalZeroSet_charbonnelClosure (by omega)

/-- Exact assembly-facing regularity statement: avoiding the finite bad set
makes the full common parameter vector a regular value of every normalized
old tuple in `sardianProjectionOldExactDepthList`. -/
theorem
    not_mem_exactDepthProjectionCriticalParameterSet_iff_all_regular
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    (epsilon : RealEuclidean (K + 1)) :
    epsilon ∉ family.exactDepthProjectionCriticalParameterSet hG hsmooth ↔
      ∀ exactOld ∈ sardianProjectionOldExactDepthList hG hsmooth family,
        ∀ v : RealEuclidean (n + (K + 1)),
          sardianProjectionOldTuple exactOld v = epsilon →
            Function.Surjective
              (fderiv ℝ (sardianProjectionOldTuple exactOld) v) := by
  constructor
  · intro hepsilon exactOld hexactOld v hv
    have hdiff : Differentiable ℝ (sardianProjectionOldTuple exactOld) :=
      (contDiff_sardianProjectionOldTuple exactOld).differentiable (by simp)
    apply fderiv_surjective_of_not_mem_standardJacobianCriticalValueSet
      (sardianProjectionOldTuple exactOld) hdiff ?_ hv
    intro hbad
    exact hepsilon ⟨exactOld, hexactOld, hbad⟩
  · intro hregular hbad
    rw [family.mem_exactDepthProjectionCriticalParameterSet_iff
      hG hsmooth epsilon] at hbad
    obtain ⟨exactOld, hexactOld, v, hv, hsingular⟩ := hbad
    exact hsingular (hregular exactOld hexactOld v hv)

/-- One-direction form convenient at a selected exact-depth constituent. -/
theorem exactDepthOldTuple_fderiv_surjective_of_not_mem
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K)
    {epsilon : RealEuclidean (K + 1)}
    (hepsilon :
      epsilon ∉ family.exactDepthProjectionCriticalParameterSet hG hsmooth)
    (exactOld : CharbonnelSardianConstituent
      G (order + 1) (n + 1) K)
    (hexactOld :
      exactOld ∈ sardianProjectionOldExactDepthList hG hsmooth family)
    (v : RealEuclidean (n + (K + 1)))
    (hv : sardianProjectionOldTuple exactOld v = epsilon) :
    Function.Surjective
      (fderiv ℝ (sardianProjectionOldTuple exactOld) v) :=
  (family.not_mem_exactDepthProjectionCriticalParameterSet_iff_all_regular
    hG hsmooth epsilon).1 hepsilon exactOld hexactOld v hv

end CharbonnelFiniteSardianFamily

end AbelFormalization
