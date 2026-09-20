import AbelFormalization.LionCarpetedLeaf
import AbelFormalization.LionStandardCarpet

/-!
# The carpets used in Lion's Lemma 4

For a carpet `delta` and a parameter `(center, height)` with positive height,
Lion replaces `delta` by

`delta_a(x) = delta(x) / (sum_i (x_i - center_i)^2 + height^2)`.

The denominator is the squared Euclidean distance from `(x, 0)` to
`(center, height)`.  Its positive last-coordinate contribution makes it
everywhere nonzero.  This file proves that `delta_a` belongs to the same
geometric family and carpets both the original open set and the same leaf.
The subsequent regular-locus carpet from Lemma 3 can therefore be applied to
this re-carpeted leaf without changing its carrier.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- The flat-coordinate form of
`||(x, 0) - (center, height)||^2`. -/
def lionLiftedSquaredDistanceDenominator {n : ℕ}
    (center : RealEuclidean n) (height : ℝ) :
    RealEuclideanFunction n :=
  fun x ↦ standardSquaredDistance center x + height ^ 2

/-- Lion's parameter-dependent carpet `delta_a`. -/
def lionRadialCarpet {n : ℕ} (delta : RealEuclideanFunction n)
    (center : RealEuclidean n) (height : ℝ) :
    RealEuclideanFunction n :=
  fun x ↦ delta x / lionLiftedSquaredDistanceDenominator center height x

theorem lionLiftedSquaredDistanceDenominator_nonneg {n : ℕ}
    (center : RealEuclidean n) (height : ℝ) (x : RealEuclidean n) :
    0 ≤ lionLiftedSquaredDistanceDenominator center height x := by
  unfold lionLiftedSquaredDistanceDenominator
  exact add_nonneg (standardSquaredDistance_nonneg center x) (sq_nonneg height)

/-- The positive height keeps Lion's radial denominator away from zero. -/
theorem lionLiftedSquaredDistanceDenominator_pos {n : ℕ}
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n) :
    0 < lionLiftedSquaredDistanceDenominator center height x := by
  unfold lionLiftedSquaredDistanceDenominator
  nlinarith [standardSquaredDistance_nonneg center x]

theorem lionLiftedSquaredDistanceDenominator_ne_zero {n : ℕ}
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n) :
    lionLiftedSquaredDistanceDenominator center height x ≠ 0 :=
  ne_of_gt (lionLiftedSquaredDistanceDenominator_pos center hheight x)

theorem lionLiftedSquaredDistanceDenominator_continuous {n : ℕ}
    (center : RealEuclidean n) (height : ℝ) :
    Continuous (lionLiftedSquaredDistanceDenominator center height) := by
  have hdist : Continuous
      (fun x : RealEuclidean n ↦ ∑ i : Fin n, (x i - center i) ^ 2) :=
    continuous_finsetSum Finset.univ fun i _ ↦
      ((continuous_apply i).sub continuous_const).pow 2
  have hconst : Continuous (fun _ : RealEuclidean n ↦ height ^ 2) :=
    continuous_const
  convert hdist.add hconst using 1
  funext x
  simp only [lionLiftedSquaredDistanceDenominator,
    standardSquaredDistance, algebraicSquaredDistance_apply,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, Pi.add_apply]

theorem lionRadialCarpet_continuous {n : ℕ}
    {delta : RealEuclideanFunction n} (hdelta : Continuous delta)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    Continuous (lionRadialCarpet delta center height) := by
  unfold lionRadialCarpet
  exact hdelta.div
    (lionLiftedSquaredDistanceDenominator_continuous center height)
    (lionLiftedSquaredDistanceDenominator_ne_zero center hheight)

theorem IsGeometricFunctionFamily.lionLiftedSquaredDistanceDenominator_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (center : RealEuclidean n) (height : ℝ) :
    lionLiftedSquaredDistanceDenominator center height ∈ G n := by
  exact hG.add (hG.standardSquaredDistance_mem center)
    (hG.const_mem (height ^ 2))

/-- The first carpet modification in Lemma 4 remains in the geometric
function family. -/
theorem IsGeometricFunctionFamily.lionRadialCarpet_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {delta : RealEuclideanFunction n} (hdelta : delta ∈ G n)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    lionRadialCarpet delta center height ∈ G n := by
  have hden := hG.lionLiftedSquaredDistanceDenominator_mem center height
  have hinv := hG.inv hden
    (lionLiftedSquaredDistanceDenominator_ne_zero center hheight)
  have hmul := hG.mul hdelta hinv
  convert hmul using 1
  funext x
  simp only [lionRadialCarpet, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]

/-- Restricting a carpet to its intersection with a closed set preserves
the carpet property.  This is the zero-fiber restriction used for leaves. -/
theorem IsLionCarpetOn.inter_closed
    {X : Type*} [TopologicalSpace X]
    {U C : Set X} {delta : X → ℝ}
    (hcarpet : IsLionCarpetOn U delta) (hC : IsClosed C) :
    IsLionCarpetOn (U ∩ C) delta := by
  constructor
  · intro x hx
    exact hcarpet.pos x hx.1
  · intro eta heta
    have hcompact := hcarpet.isCompact_superlevel eta heta
    have heq :
        {x | x ∈ U ∩ C ∧ eta ≤ delta x} =
          {x | x ∈ U ∧ eta ≤ delta x} ∩ C := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff]
      tauto
    rw [heq]
    exact hcompact.inter_right hC

/-- Dividing by Lion's lifted squared distance preserves the carpet
property on the same open set. -/
theorem IsLionCarpetOn.of_lionRadialCarpet
    {n : ℕ} {U : Set (RealEuclidean n)}
    {delta : RealEuclideanFunction n}
    (hcarpet : IsLionCarpetOn U delta) (hdelta : Continuous delta)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    IsLionCarpetOn U (lionRadialCarpet delta center height) := by
  constructor
  · intro x hx
    exact div_pos (hcarpet.pos x hx)
      (lionLiftedSquaredDistanceDenominator_pos center hheight x)
  · intro eta heta
    let denominator := lionLiftedSquaredDistanceDenominator center height
    have hheightSq : 0 < height ^ 2 := sq_pos_of_pos hheight
    have hthreshold : 0 < eta * height ^ 2 := mul_pos heta hheightSq
    have hcompact : IsCompact
        {x | x ∈ U ∧ eta * height ^ 2 ≤ delta x} :=
      hcarpet.isCompact_superlevel (eta * height ^ 2) hthreshold
    have hdenContinuous : Continuous denominator := by
      exact lionLiftedSquaredDistanceDenominator_continuous center height
    have hclosed : IsClosed {x | eta * denominator x ≤ delta x} :=
      isClosed_le (continuous_const.mul hdenContinuous) hdelta
    have heq :
        {x | x ∈ U ∧ eta ≤ lionRadialCarpet delta center height x} =
          {x | x ∈ U ∧ eta * height ^ 2 ≤ delta x} ∩
            {x | eta * denominator x ≤ delta x} := by
      ext x
      have hdenPos : 0 < denominator x := by
        exact lionLiftedSquaredDistanceDenominator_pos center hheight x
      have hheightLe : height ^ 2 ≤ denominator x := by
        dsimp only [denominator, lionLiftedSquaredDistanceDenominator]
        linarith [standardSquaredDistance_nonneg center x]
      constructor
      · rintro ⟨hxU, hxlevel⟩
        have hmul : eta * denominator x ≤ delta x := by
          exact (le_div_iff₀ hdenPos).mp hxlevel
        refine ⟨⟨hxU, ?_⟩, hmul⟩
        exact (mul_le_mul_of_nonneg_left hheightLe (le_of_lt heta)).trans hmul
      · rintro ⟨⟨hxU, _hxthreshold⟩, hmul⟩
        exact ⟨hxU, (le_div_iff₀ hdenPos).mpr hmul⟩
    rw [heq]
    exact hcompact.inter_right hclosed

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q : ℕ}

/-- The radial carpet is a carpet on the original leaf, not only on its
associated open set. -/
theorem lionRadialCarpet_isCarpetOn_carrier
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    IsLionCarpetOn L.carrier
      (lionRadialCarpet L.delta center height) := by
  have hU : IsLionCarpetOn L.U
      (lionRadialCarpet L.delta center height) :=
    L.isCarpet.of_lionRadialCarpet
      (L.carpet_contDiff hsmooth).continuous center hheight
  have hclosed : IsClosed
      (L.equations ⁻¹' {(0 : RealEuclidean q)}) :=
    isClosed_singleton.preimage (L.equations_contDiff hsmooth).continuous
  rw [L.carrier_eq_inter_preimage_zero]
  exact hU.inter_closed hclosed

/-- Re-carpet a leaf by Lion's parameter-dependent radial denominator.  The
open set, equations, and hence the represented leaf are unchanged. -/
def radialized
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    LionCarpetedLeaf G n q where
  U := L.U
  isOpen_U := L.isOpen_U
  delta := lionRadialCarpet L.delta center height
  isCarpet := L.isCarpet.of_lionRadialCarpet
    (L.carpet_contDiff hsmooth).continuous center hheight
  delta_mem := hG.lionRadialCarpet_mem L.delta_mem center hheight
  equations := L.equations
  equations_mem := L.equations_mem
  fderiv_surjective := L.fderiv_surjective

@[simp]
theorem radialized_U
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    (L.radialized hG hsmooth center hheight).U = L.U :=
  rfl

@[simp]
theorem radialized_delta
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    (L.radialized hG hsmooth center hheight).delta =
      lionRadialCarpet L.delta center height :=
  rfl

@[simp]
theorem radialized_carrier
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    (L.radialized hG hsmooth center hheight).carrier = L.carrier :=
  rfl

@[simp]
theorem radialized_regularityMinorSum
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p) :
    (L.radialized hG hsmooth center hheight).regularityMinorSum g =
      L.regularityMinorSum g :=
  rfl

@[simp]
theorem radialized_regularLocus
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p) :
    (L.radialized hG hsmooth center hheight).regularLocus g =
      L.regularLocus g :=
  rfl

/-- The second denominator in Lion's Lemma 4 is strictly positive. -/
theorem one_add_regularityMinorSum_pos
    (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) (x : RealEuclidean n) :
    0 < 1 + L.regularityMinorSum g x := by
  linarith [L.regularityMinorSum_nonneg g x]

/-- Lion's Lemma 4 carpet on the regular locus:
`delta'_a = delta_a * thetaNorm / (1 + thetaNorm)`. -/
def criticalCarpet
    (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) :
    RealEuclideanFunction n :=
  fun x ↦ lionRadialCarpet L.delta center height x *
    L.regularityMinorSum g x / (1 + L.regularityMinorSum g x)

@[simp]
theorem criticalCarpet_apply
    (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) (x : RealEuclidean n) :
    L.criticalCarpet g center height x =
      lionRadialCarpet L.delta center height x *
        L.regularityMinorSum g x / (1 + L.regularityMinorSum g x) :=
  rfl

/-- The displayed Lemma 4 carpet is precisely Lemma 3's regular carpet
applied after the radial re-carpetting. -/
theorem criticalCarpet_eq_radialized_regularCarpet
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p) :
    L.criticalCarpet g center height =
      (L.radialized hG hsmooth center hheight).regularCarpet g := by
  funext x
  simp only [criticalCarpet, regularCarpet, regularityCarpetFactor,
    radialized_delta, radialized_regularityMinorSum]
  ring

/-- The exact `delta'_a` used in Lemma 4 stays in the geometric family. -/
theorem criticalCarpet_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    L.criticalCarpet g center height ∈ G n := by
  have hradial : lionRadialCarpet L.delta center height ∈ G n :=
    hG.lionRadialCarpet_mem L.delta_mem center hheight
  have hfactor : L.regularityCarpetFactor g ∈ G n :=
    L.regularityCarpetFactor_mem hG hderiv g hg
  have hproduct := hG.mul hradial hfactor
  convert hproduct using 1
  funext x
  simp only [criticalCarpet, regularityCarpetFactor, Pi.mul_apply]
  ring

/-- Source-faithful properness statement for Lemma 4: `delta'_a` carpets
the same Lemma 3 regular locus `U'`. -/
theorem criticalCarpet_isLionCarpetOn
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    IsLionCarpetOn (L.regularLocus g)
      (L.criticalCarpet g center height) := by
  let radial := L.radialized hG hsmooth center hheight
  have hcarpet := radial.regularCarpet_isLionCarpetOn
    hG hsmooth hderiv g hg
  simpa only [radial, radialized_regularLocus,
    ← L.criticalCarpet_eq_radialized_regularCarpet
      hG hsmooth center hheight g] using hcarpet

/-- The associated leaf on which Lemma 4 performs its critical-point
construction.  Its carpet is exactly `delta'_a`. -/
def criticalLeaf
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    LionCarpetedLeaf G n q :=
  (L.radialized hG hsmooth center hheight).regularLeaf
    hG hsmooth hderiv g hg

@[simp]
theorem criticalLeaf_U
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    (L.criticalLeaf hG hsmooth hderiv center hheight g hg).U =
      L.regularLocus g :=
  rfl

@[simp]
theorem criticalLeaf_delta
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    (L.criticalLeaf hG hsmooth hderiv center hheight g hg).delta =
      L.criticalCarpet g center height := by
  change (L.radialized hG hsmooth center hheight).regularCarpet g = _
  exact (L.criticalCarpet_eq_radialized_regularCarpet
    hG hsmooth center hheight g).symm

/-- The new leaf is exactly `X' = X ∩ U'`, the regular part of the
original leaf in Lion's Lemmas 3 and 4. -/
theorem criticalLeaf_carrier
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    (L.criticalLeaf hG hsmooth hderiv center hheight g hg).carrier =
      L.carrier ∩ L.regularLocus g := by
  exact (L.radialized hG hsmooth center hheight).regularLeaf_carrier_eq_inter_regularLocus
    hG hsmooth hderiv g hg

/-- The same `delta'_a` also carpets `X'`, the carrier of the regular leaf,
as asserted immediately before the critical-point construction in Lemma 4. -/
theorem criticalCarpet_isLionCarpetOn_regularCarrier
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    IsLionCarpetOn (L.carrier ∩ L.regularLocus g)
      (L.criticalCarpet g center height) := by
  let K := L.criticalLeaf hG hsmooth hderiv center hheight g hg
  have hclosed : IsClosed
      (K.equations ⁻¹' {(0 : RealEuclidean q)}) :=
    isClosed_singleton.preimage (K.equations_contDiff hsmooth).continuous
  have hcarrier : IsLionCarpetOn K.carrier K.delta := by
    rw [K.carrier_eq_inter_preimage_zero]
    exact K.isCarpet.inter_closed hclosed
  simpa only [K, criticalLeaf_carrier, criticalLeaf_delta] using hcarrier

end LionCarpetedLeaf

end AbelFormalization
