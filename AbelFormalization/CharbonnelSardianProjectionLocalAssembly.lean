import AbelFormalization.CharbonnelSardianProjectionFamilyBoundaryScale
import AbelFormalization.CharbonnelModulusFirstReparameterization
import AbelFormalization.CharbonnelSardianProjectionCompactUniformization
import AbelFormalization.MaxwellCompactComponentMembership

/-!
# Complete local geometric assembly for Sardian projection

Given one modulus on which every exact-depth old tuple level is regular,
this file performs Wilkie's full local projection argument: it refines the
modulus along the compact boundary scale, uses the old from-above clause to
select a constituent and a nonempty localized fiber, rules out full
projection, applies the bounded-or-radial dichotomy, and inserts the selected
piece into the padded projected finite family.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A regular-value refinement of the old modulus supplies the complete
one-coordinate Sardian projection certificate. -/
noncomputable def
    sardianProjectionCertificate_of_regularModulus
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    {order n : ℕ} (horder : 0 < order) (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      (abelGeometricFamily f) (order + 1) (n + 1) A)
    (regularModulus : CharbonnelModulus
      (old.commonHiddenArity + 1))
    (hregularRefines : regularModulus.Refines old.modulus)
    (hregular :
      ∀ epsilon : RealEuclidean
          ((old.commonHiddenArity + 1) + 1),
        regularModulus.IsBounded epsilon →
          ∀ exactOld ∈
              sardianProjectionOldExactDepthList
                hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                old.family,
            ∀ v : RealEuclidean
                (n + (old.commonHiddenArity + 1)),
              sardianProjectionOldTuple exactOld v =
                  CharbonnelModulus.parameterTail epsilon →
                Function.Surjective
                  (fderiv ℝ
                    (sardianProjectionOldTuple exactOld) v)) :
    CharbonnelSardianApproximationCertificate
      (abelGeometricFamily f) order n
      (realEuclideanExistentialProjection A) := by
  classical
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  let initialBound : ℝ := regularModulus.initialErrorBound
  have hinitialBound : 0 < initialBound :=
    regularModulus.initialErrorBound_pos
  let scale : ℝ → ℝ := fun r ↦
    sardianProjectionFiniteFamilyBoundaryScale
      hG hsmooth old initialBound hinitialBound r
  have hscalePos : ∀ r : ℝ, 0 < r → 0 < scale r := by
    intro r hr
    exact sardianProjectionFiniteFamilyBoundaryScale_pos
      hG hsmooth old hinitialBound hr
  have hscaleInitial : ∀ r : ℝ, 0 < r → scale r < initialBound := by
    intro r hr
    exact sardianProjectionFiniteFamilyBoundaryScale_lt_initial
      hG hsmooth old hinitialBound hr
  let prefixModulus : CharbonnelModulus
      (old.commonHiddenArity + 1) :=
    regularModulus.commonWithFirstPullback
      scale hscalePos initialBound hinitialBound
  have hprefixRefinesOld : prefixModulus.Refines old.modulus := by
    intro epsilon hepsilon
    have hregularBounded : regularModulus.IsBounded epsilon := by
      exact (CharbonnelModulus.isBounded_infimum_iff
        regularModulus
        (regularModulus.pullbackFirst
          scale hscalePos initialBound hinitialBound)
        epsilon).1 (by
          simpa only [prefixModulus,
            CharbonnelModulus.commonWithFirstPullback] using hepsilon) |>.1
    exact hregularRefines epsilon hregularBounded
  apply sardianProjectionCertificate_of_refinedLocalBoundarySmallLevels
    hG hsmooth hderiv horder hn old prefixModulus hprefixRefinesOld
  intro pfx hpfx z hz
  have hpfxBoth :=
    CharbonnelModulus.isBounded_commonWithFirstPullback
      scale hscalePos initialBound hinitialBound regularModulus
      (fun r hr _hrBound ↦ hscaleInitial r hr)
      pfx (by simpa only [prefixModulus] using hpfx)
  let modified :=
    charbonnelReparameterizeFirst scale pfx
  have hpfxRegular : regularModulus.IsBounded pfx := hpfxBoth.1
  have hmodifiedRegular : regularModulus.IsBounded modified := by
    simpa only [modified] using hpfxBoth.2
  have hmodifiedOld : old.modulus.IsBounded modified :=
    hregularRefines modified hmodifiedRegular
  have hr : 0 < pfx 0 := hpfxRegular.coord_pos 0
  have htail :
      CharbonnelModulus.parameterTail modified =
        CharbonnelModulus.parameterTail pfx := by
    funext i
    simp [modified, charbonnelReparameterizeFirst,
      CharbonnelModulus.parameterTail]
  obtain ⟨c, hcK, hzc, a, hidden, haBall, hfrontier,
      hnorm, hnotProjection⟩ :=
    (sardianProjectionFiniteFamilyBoundaryScale_spec
      hG hsmooth old hinitialBound hr hz)
  let U : Set (RealEuclidean n) := Metric.ball c (pfx 0 / 2)
  let V : Set (RealEuclidean n) := Metric.ball c (pfx 0 / 8)
  let oldPoint : RealEuclidean (n + 1) :=
    realEuclideanAppend a hidden
  have hmodifiedZero : modified 0 = scale (pfx 0) := by
    simp [modified]
  have hnormModified : ‖oldPoint‖ < (modified 0)⁻¹ := by
    simpa only [oldPoint, hmodifiedZero, scale] using hnorm
  obtain ⟨yOld, hyOldDist, hyOldCarrier⟩ :=
    old.approximates.approximatesBoundaryFromAbove
      modified hmodifiedOld oldPoint hfrontier hnormModified
  obtain ⟨piece, hpiece, hyPiece⟩ := hyOldCarrier
  let exactOld :=
    sardianConstituentExactDepthExtension
      hG hsmooth piece.hiddenArity_le piece.constituent
  have hexactOld :
      exactOld ∈ sardianProjectionOldExactDepthList
        hG hsmooth old.family := by
    change
      sardianConstituentExactDepthExtension
          hG hsmooth piece.hiddenArity_le piece.constituent ∈
        old.family.constituents.map
          (fun other ↦
            sardianConstituentExactDepthExtension
              hG hsmooth other.hiddenArity_le other.constituent)
    exact List.mem_map.mpr ⟨piece, hpiece, rfl⟩
  have hyExact :
      realEuclideanAppend yOld
          (CharbonnelModulus.parameterTail modified) ∈ exactOld.carrier := by
    rw [show exactOld.carrier =
        charbonnelParameterPad
          piece.hiddenArity_le piece.constituent.carrier by
      exact sardianConstituentExactDepthExtension_carrier_eq_pad
        hG hsmooth piece.hiddenArity_le piece.constituent]
    exact hyPiece
  let yVisible : RealEuclidean n := realEuclideanTakeLeft yOld
  let yErased : RealEuclidean 1 := realEuclideanTakeRight yOld
  have hyVisibleNear : dist yVisible a < scale (pfx 0) := by
    have htake :=
      dist_realEuclideanTakeLeft_le yOld oldPoint
    have htake' : dist yVisible a ≤ dist yOld oldPoint := by
      simpa only [yVisible, oldPoint,
        realEuclideanTakeLeft_append] using htake
    exact htake'.trans_lt
      (by simpa only [dist_comm, hmodifiedZero] using hyOldDist)
  have hyVisibleU : yVisible ∈ U := by
    change dist yVisible c < pfx 0 / 2
    calc
      dist yVisible c ≤ dist yVisible a + dist a c := dist_triangle _ _ _
      _ < pfx 0 / 8 + pfx 0 / 8 := by
        exact add_lt_add
          (hyVisibleNear.trans (by
            simpa only [scale] using
              (sardianProjectionFiniteFamilyBoundaryScale_lt_visible
                hG hsmooth old hinitialBound hr)))
          (Metric.mem_ball.mp haBall)
      _ < pfx 0 / 2 := by linarith
  have hySection :
      realEuclideanAppend (realEuclideanAppend yVisible yErased)
          (CharbonnelModulus.parameterTail modified) ∈ exactOld.carrier := by
    simpa only [yVisible, yErased, realEuclideanAppend_take] using hyExact
  have hfiberNonempty :
      (sardianProjectionOldTupleFiber exactOld U
        (CharbonnelModulus.parameterTail modified)).Nonempty :=
    oldTupleFiber_nonempty_of_append_mem_carrier
      exactOld U (CharbonnelModulus.parameterTail modified)
      hyVisibleU hySection
  have hUmem : U ∈
      charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f)) n := by
    exact ((polynomialSignConstructible_ball c (half_pos hr))
      |>.isProjectedZeroSet hG)
      |>.mem_literalZeroSet_charbonnelClosure hn
  have hUbounded : Bornology.IsBounded U := Metric.isBounded_ball
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconvex : Convex ℝ U := convex_ball c (pfx 0 / 2)
  have hepos : ∀ i,
      0 < CharbonnelModulus.parameterTail modified i := by
    intro i
    exact hmodifiedOld.coord_pos i.succ
  have htupleRegular :
      ∀ v, sardianProjectionOldTuple exactOld v =
          CharbonnelModulus.parameterTail modified →
        Function.Surjective
          (fderiv ℝ (sardianProjectionOldTuple exactOld) v) :=
    hregular modified hmodifiedRegular exactOld hexactOld
  have hnotProjection' :
      realEuclideanTakeLeft ''
          sardianProjectionOldTupleFiber exactOld U
            (CharbonnelModulus.parameterTail modified) ≠ U := by
    apply hnotProjection piece hpiece modified hmodifiedOld
    exact hmodifiedZero
  obtain ⟨eta, heta, hlevels⟩ :=
    sardianProjection_smallLevels_of_notProjection_bounded_or_radial
      hf hUFF hn exactOld U hUmem hUbounded h21 h22
      hUopen hUconvex
      (CharbonnelModulus.parameterTail modified) hepos
      htupleRegular hfiberNonempty hnotProjection'
  refine ⟨V, Metric.isOpen_ball, ?_, eta, heta, ?_⟩
  · exact hzc
  intro t ht hteta z' hz'
  obtain ⟨x, hxU, hxLevel⟩ := hlevels t ht hteta
  refine ⟨x, ?_, ?_⟩
  · have hz'c : dist z' c < pfx 0 / 8 :=
      Metric.mem_ball.mp hz'.2
    have hcx : dist c x < pfx 0 / 2 := by
      simpa only [dist_comm] using Metric.mem_ball.mp hxU
    exact (dist_triangle z' c x).trans_lt (by linarith)
  · have hpadded :
        realEuclideanAppend x
            (charbonnelAppendLastParameter
              (CharbonnelModulus.parameterTail modified) t) ∈
          (sardianProjectionAlgebraicPaddedFamily
            hG hsmooth hderiv hn old.family).carrier := by
      apply
        (mem_sardianProjectionAlgebraicFamilyOfExactList_carrier_iff
          hG hsmooth hderiv hn
          (sardianProjectionOldExactDepthList
            hG hsmooth old.family)).2
      exact ⟨exactOld, hexactOld, hxLevel⟩
    simpa only [htail] using hpadded

end AbelFormalization
