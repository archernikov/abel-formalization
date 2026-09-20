import AbelFormalization.LionRadialCriticalTraceRankSelection
import AbelFormalization.RectangularParametricRegularSlice
import AbelFormalization.LionTheorem7GenericBound

/-!
# Lion's radial parameter selection

The logarithmic Lagrange incidence family is a smooth joint submersion over
the regular locus and positive heights.  Rectangular parametric Sard selects
one positive-height radial parameter for which every fixed-parameter zero is
regular.  The critical-determinant row-selection theorem then gives the
finite regular-minor cover required in Lion's Lemma 4.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The derivative of a family with its parameter fixed is the first partial
of the full derivative. -/
theorem fderiv_fixedParameter_eq_fstPartial
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Phi : X × Y → Z) (x : X) (y : Y)
    (hPhi : DifferentiableAt ℝ Phi (x, y)) :
    fderiv ℝ (fun w : X ↦ Phi (w, y)) x =
      fstPartial (fderiv ℝ Phi (x, y)) := by
  let I : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
  have hins : HasFDerivAt (fun w : X ↦ (w, y)) I x :=
    hasFDerivAt_prodMk_left x y
  have hcomp := hPhi.hasFDerivAt.comp x hins
  have hcomp' : HasFDerivAt (fun w : X ↦ Phi (w, y))
      ((fderiv ℝ Phi (x, y)).comp I) x := by
    simpa only [Function.comp_def] using hcomp
  simpa only [fstPartial, I] using hcomp'.fderiv

namespace LionCarpetedLeaf

/-- Lion's logarithmic Lagrange incidence manifold admits a positive radial
parameter whose fixed slice is regular at every zero; consequently every
point of the critical trace has a regular critical-coefficient selection. -/
theorem exists_radialParameters_hasCriticalTraceRegularCoefficientSelection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {n q p : ℕ} (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hdim : p + q < n) :
    ∃ center : RealEuclidean n, ∃ height : ℝ, 0 < height ∧
      L.HasCriticalTraceRegularCoefficientSelection g center height := by
  let X := RealEuclidean n × RealEuclidean (q + p)
  let Y := RealEuclidean n × ℝ
  let Z := RealEuclidean n × RealEuclidean q
  let Phi : X × Y → Z := L.criticalTraceLogLagrangeFamily g
  let U : Set (X × Y) :=
    {z | z.1.1 ∈ L.regularLocus g ∧ 0 < z.2.2}
  let V : Set Y := {a | 0 < a.2}
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact ((L.regularLocus_isOpen hG hsmooth hderiv g hg).preimage
      (continuous_fst.fst)).inter
        (isOpen_lt continuous_const continuous_snd.snd)
  have hPhi : ContDiffOn ℝ ∞ Phi U := by
    intro z hz
    exact (L.contDiffAt_criticalTraceLogLagrangeFamily
      hG hsmooth hderiv g hg z.1.1 hz.1 z.1.2 z.2.1 hz.2).contDiffWithinAt
  have hsourceTargetDim : Module.finrank ℝ Z ≤ Module.finrank ℝ X := by
    dsimp only [X, Z]
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    omega
  have hPhiSurj : ∀ z ∈ U, (fderiv ℝ Phi z).range = ⊤ := by
    intro z hz
    apply LinearMap.range_eq_top.mpr
    exact L.criticalTraceLogLagrangeFamily_fderiv_surjective_of_mem_regularLocus
      hG hsmooth hderiv g hg z.1.1 hz.1 z.1.2 z.2.1 hz.2
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact isOpen_lt continuous_const continuous_snd
  have hVnonempty : V.Nonempty := by
    refine ⟨(0, 1), ?_⟩
    norm_num [V]
  obtain ⟨a, haV, hregular⟩ :=
    exists_parameter_mem_with_regular_fixed_slice_rectangular
      Phi U (0 : Z) hUopen hPhi hsourceTargetDim hPhiSurj
        V hVopen hVnonempty
  obtain ⟨center, height⟩ := a
  have hheight : 0 < height := haV
  refine ⟨center, height, hheight, ?_⟩
  intro x hx
  obtain ⟨lambda, hzero⟩ :=
    L.exists_lagrangeLift_mem_criticalTraceLogLagrangeFamily_zero
      hG hsmooth hderiv g hg center hheight hx
  have hpointU : (((x, lambda), (center, height)) : X × Y) ∈ U := by
    exact ⟨hx.1.2, hheight⟩
  have hpartialRange :
      (fstPartial (fderiv ℝ Phi ((x, lambda), (center, height)))).range = ⊤ :=
    hregular ((x, lambda), (center, height)) hpointU hzero rfl
  have hfullDiff : DifferentiableAt ℝ Phi ((x, lambda), (center, height)) :=
    (L.contDiffAt_criticalTraceLogLagrangeFamily
      hG hsmooth hderiv g hg x hx.1.2 lambda center hheight).differentiableAt
        (by simp)
  have hfixedRange :
      (fderiv ℝ
        (fun z : RealEuclidean n × RealEuclidean (q + p) ↦
          L.criticalTraceLogLagrangeFamily g
            (z, (center, height)))
        (x, lambda)).range = ⊤ := by
    rw [fderiv_fixedParameter_eq_fstPartial Phi
      (x, lambda) (center, height) hfullDiff]
    exact hpartialRange
  exact L.exists_criticalCoefficientSelection_of_fixedParameterLogLagrange_surjective
    hG hsmooth hderiv g hg center hheight hdim hx lambda hzero
      (LinearMap.range_eq_top.mp hfixedRange)

end LionCarpetedLeaf

/-- The radial parameter-selection input to Lion's generic-fiber induction
follows from the standing geometric, smoothness, and derivative-closure
hypotheses alone. -/
theorem hasLionLemma4RadialSelections
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G) :
    HasLionLemma4RadialSelections G := by
  intro n q p L g hg hdim
  exact L.exists_radialParameters_hasCriticalTraceRegularCoefficientSelection
    hG hsmooth hderiv g hg hdim

end AbelFormalization

