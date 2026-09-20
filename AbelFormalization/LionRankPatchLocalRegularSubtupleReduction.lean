import AbelFormalization.LionRankPatchCanonicalLagrangeReduction
import AbelFormalization.LionFixedMinorConstantRankComponentEncoding

/-!
# Local regular-subtuple reduction for canonical rank/minor patches

This file isolates a sufficient geometric input in the canonical rank/minor
Lagrange reduction.  At each point of the concrete reciprocal/minor fiber, it
asks for a source-sized subtuple of the canonical equations whose differentials
are independent and whose local level set is contained in the full fiber.

A parametric Sard argument first gives a null set of bad squared-distance
centers for each subtuple.  Since the chart family is finite, one center works
simultaneously for every chart over a fixed patch and target.  Compact
componentwise distance minima, the local fiber presentation, and the ordinary
Lagrange multiplier theorem then construct the existing finite regular
Lagrange cover.

The local presentation property is strictly geometric: it mentions neither
centers nor multipliers nor regularity of an augmented critical system.  It is
not automatic for smooth geometric families.  For example, for `g(x) = x^3`
at target zero and the rank-zero patch, the canonical equations at `(0, 1)`
are `x^3 = 0`, `3*x^2 = 0`, and `u = 1`.  Only the last equation has nonzero
differential, and its local level set does not cut out `x = 0`.  Thus this
premise deliberately records a genuine regular-presentation restriction; the
theorems below do not claim the original cover assumption in full generality.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff MeasureTheory ENNReal

namespace AbelFormalization

set_option autoImplicit false

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem exists_null_badParameterSet_for_regular_fixedSlices
    (Phi : X × Y → Z) (S : Set (X × Y)) (z : Z)
    (hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hLevel : ∀ p ∈ S, Phi p = z)
    (hSurj : ∀ p ∈ S, (fderiv ℝ Phi p).range = ⊤) :
    ∃ bad : Set Y,
      μH[Module.finrank ℝ Y] bad = 0 ∧
      ∀ c ∉ bad, ∀ q ∈ S, q.2 = c →
        (fstPartial (fderiv ℝ Phi q)).range = ⊤ := by
  obtain ⟨T, hTcount, hTcover⟩ :=
    exists_countable_parametric_chart_cover Phi S hPhi hSurj
  let _ : Countable T := hTcount.to_subtype
  let chart : T → Y → X × Y := fun i ↦
    parametricLevelChart Phi i.1.1 (hPhi i.1.1 i.1.2) hdim
      (hSurj i.1.1 i.1.2)
  let projection : T → Y → Y := fun i y ↦ (chart i y).2
  let criticalDomain : T → Set Y := fun i ↦
    {y | y ∈ parametricChartParameterSet Phi i.1.1
          (hPhi i.1.1 i.1.2) hdim
          (hSurj i.1.1 i.1.2) ∧
        chart i y ∈ S ∧
        (fstPartial (fderiv ℝ Phi (chart i y))).range ≠ ⊤}
  let bad : Set Y := ⋃ i, projection i '' criticalDomain i
  have hbad : μH[Module.finrank ℝ Y] bad = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro i
    exact addHaar_image_criticalSet_eq_zero
      (μH[Module.finrank ℝ Y] : MeasureTheory.Measure Y)
      (fun y hy ↦ differentiableAt_parametricLevelChart_of_mem
        Phi i.1.1 (hPhi i.1.1 i.1.2) hdim
          (hSurj i.1.1 i.1.2) hy.1 |>.snd)
      (fun y hy ↦ parametricLevelProjection_det_eq_zero_of_mem
        Phi i.1.1 (hPhi i.1.1 i.1.2) hdim
          (hSurj i.1.1 i.1.2) hy.1
          (hSurj (chart i y) hy.2.1) hy.2.2)
  refine ⟨bad, hbad, ?_⟩
  intro c hc q hqS hqc
  by_contra hqBad
  let qs : S := ⟨q, hqS⟩
  obtain ⟨p, hpT, hqU⟩ := hTcover qs
  let i : T := ⟨p, hpT⟩
  have hlevel : Phi q = Phi p :=
    (hLevel q hqS).trans (hLevel p p.property).symm
  obtain ⟨y, hyParam, hyChart⟩ := exists_parametricLevelChart_parameter
    Phi p q (hPhi p p.property) hdim (hSurj p p.property) hlevel hqU
  have hchartEq : chart i y = q := by
    simpa only [chart, i] using hyChart
  have hyS : chart i y ∈ S := by
    rw [hchartEq]
    exact hqS
  have hyBad : (fstPartial (fderiv ℝ Phi (chart i y))).range ≠ ⊤ := by
    rw [hchartEq]
    exact hqBad
  apply hc
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  refine ⟨y, ⟨hyParam, hyS, hyBad⟩, ?_⟩
  change (chart i y).2 = c
  rw [hchartEq, hqc]

theorem exists_null_badCenters_regular_lagrangeCriticalSystem_at_target_on_regularLocus
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i, ContDiff ℝ 2 (H i))
    (t : RealEuclidean k) :
    ∃ bad : Set (RealEuclidean a),
      μH[Module.finrank ℝ (RealEuclidean a)] bad = 0 ∧
      ∀ center ∉ bad, ∀ z : RealEuclidean (a + k),
        lagrangeCriticalSystemMap H
            (standardSquaredDistance center) z =
          realEuclideanAppend (0 : RealEuclidean a) t →
        (constraintFDeriv H
          (lagrangePrimalProjection a k z)).range = ⊤ →
        (fderiv ℝ (lagrangeCriticalSystemMap H
          (standardSquaredDistance center)) z).range = ⊤ := by
  let Phi := lagrangeSquaredDistanceCriticalFamily H
  let target : RealEuclidean (a + k) :=
    realEuclideanAppend (0 : RealEuclidean a) t
  let S : Set (RealEuclidean (a + k) × RealEuclidean a) :=
    {p | Phi p = target ∧
      (constraintFDeriv H
        (lagrangePrimalProjection a k p.1)).range = ⊤}
  have hPhiGlobal : ContDiff ℝ 1 Phi :=
    contDiff_lagrangeSquaredDistanceCriticalFamily H hH
  have hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p := by
    intro p _hp
    exact hPhiGlobal.contDiffAt
  have hSurj : ∀ p ∈ S, (fderiv ℝ Phi p).range = ⊤ := by
    intro p hp
    exact lagrangeSquaredDistanceCriticalFamily_fderiv_range_eq_top
      H p.1 p.2
      (hPhiGlobal.differentiable (by norm_num) p)
      (fun i ↦ ((hH i).differentiable (by norm_num)).differentiableAt)
      hp.2
  obtain ⟨bad, hbad, hgood⟩ :=
    exists_null_badParameterSet_for_regular_fixedSlices
    Phi S target hPhi rfl (fun p hp ↦ hp.1) hSurj
  refine ⟨bad, hbad, ?_⟩
  intro center hcenter z hz hregular
  have hzS : (z, center) ∈ S := by
    refine ⟨?_, hregular⟩
    change lagrangeCriticalSystemMap H
      (standardSquaredDistance center) z =
        realEuclideanAppend (0 : RealEuclidean a) t
    exact hz
  have hfixed := hgood center hcenter (z, center) hzS rfl
  have hfamily : DifferentiableAt ℝ Phi (z, center) :=
    (hPhiGlobal.differentiable (by norm_num)).differentiableAt
  rw [fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
    H z center hfamily]
  exact hfixed

theorem exists_commonCenter_regular_rankMinorLagrangeCharts_on_regularLocus
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
    (hH : ∀ (chart : RankMinorLagrangeChartIndex a b i) j,
      ContDiff ℝ 2 (rankMinorPatchLagrangeSubtuple g i chart j)) :
    ∃ center : RealEuclidean (a + 1),
      ∀ (chart : RankMinorLagrangeChartIndex a b i)
        (z : RealEuclidean ((a + 1) + (chart.1 : ℕ))),
        lagrangeCriticalSystemMap
            (rankMinorPatchLagrangeSubtuple g i chart)
            (standardSquaredDistance center) z =
          realEuclideanAppend (0 : RealEuclidean (a + 1))
            (rankMinorPatchLagrangeSubtarget i t chart) →
        (constraintFDeriv
          (rankMinorPatchLagrangeSubtuple g i chart)
          (lagrangePrimalProjection (a + 1) (chart.1 : ℕ) z)).range = ⊤ →
        (fderiv ℝ (lagrangeCriticalSystemMap
          (rankMinorPatchLagrangeSubtuple g i chart)
          (standardSquaredDistance center)) z).range = ⊤ := by
  classical
  let badData := fun chart : RankMinorLagrangeChartIndex a b i ↦
    exists_null_badCenters_regular_lagrangeCriticalSystem_at_target_on_regularLocus
      (rankMinorPatchLagrangeSubtuple g i chart) (hH chart)
      (rankMinorPatchLagrangeSubtarget i t chart)
  let bad : RankMinorLagrangeChartIndex a b i →
      Set (RealEuclidean (a + 1)) := fun chart ↦
    Classical.choose (badData chart)
  have hbad : ∀ chart,
      μH[Module.finrank ℝ (RealEuclidean (a + 1))] (bad chart) = 0 := by
    intro chart
    exact (Classical.choose_spec (badData chart)).1
  let allBad : Set (RealEuclidean (a + 1)) := ⋃ chart, bad chart
  have hallBad :
      μH[Module.finrank ℝ (RealEuclidean (a + 1))] allBad = 0 := by
    apply MeasureTheory.measure_iUnion_null
    exact hbad
  have hallBadNe : allBad ≠ Set.univ := by
    intro hbaduniv
    have hunivzero :
        μH[Module.finrank ℝ (RealEuclidean (a + 1))]
          (Set.univ : Set (RealEuclidean (a + 1))) = 0 := by
      simpa [hbaduniv] using hallBad
    exact (isOpen_univ.measure_ne_zero
      (μH[Module.finrank ℝ (RealEuclidean (a + 1))] :
        MeasureTheory.Measure (RealEuclidean (a + 1))) univ_nonempty)
      hunivzero
  obtain ⟨center, hcenter⟩ := Set.nonempty_compl.mpr hallBadNe
  refine ⟨center, ?_⟩
  intro chart z hz hregular
  have hcenterChart : center ∉ bad chart := by
    intro hc
    exact hcenter (Set.mem_iUnion.2 ⟨chart, hc⟩)
  exact (Classical.choose_spec (badData chart)).2
    center hcenterChart z hz hregular

/-- Every point of a canonical reciprocal/minor fiber has a locally defining
subtuple with independent differentials.

This is a sufficient regular-presentation hypothesis, not a consequence of
smoothness alone; the cubic rank-zero example in the module docstring fails
it. -/
def HasCanonicalRankMinorLocalRegularSubtuplePresentations
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) : Prop :=
  ∀ (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
    (x : constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
      {rankMinorPatchConstraintTarget i t}),
    ∃ chart : RankMinorLagrangeChartIndex a b i,
      (constraintFDeriv (rankMinorPatchLagrangeSubtuple g i chart)
        (x : RealEuclidean (a + 1))).range = ⊤ ∧
      ∃ V ∈ 𝓝 (x : RealEuclidean (a + 1)),
        V ∩ {y | ∀ j,
          rankMinorPatchLagrangeSubtuple g i chart j y =
            rankMinorPatchLagrangeSubtuple g i chart j x} ⊆
          constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
            {rankMinorPatchConstraintTarget i t}

/-- Family-level form of local regular subtuple presentation. -/
def HasCanonicalRankMinorLocalRegularSubtuplePresentationsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g →
      HasCanonicalRankMinorLocalRegularSubtuplePresentations g

/-- Local regular presentations of the canonical fiber suffice to construct
the finite regular-Lagrange cover required by the fixed-square reduction. -/
noncomputable def
    canonicalRankMinorFiniteRegularLagrangeCover_of_localRegularSubtuplePresentations
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (hlocal : HasCanonicalRankMinorLocalRegularSubtuplePresentations g) :
    CanonicalRankMinorFiniteRegularLagrangeCover g := by
  classical
  have hfullInf : ∀ (i : RankMinorPatchIndex a b) q,
      ContDiff ℝ ∞ (rankMinorPatchConstraintTuple g i q) := by
    intro i q
    exact hsmooth (a + 1) (rankMinorPatchConstraintTuple g i q)
      (hG.rankMinorPatchConstraintTuple_mem hderiv g hg i q)
  have hchartTwo : ∀ (i : RankMinorPatchIndex a b)
      (chart : RankMinorLagrangeChartIndex a b i) j,
      ContDiff ℝ 2 (rankMinorPatchLagrangeSubtuple g i chart j) := by
    intro i chart j
    exact (hfullInf i (chart.2 j)).of_le (by norm_num)
  let centerData := fun (i : RankMinorPatchIndex a b)
      (t : RealEuclidean b) ↦
    exists_commonCenter_regular_rankMinorLagrangeCharts_on_regularLocus
      g i t (hchartTwo i)
  let center : ∀ i : RankMinorPatchIndex a b,
      RankMinorLagrangeChartIndex a b i →
        RealEuclidean b → RealEuclidean (a + 1) :=
    fun i _chart t ↦ Classical.choose (centerData i t)
  have hcenter : ∀ (i : RankMinorPatchIndex a b)
      (t : RealEuclidean b)
      (chart : RankMinorLagrangeChartIndex a b i)
      (z : RealEuclidean ((a + 1) + (chart.1 : ℕ))),
      lagrangeCriticalSystemMap
          (rankMinorPatchLagrangeSubtuple g i chart)
          (standardSquaredDistance (center i chart t)) z =
        realEuclideanAppend (0 : RealEuclidean (a + 1))
          (rankMinorPatchLagrangeSubtarget i t chart) →
      (constraintFDeriv (rankMinorPatchLagrangeSubtuple g i chart)
        (lagrangePrimalProjection (a + 1) (chart.1 : ℕ) z)).range = ⊤ →
      (fderiv ℝ (lagrangeCriticalSystemMap
        (rankMinorPatchLagrangeSubtuple g i chart)
        (standardSquaredDistance (center i chart t))) z).range = ⊤ := by
    intro i t chart z hz hregular
    exact (Classical.choose_spec (centerData i t)) chart z
      (by simpa only [center] using hz) hregular
  refine
    { center := center
      component_lift := ?_ }
  intro i t x
  let fullH := rankMinorPatchConstraintTuple g i
  let fullTarget := rankMinorPatchConstraintTarget i t
  let M : Set (RealEuclidean (a + 1)) :=
    constraintMap fullH ⁻¹' {fullTarget}
  let commonCenter : RealEuclidean (a + 1) :=
    Classical.choose (centerData i t)
  let rho : RealEuclideanFunction (a + 1) :=
    standardSquaredDistance commonCenter
  have hfullC1 : ContDiff ℝ 1 (constraintMap fullH) := by
    rw [contDiff_pi]
    intro q
    exact (hfullInf i q).of_le (by norm_num)
  have hMclosed : IsClosed M :=
    isClosed_singleton.preimage hfullC1.continuous
  have hrhoMem : rho ∈ G (a + 1) := by
    simpa only [rho, standardSquaredDistance] using
      hG.standardSquaredDistance_mem commonCenter
  have hrhoInf : ContDiff ℝ ∞ rho :=
    hsmooth (a + 1) rho hrhoMem
  have hrhoStrict : ∀ y : RealEuclidean (a + 1),
      HasStrictFDerivAt rho (fderiv ℝ rho y) y := by
    intro y
    exact hrhoInf.contDiffAt.hasStrictFDerivAt (by norm_num)
  have hcompact : ∀ R : ℝ,
      IsCompact {y : M | rho (y : RealEuclidean (a + 1)) ≤ R} := by
    intro R
    apply isCompact_subtype_sublevel_of_isClosed hMclosed rho
    intro c
    simpa only [rho, standardSquaredDistance] using
      isCompact_algebraicSquaredDistance_basis_sublevel
        (Pi.basisFun ℝ (Fin (a + 1))) commonCenter c
  have hxM : (x : RealEuclidean (a + 1)) ∈ M := by
    exact x.property
  let xx : M := ⟨(x : RealEuclidean (a + 1)), hxM⟩
  obtain ⟨y, hycomponent, hymin⟩ :=
    exists_componentMinimizer_of_compact_sublevel
      (fun y : M ↦ rho (y : RealEuclidean (a + 1)))
      (hrhoInf.continuous.comp continuous_subtype_val)
      hcompact xx
  obtain ⟨chart, hHsurj, hlocalConstraint⟩ :=
    hlocal i t ⟨(y : RealEuclidean (a + 1)), y.property⟩
  let H := rankMinorPatchLagrangeSubtuple g i chart
  have hHinf : ∀ j, ContDiff ℝ ∞ (H j) := by
    intro j
    exact hfullInf i (chart.2 j)
  have hHstrict : ∀ j, HasStrictFDerivAt
      (H j) (fderiv ℝ (H j) y) y := by
    intro j
    exact (hHinf j).contDiffAt.hasStrictFDerivAt (by norm_num)
  have hlocalMin : IsLocalMinOn rho
      {w | ∀ j, H j w = H j y} (y : RealEuclidean (a + 1)) := by
    apply componentMinimizer_isLocalMinOn_of_localConstraintFiber
      (constraintMap fullH) H fullTarget rho y hymin hHstrict
    · simpa only [H] using hHsurj
    · simpa only [M, fullH, fullTarget, H] using hlocalConstraint
  obtain ⟨lambda, hstationarity⟩ :=
    exists_lagrangeStationarityCovector_eq_zero_of_isLocalExtrOn
      H rho (y : RealEuclidean (a + 1)) (Or.inl hlocalMin)
      hHstrict (hrhoStrict y) (by simpa only [H] using hHsurj)
  have hyvalue : constraintMap fullH (y : RealEuclidean (a + 1)) =
      fullTarget := by
    simpa only [M, Set.mem_preimage, Set.mem_singleton_iff] using y.property
  have hfeasible : ∀ j, H j y =
      rankMinorPatchLagrangeSubtarget i t chart j := by
    intro j
    have hj := congrFun hyvalue (chart.2 j)
    simpa only [H, fullH, fullTarget, constraintMap,
      rankMinorPatchLagrangeSubtuple,
      rankMinorPatchLagrangeSubtarget] using hj
  let z : RealEuclidean ((a + 1) + (chart.1 : ℕ)) :=
    realEuclideanAppend (y : RealEuclidean (a + 1)) lambda
  have hzsystem : lagrangeCriticalSystemMap H rho z =
      realEuclideanAppend (0 : RealEuclidean (a + 1))
        (rankMinorPatchLagrangeSubtarget i t chart) :=
    (lagrangeCriticalSystemMap_append_eq_target_iff
      H rho (y : RealEuclidean (a + 1)) lambda
        (rankMinorPatchLagrangeSubtarget i t chart)).mpr
      ⟨hfeasible, hstationarity⟩
  have hzregular : (fderiv ℝ (lagrangeCriticalSystemMap H rho) z).range = ⊤ := by
    apply hcenter i t chart z
    · simpa only [H, rho, commonCenter, center] using hzsystem
    · have hprimal : lagrangePrimalProjection (a + 1)
          (chart.1 : ℕ) z = (y : RealEuclidean (a + 1)) := by
        exact lagrangePrimalProjection_append
          (y : RealEuclidean (a + 1)) lambda
      rw [hprimal]
      simpa only [H] using hHsurj
  refine ⟨chart, ⟨(y : RealEuclidean (a + 1)), y.property⟩,
    lambda, ?_, ?_, ?_⟩
  · simpa only [xx] using hycomponent
  · simpa only [H, z, rho, commonCenter, center] using hzsystem
  · simpa only [H, z, rho, commonCenter, center] using hzregular

/-- Family-level adapter from local regular canonical presentations to the
finite regular-Lagrange covers used by the rank/minor reduction. -/
theorem hasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily_of_localRegularSubtuplePresentations
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hlocal : HasCanonicalRankMinorLocalRegularSubtuplePresentationsForFamily G) :
    HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily G := by
  intro a b g hg
  exact ⟨canonicalRankMinorFiniteRegularLagrangeCover_of_localRegularSubtuplePresentations
    hG hsmooth hderiv g hg (hlocal a b g hg)⟩

end AbelFormalization
