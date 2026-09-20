import AbelFormalization.LionGlobalSubmersionComponentEncoding
import AbelFormalization.SmoothFamilyConstantRankLocalFiber

/-!
# Fixed-square encodings under a global selected-minor rank bound

The globally-submersive encoding uses every output coordinate as a Lagrange
constraint.  This file treats a second, genuinely lower-rank regime.  We fix
`k` selected output coordinates and source columns such that their `k × k`
minor never vanishes, and assume the full derivative has rank at most `k`.
The selected map is then a global submersion, while the constant-rank lemma
shows locally that its fibers agree with the fibers of the full map.

The square map is fixed before the original target varies.  A square-fiber
point need not lie in the original fiber globally, so the component injection
uses a fallback base point.  The specifically constructed Lagrange lifts have
the correct primal point, which is all the component-choice argument needs.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Local minima from locally matching constraints -/

/-- A componentwise minimum becomes a local constrained minimum whenever the
constraint level is locally contained in the original fiber. -/
theorem componentMinimizer_isLocalMinOn_of_localConstraintFiber
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (H : Fin k → RealEuclideanFunction a)
    (t : RealEuclidean b) (rho : RealEuclideanFunction a)
    (x : g ⁻¹' {t})
    (hmin : x ∈ componentMinimizers
      (fun y : g ⁻¹' {t} ↦ rho (y : RealEuclidean a)))
    (hstrict : ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hlocalConstraint : ∃ V ∈ 𝓝 (x : RealEuclidean a),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ g ⁻¹' {t}) :
    IsLocalMinOn rho {y | ∀ i, H i y = H i x}
      (x : RealEuclidean a) := by
  obtain ⟨U, hU, hcomponent⟩ :=
    localConstraintFiber_of_surjectiveDerivative
      H x hstrict hsurj hlocalConstraint
  change IsMinOn
    (fun y : g ⁻¹' {t} ↦ rho (y : RealEuclidean a))
      (connectedComponent x) x at hmin
  rw [IsLocalMinOn]
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU,
    self_mem_nhdsWithin] with y hyU hyfiber
  obtain ⟨hyM, hycomponent⟩ := hcomponent y hyU hyfiber
  exact hmin hycomponent

/-- Under a fixed nonzero selected minor and a matching global rank bound, a
component minimum of a full fiber is a local minimum on the selected-output
constraint level. -/
theorem componentMinimizer_isLocalMinOn_selectedOutputFiber
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hg : ContDiff ℝ 1 g)
    (hminor : ∀ y, standardJacobianMinor g rows cols y ≠ 0)
    (hrank : ∀ y, Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k)
    (t : RealEuclidean b) (rho : RealEuclideanFunction a)
    (x : g ⁻¹' {t})
    (hmin : x ∈ componentMinimizers
      (fun y : g ⁻¹' {t} ↦ rho (y : RealEuclidean a)))
    (hstrict : ∀ i, HasStrictFDerivAt
      (fun y ↦ g y (rows i))
      (fderiv ℝ (fun y ↦ g y (rows i)) x) x)
    (hsurj : (constraintFDeriv (fun i y ↦ g y (rows i)) x).range = ⊤) :
    IsLocalMinOn rho {y | ∀ i, g y (rows i) = g x (rows i)}
      (x : RealEuclidean a) := by
  have hxvalue : g (x : RealEuclidean a) = t := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using x.property
  obtain ⟨U, hUopen, hxU, hfiber⟩ :=
    exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le
      hg (x : RealEuclidean a) rows cols (hminor x)
        (Filter.Eventually.of_forall hrank)
  have hlocalConstraint : ∃ V ∈ 𝓝 (x : RealEuclidean a),
      V ∩ {y | ∀ i, g y (rows i) = g x (rows i)} ⊆ g ⁻¹' {t} := by
    refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
    intro y hy
    have hselected : selectedOutputMap g rows y =
        selectedOutputMap g rows x := by
      funext i
      exact hy.2 i
    have hgy : g y = g x := hfiber y hy.1 x hxU hselected
    change g y = t
    exact hgy.trans hxvalue
  exact componentMinimizer_isLocalMinOn_of_localConstraintFiber
    g (fun i y ↦ g y (rows i)) t rho x hmin hstrict hsurj
      hlocalConstraint

/-! ## The fixed-square component encoding -/

/-- A family map with one everywhere nonzero selected `k × k` minor and
global derivative rank at most `k` has a fixed-square regular-fiber encoding
of every full fiber.  This includes constant-rank maps of nonmaximal rank
whenever one minor works globally. -/
noncomputable def
    fixedSquareRegularFiberComponentEncoding_of_fixedMinor_rank_le
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hminor : ∀ x, standardJacobianMinor g rows cols x ≠ 0)
    (hrank : ∀ x, Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap) ≤ k) :
    FixedSquareRegularFiberComponentEncoding G g := by
  classical
  let H : Fin k → RealEuclideanFunction a := fun i x ↦ g x (rows i)
  have hHmem : ∀ i, H i ∈ G a := fun i ↦ hg (rows i)
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth a (H i) (hHmem i)
  have hH2 : ∀ i, ContDiff ℝ 2 (H i) :=
    fun i ↦ (hHinf i).of_le (by norm_num)
  have hgDiff : ContDiff ℝ 1 g := by
    rw [contDiff_pi]
    intro i
    exact (hsmooth a (fun x ↦ g x i) (hg i)).of_le (by norm_num)
  have hHrange : ∀ x : RealEuclidean a,
      (constraintFDeriv H x).range = ⊤ := by
    intro x
    have hcoordinate : ∀ i, DifferentiableAt ℝ (H i) x := by
      intro i
      exact (hHinf i).differentiable (by norm_num) |>.differentiableAt
    have hderivative : fderiv ℝ (selectedOutputMap g rows) x =
        constraintFDeriv H x := by
      change fderiv ℝ (constraintMap H) x = constraintFDeriv H x
      exact fderiv_pi hcoordinate
    rw [← hderivative]
    exact LinearMap.range_eq_top.mpr
      (fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
        (hgDiff.differentiable (by norm_num) x) rows cols (hminor x))
  let squareMap : RealEuclidean ((a + k) + a) →
      RealEuclidean ((a + k) + a) :=
    lagrangeParameterRecordingSquareMap H
  have hsquareMem : FunctionTupleInFamily G squareMap :=
    hG.lagrangeParameterRecordingSquareMap_mem hderiv H hHmem
  have hfamilyC1 : ContDiff ℝ 1
      (lagrangeSquaredDistanceCriticalFamily H) :=
    contDiff_lagrangeSquaredDistanceCriticalFamily H hH2
  have hsquareC1 : ContDiff ℝ 1 squareMap :=
    contDiff_flatParameterRecordingMap hfamilyC1
  let selectedTarget : RealEuclidean b → RealEuclidean k :=
    fun t i ↦ t (rows i)
  let center : RealEuclidean b → RealEuclidean a := fun t ↦
    Classical.choose
      (exists_center_regular_lagrangeCriticalSystem_at_target
        H hH2 hHrange (selectedTarget t))
  have hcenter : ∀ t : RealEuclidean b,
      ∀ z : RealEuclidean (a + k),
        lagrangeCriticalSystemMap H
            (standardSquaredDistance (center t)) z =
          realEuclideanAppend (0 : RealEuclidean a) (selectedTarget t) →
        (fderiv ℝ (lagrangeCriticalSystemMap H
          (standardSquaredDistance (center t))) z).range = ⊤ := by
    intro t
    exact Classical.choose_spec
      (exists_center_regular_lagrangeCriticalSystem_at_target
        H hH2 hHrange (selectedTarget t))
  let fiberTarget : RealEuclidean b → RealEuclidean ((a + k) + a) :=
    fun t ↦ realEuclideanAppend
      (realEuclideanAppend (0 : RealEuclidean a) (selectedTarget t))
      (center t)
  have hpick : ∀ t : RealEuclidean b,
      ∃ pick : ConnectedComponents (g ⁻¹' {t}) →
          smoothRegularFiber squareMap (fiberTarget t),
        Function.Injective pick := by
    intro t
    let M : Set (RealEuclidean a) := g ⁻¹' {t}
    by_cases hM : M.Nonempty
    · let x0 : M := ⟨Classical.choose hM, Classical.choose_spec hM⟩
      let rho : RealEuclideanFunction a :=
        standardSquaredDistance (center t)
      have hMclosed : IsClosed M :=
        isClosed_singleton.preimage hgDiff.continuous
      have hrhoMem : rho ∈ G a := by
        simpa only [rho, standardSquaredDistance] using
          hG.standardSquaredDistance_mem (center t)
      have hrhoInf : ContDiff ℝ ∞ rho :=
        hsmooth a rho hrhoMem
      have hrhoStrict : ∀ x : RealEuclidean a,
          HasStrictFDerivAt rho (fderiv ℝ rho x) x := by
        intro x
        exact hrhoInf.contDiffAt.hasStrictFDerivAt (by norm_num)
      have hHstrict : ∀ x : RealEuclidean a,
          ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x := by
        intro x i
        exact (hHinf i).contDiffAt.hasStrictFDerivAt (by norm_num)
      have hcompact : ∀ R : ℝ,
          IsCompact {x : M | rho (x : RealEuclidean a) ≤ R} := by
        intro R
        apply isCompact_subtype_sublevel_of_isClosed hMclosed rho
        intro c
        simpa only [rho, standardSquaredDistance] using
          isCompact_algebraicSquaredDistance_basis_sublevel
            (Pi.basisFun ℝ (Fin a)) (center t) c
      let primal : smoothRegularFiber squareMap (fiberTarget t) →
          RealEuclidean a := fun v ↦
        lagrangePrimalProjection a k
          (realEuclideanTakeLeft (v : RealEuclidean ((a + k) + a)))
      let base : smoothRegularFiber squareMap (fiberTarget t) → M :=
        fun v ↦ if hv : primal v ∈ M then ⟨primal v, hv⟩ else x0
      have hlift : ∀ x : M,
          x ∈ componentMinimizers
            (fun y : M ↦ rho (y : RealEuclidean a)) →
          ∃ v : smoothRegularFiber squareMap (fiberTarget t),
            base v = x := by
        intro x hmin
        have hlocal : IsLocalExtrOn rho
            {y | ∀ i, H i y = H i x} (x : RealEuclidean a) :=
          Or.inl (componentMinimizer_isLocalMinOn_selectedOutputFiber
            g rows cols hgDiff hminor hrank t rho x hmin
            (by simpa only [H] using hHstrict x) (hHrange x))
        obtain ⟨lambda, hstationarity⟩ :=
          exists_lagrangeStationarityCovector_eq_zero_of_isLocalExtrOn
            H rho x hlocal (hHstrict x) (hrhoStrict x) (hHrange x)
        have hxvalue : g (x : RealEuclidean a) = t := by
          simpa only [M, Set.mem_preimage, Set.mem_singleton_iff] using x.property
        have hfeasible : ∀ i, H i x = selectedTarget t i := by
          intro i
          exact congrFun hxvalue (rows i)
        let z : RealEuclidean (a + k) :=
          realEuclideanAppend (x : RealEuclidean a) lambda
        have hzsystem : lagrangeCriticalSystemMap H rho z =
            realEuclideanAppend (0 : RealEuclidean a) (selectedTarget t) :=
          (lagrangeCriticalSystemMap_append_eq_target_iff
            H rho (x : RealEuclidean a) lambda (selectedTarget t)).mpr
            ⟨hfeasible, hstationarity⟩
        let v : RealEuclidean ((a + k) + a) :=
          realEuclideanAppend z (center t)
        have hvvalue : squareMap v = fiberTarget t := by
          simp only [squareMap, fiberTarget, v, rho,
            lagrangeParameterRecordingSquareMap_append, hzsystem]
        have hfamilyAt : DifferentiableAt ℝ
            (lagrangeSquaredDistanceCriticalFamily H) (z, center t) :=
          (hfamilyC1.differentiable (by norm_num)).differentiableAt
        have hpartial : Function.Surjective
            (fstPartial (fderiv ℝ
              (lagrangeSquaredDistanceCriticalFamily H) (z, center t))) := by
          rw [← fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
            H z (center t) hfamilyAt]
          exact LinearMap.range_eq_top.mp (by
            simpa only [rho] using hcenter t z (by
              simpa only [rho] using hzsystem))
        have hvderiv : Function.Surjective (fderiv ℝ squareMap v) := by
          simpa only [squareMap, lagrangeParameterRecordingSquareMap, v] using
            surjective_fderiv_flatParameterRecordingMap hfamilyAt hpartial
        have hvregular : v ∈ smoothRegularFiber squareMap
            (fiberTarget t) :=
          (mem_smoothRegularFiber_iff_of_contDiff_square
            squareMap hsquareC1 (fiberTarget t) v).mpr
            ⟨hvvalue, hvderiv⟩
        let vv : smoothRegularFiber squareMap (fiberTarget t) :=
          ⟨v, hvregular⟩
        have hprimal : primal vv = (x : RealEuclidean a) := by
          change lagrangePrimalProjection a k
              (realEuclideanTakeLeft v) = (x : RealEuclidean a)
          rw [show realEuclideanTakeLeft v = z by
            exact realEuclideanTakeLeft_append z (center t)]
          exact lagrangePrimalProjection_append (x : RealEuclidean a) lambda
        have hprimalM : primal vv ∈ M := by
          rw [hprimal]
          exact x.property
        refine ⟨vv, ?_⟩
        simp only [base, dite_eq_left hprimalM]
        exact Subtype.ext hprimal
      have hmeet : ∀ x : M,
          ∃ v : smoothRegularFiber squareMap (fiberTarget t),
            base v ∈ connectedComponent x := by
        intro x
        obtain ⟨y, hycomponent, hymin⟩ :=
          exists_componentMinimizer_of_compact_sublevel
            (fun y : M ↦ rho (y : RealEuclidean a))
            (hrhoInf.continuous.comp continuous_subtype_val)
            hcompact x
        obtain ⟨v, hvbase⟩ := hlift y hymin
        exact ⟨v, by simpa only [hvbase] using hycomponent⟩
      exact exists_injective_connectedComponents_to_lifts base hmeet
    · have hccFalse : ∀ c : ConnectedComponents M, False := by
        intro c
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        exact hM ⟨(x : RealEuclidean a), x.property⟩
      let pick : ConnectedComponents M →
          smoothRegularFiber squareMap (fiberTarget t) :=
        fun c ↦ (hccFalse c).elim
      refine ⟨pick, ?_⟩
      intro c
      exact (hccFalse c).elim
  exact
    { dimension := (a + k) + a
      squareMap := squareMap
      fiberTarget := fiberTarget
      squareMap_mem := hsquareMem
      encode := fun t ↦ Classical.choose (hpick t)
      encode_injective := fun t ↦ Classical.choose_spec (hpick t) }

/-- The fixed-minor rank-bound encoding converts a uniform square regular
fiber bound into one component bound valid for every target of `g`. -/
theorem exists_uniform_component_bound_of_fixedMinor_rank_le
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hregular : HasUniformSquareRegularFiberBound G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hminor : ∀ x, standardJacobianMinor g rows cols x ≠ 0)
    (hrank : ∀ x, Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap) ≤ k) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N := by
  exact
    (fixedSquareRegularFiberComponentEncoding_of_fixedMinor_rank_le
      hG hsmooth hderiv g hg rows cols hminor hrank).exists_uniform_component_bound
        hregular

end AbelFormalization
