import AbelFormalization.LionGlobalSubmersionFixedSquare

/-!
# One fixed square map encoding globally submersive rectangular fibers

For a globally submersive smooth family map `g : ℝ^a → ℝ^k`, use its raw
component functions as the Lagrange constraints.  The center is chosen
separately at each fiber target, but the parameter-recording Lagrange square
map is fixed independently of that target.

Each connected component of a closed fiber contains a minimum of squared
distance to the chosen center.  Local connectedness of a regular level set
turns this into a constrained local minimum.  A Lagrange multiplier lifts it
to a point of the fixed square map's regular fiber, and the primal coordinate
of the lift determines the original connected component.  The existing
topological choice lemma therefore supplies an injection of components.

This covers globally submersive maps.  Singular rank strata remain outside
this statement.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## A componentwise minimum on a raw nonzero fiber -/

/-- A component minimum on a regular raw fiber is a local constrained
minimum for the unshifted component functions. -/
theorem componentMinimizer_isLocalMinOn_rawFiber
    {a k : ℕ} (g : RealEuclidean a → RealEuclidean k)
    (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i x, H i x = g x i)
    (t : RealEuclidean k) (rho : RealEuclideanFunction a)
    (x : g ⁻¹' {t})
    (hmin : x ∈ componentMinimizers
      (fun y : g ⁻¹' {t} ↦ rho (y : RealEuclidean a)))
    (hstrict : ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    IsLocalMinOn rho {y | ∀ i, H i y = H i x}
      (x : RealEuclidean a) := by
  have hxvalue : g (x : RealEuclidean a) = t := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using x.property
  have hlocalConstraint :
      ∃ V ∈ nhds (x : RealEuclidean a),
        V ∩ {y | ∀ i, H i y = H i x} ⊆ g ⁻¹' {t} := by
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    intro y hy
    change g y = t
    apply funext
    intro i
    calc
      g y i = H i y := (hH i y).symm
      _ = H i x := hy.2 i
      _ = g x i := hH i x
      _ = t i := congrFun hxvalue i
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

/-! ## The fixed-square injection -/

/-- A globally submersive map whose components lie in a smooth geometric
family closed under coordinate derivatives has one fixed square family map
encoding every fiber's connected components into a regular square fiber. -/
noncomputable def fixedSquareRegularFiberComponentEncoding_of_globalSubmersion
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (g : RealEuclidean a → RealEuclidean k)
    (hg : FunctionTupleInFamily G g)
    (hglob : ∀ x : RealEuclidean a,
      Function.Surjective (fderiv ℝ g x)) :
    FixedSquareRegularFiberComponentEncoding G g := by
  classical
  let H : Fin k → RealEuclideanFunction a := fun i x ↦ g x i
  have hHmem : ∀ i, H i ∈ G a := fun i ↦ hg i
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth a (H i) (hHmem i)
  have hH2 : ∀ i, ContDiff ℝ 2 (H i) :=
    fun i ↦ (hHinf i).of_le (by norm_num)
  have hgDiff : ContDiff ℝ 1 g := by
    rw [contDiff_pi]
    intro i
    exact (hHinf i).of_le (by norm_num)
  have hHrange : ∀ x : RealEuclidean a,
      (constraintFDeriv H x).range = ⊤ := by
    intro x
    have hcoordinate : ∀ i, DifferentiableAt ℝ (H i) x := by
      intro i
      exact (hHinf i).differentiable (by norm_num) |>.differentiableAt
    have hderivative : fderiv ℝ g x = constraintFDeriv H x := by
      change fderiv ℝ (constraintMap H) x = constraintFDeriv H x
      exact fderiv_pi hcoordinate
    rw [← hderivative]
    exact LinearMap.range_eq_top.mpr (hglob x)
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
  let center : RealEuclidean k → RealEuclidean a := fun t ↦
    Classical.choose
      (exists_center_regular_lagrangeCriticalSystem_at_target
        H hH2 hHrange t)
  have hcenter : ∀ t : RealEuclidean k,
      ∀ z : RealEuclidean (a + k),
        lagrangeCriticalSystemMap H
            (standardSquaredDistance (center t)) z =
          realEuclideanAppend (0 : RealEuclidean a) t →
        (fderiv ℝ (lagrangeCriticalSystemMap H
          (standardSquaredDistance (center t))) z).range = ⊤ := by
    intro t
    exact Classical.choose_spec
      (exists_center_regular_lagrangeCriticalSystem_at_target
        H hH2 hHrange t)
  let fiberTarget : RealEuclidean k → RealEuclidean ((a + k) + a) :=
    fun t ↦ realEuclideanAppend
      (realEuclideanAppend (0 : RealEuclidean a) t) (center t)
  have hpick : ∀ t : RealEuclidean k,
      ∃ pick : ConnectedComponents (g ⁻¹' {t}) →
          smoothRegularFiber squareMap (fiberTarget t),
        Function.Injective pick := by
    intro t
    let M : Set (RealEuclidean a) := g ⁻¹' {t}
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
    let base : smoothRegularFiber squareMap (fiberTarget t) → M :=
      fun v ↦ ⟨lagrangePrimalProjection a k
          (realEuclideanTakeLeft (v : RealEuclidean ((a + k) + a))), by
        have hv : squareMap
            (v : RealEuclidean ((a + k) + a)) = fiberTarget t :=
          v.property.1
        change g (lagrangePrimalProjection a k
          (realEuclideanTakeLeft (v : RealEuclidean ((a + k) + a)))) = t
        funext i
        have hcoordinate := congrFun hv
          (Fin.castAdd a (Fin.natAdd a i))
        simpa only [squareMap, fiberTarget,
          lagrangeParameterRecordingSquareMap_constraint,
          realEuclideanAppend_castAdd, realEuclideanAppend_natAdd]
          using hcoordinate⟩
    have hlift : ∀ x : M,
        x ∈ componentMinimizers
          (fun y : M ↦ rho (y : RealEuclidean a)) →
        ∃ v : smoothRegularFiber squareMap (fiberTarget t),
          base v = x := by
      intro x hmin
      have hlocal : IsLocalExtrOn rho
          {y | ∀ i, H i y = H i x} (x : RealEuclidean a) :=
        Or.inl (componentMinimizer_isLocalMinOn_rawFiber
          g H (fun _ _ ↦ rfl) t rho x hmin
          (hHstrict x) (hHrange x))
      obtain ⟨lambda, hstationarity⟩ :=
        exists_lagrangeStationarityCovector_eq_zero_of_isLocalExtrOn
          H rho x hlocal (hHstrict x) (hrhoStrict x) (hHrange x)
      have hxvalue : g (x : RealEuclidean a) = t := by
        simpa only [M, Set.mem_preimage, Set.mem_singleton_iff] using x.property
      have hfeasible : ∀ i, H i x = t i := by
        intro i
        exact congrFun hxvalue i
      let z : RealEuclidean (a + k) :=
        realEuclideanAppend (x : RealEuclidean a) lambda
      have hzsystem : lagrangeCriticalSystemMap H rho z =
          realEuclideanAppend (0 : RealEuclidean a) t :=
        (lagrangeCriticalSystemMap_append_eq_target_iff
          H rho (x : RealEuclidean a) lambda t).mpr
          ⟨hfeasible, hstationarity⟩
      let v : RealEuclidean ((a + k) + a) :=
        realEuclideanAppend z (center t)
      have hvvalue : squareMap v = fiberTarget t := by
        simpa only [squareMap, fiberTarget, v, rho,
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
          surjective_fderiv_flatParameterRecordingMap
            hfamilyAt hpartial
      have hvregular : v ∈ smoothRegularFiber squareMap
          (fiberTarget t) :=
        (mem_smoothRegularFiber_iff_of_contDiff_square
          squareMap hsquareC1 (fiberTarget t) v).mpr
          ⟨hvvalue, hvderiv⟩
      refine ⟨⟨v, hvregular⟩, ?_⟩
      apply Subtype.ext
      change lagrangePrimalProjection a k
          (realEuclideanTakeLeft v) =
        (x : RealEuclidean a)
      rw [show realEuclideanTakeLeft v = z by
        exact realEuclideanTakeLeft_append z (center t)]
      exact lagrangePrimalProjection_append (x : RealEuclidean a) lambda
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
  exact
    { dimension := (a + k) + a
      squareMap := squareMap
      fiberTarget := fiberTarget
      squareMap_mem := hsquareMem
      encode := fun t ↦ Classical.choose (hpick t)
      encode_injective := fun t ↦ Classical.choose_spec (hpick t) }

end AbelFormalization
