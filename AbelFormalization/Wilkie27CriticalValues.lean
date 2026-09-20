import AbelFormalization.CharbonnelSardianProjectionOneCoordinate
import AbelFormalization.MaxwellAutomaticFirstOrder

/-!
# Wilkie's critical-value smallness argument

For a smooth tuple belonging to the maintained Charbonnel family, the set of
critical values has empty interior.  The proof is Wilkie's selection argument:
continuous weak selection chooses a local section through the critical
incidence relation, Maxwell almost-everywhere smoothness makes that section
differentiable at one point, and the chain rule contradicts criticality.

This replaces the general rectangular Morse--Sard premise in the Sardian
projection constructor by the already established family-theoretic inputs.
-/

noncomputable section

open Set Function MeasureTheory
open scoped ContDiff MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## The differential contradiction -/

/-- A differentiable local right inverse forces the outer derivative to be
surjective.  Only equality on an open neighborhood of the base point is
needed. -/
theorem fderiv_surjective_along_differentiable_section
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (U : Set F) (hUopen : IsOpen U)
    (φ : F → E)
    (hsection : ∀ y ∈ U, g (φ y) = y)
    {y : F} (hy : y ∈ U)
    (hφdiff : DifferentiableAt ℝ φ y)
    (hgdiff : DifferentiableAt ℝ g (φ y)) :
    Function.Surjective (fderiv ℝ g (φ y)) := by
  have heventually : (g ∘ φ) =ᶠ[𝓝 y] id := by
    filter_upwards [hUopen.mem_nhds hy] with z hz
    exact hsection z hz
  have hchain := fderiv_comp (x := y) hgdiff hφdiff
  have hrightInverse :
      (fderiv ℝ g (φ y)).comp (fderiv ℝ φ y) =
        ContinuousLinearMap.id ℝ F := by
    calc
      (fderiv ℝ g (φ y)).comp (fderiv ℝ φ y) =
          fderiv ℝ (g ∘ φ) y := hchain.symm
      _ = fderiv ℝ id y := heventually.fderiv_eq
      _ = ContinuousLinearMap.id ℝ F := fderiv_id
  intro v
  refine ⟨fderiv ℝ φ y v, ?_⟩
  have hv := congrArg (fun L : F →L[ℝ] F ↦ L v) hrightInverse
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using hv

/-! ## The critical incidence belongs to the family -/

/-- The full `(value,source)` critical incidence is itself a literal zero
set, hence a member of the Charbonnel closure in positive arity. -/
theorem standardJacobianCriticalIncidenceSet_mem_literalZeroCharbonnel
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (hb : 0 < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    standardJacobianCriticalIncidenceSet g ∈
      charbonnelClosure (literalZeroSetFamily G) (b + a) := by
  have hbase : standardJacobianCriticalIncidenceSet g ∈
      literalZeroSetFamily G (b + a) := by
    exact ⟨standardJacobianCriticalValueResidual g,
      standardJacobianCriticalValueResidual_mem hG hderiv g hg, rfl⟩
  exact mem_charbonnelClosure_of_mem (by omega) hbase

/-! ## Wilkie 2.7 for family tuples -/

/-- Wilkie's weak-selection proof that a smooth family tuple has no open set
of critical values. -/
theorem standardJacobianCriticalValueSet_interior_eq_empty_of_charbonnel
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure (literalZeroSetFamily G)))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure (literalZeroSetFamily G)))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    interior (standardJacobianCriticalValueSet g) = ∅ := by
  by_contra hne
  have hinterior :
      (interior (standardJacobianCriticalValueSet g)).Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨e₀, r, hr, hball⟩ :=
    exists_openBall_subset_of_interior_nonempty hinterior
  let B : Set (RealEuclidean b) := Metric.ball e₀ r
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBnonempty : B.Nonempty := ⟨e₀, Metric.mem_ball_self hr⟩
  have hBmem : B ∈ charbonnelClosure (literalZeroSetFamily G) b :=
    hC.ws2_polynomialSign hb (polynomialSignConstructible_ball e₀ hr)
  have hRmem : standardJacobianCriticalIncidenceSet g ∈
      charbonnelClosure (literalZeroSetFamily G) (b + a) :=
    standardJacobianCriticalIncidenceSet_mem_literalZeroCharbonnel
      hG hderiv hb g hg
  have hfull : MaxwellHasFullFibersOver B
      (standardJacobianCriticalIncidenceSet g) := by
    intro e he
    have hecritical : e ∈ standardJacobianCriticalValueSet g := hball he
    obtain ⟨x, hgxe, hminors⟩ :=
      (mem_standardJacobianCriticalValueSet_iff g e).1 hecritical
    refine ⟨x, ?_⟩
    change standardJacobianCriticalValueResidual g
      (realEuclideanAppend e x) = 0
    exact (standardJacobianCriticalValueResidual_append_eq_zero_iff
      g e x).2 ⟨hgxe, hminors⟩
  obtain ⟨s⟩ :=
    (maxwellContinuousWeakSelection_of_theorem21 hC h21)
      hb ha hBopen hBnonempty hBmem hRmem hfull
  obtain ⟨A, hAclosed, _hAmem, hAempty, hφsmooth⟩ :=
    (maxwellAlmostEverywhereSmoothness_of_charbonnel hC hmem h21 h22)
      1 hb ha s.U s.phi s.U_open s.U_mem s.graph_mem
  have hUnotSubset : ¬ s.U ⊆ A := by
    intro hsubset
    have hUint : s.U ⊆ interior A :=
      s.U_open.subset_interior_iff.mpr hsubset
    obtain ⟨y, hy⟩ := s.U_nonempty
    simpa [hAempty] using hUint hy
  obtain ⟨y, hyU, hyA⟩ := Set.not_subset.mp hUnotSubset
  have hφdiff : DifferentiableAt ℝ s.phi y :=
    (hφsmooth.contDiffAt
      ((s.U_open.sdiff hAclosed).mem_nhds ⟨hyU, hyA⟩))
      |>.differentiableAt (by norm_num)
  have hgdiff : Differentiable ℝ g := by
    rw [differentiable_pi]
    intro i
    exact (hsmooth a (fun x ↦ g x i) (hg i)).differentiable (by simp)
  have hsection : ∀ z ∈ s.U, g (s.phi z) = z := by
    intro z hz
    have hincidence : realEuclideanAppend z (s.phi z) ∈
        standardJacobianCriticalIncidenceSet g := by
      apply s.graph_subset
      exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
        s.U s.phi z (s.phi z)).2 ⟨hz, rfl⟩
    change standardJacobianCriticalValueResidual g
      (realEuclideanAppend z (s.phi z)) = 0 at hincidence
    exact (standardJacobianCriticalValueResidual_append_eq_zero_iff
      g z (s.phi z)).1 hincidence |>.1
  have hsurj : Function.Surjective (fderiv ℝ g (s.phi y)) :=
    fderiv_surjective_along_differentiable_section
      g s.U s.U_open s.phi hsection hyU hφdiff (hgdiff (s.phi y))
  have hincidence : realEuclideanAppend y (s.phi y) ∈
      standardJacobianCriticalIncidenceSet g := by
    apply s.graph_subset
    exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      s.U s.phi y (s.phi y)).2 ⟨hyU, rfl⟩
  change standardJacobianCriticalValueResidual g
    (realEuclideanAppend y (s.phi y)) = 0 at hincidence
  have hminors :=
    (standardJacobianCriticalValueResidual_append_eq_zero_iff
      g y (s.phi y)).1 hincidence |>.2
  obtain ⟨cols, hcols⟩ :=
    (fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
      (hgdiff (s.phi y))).1 hsurj
  exact hcols (hminors cols)

/-! ## Finite exact-depth Sardian families -/

/-- The exact-depth finite union of critical-value sets is null by Theorem
2.1 after applying the preceding empty-interior theorem to each tuple. -/
theorem CharbonnelFiniteSardianFamily.volume_exactDepthProjectionCriticalParameterSet_eq_zero_of_charbonnel
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure (literalZeroSetFamily G)))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure (literalZeroSetFamily G)))
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    volume (family.exactDepthProjectionCriticalParameterSet hG hsmooth) = 0 := by
  let exacts := sardianProjectionOldExactDepthList hG hsmooth family
  change volume {epsilon | ∃ exactOld ∈ exacts,
    epsilon ∈ standardJacobianCriticalValueSet
      (sardianProjectionOldTuple exactOld)} = 0
  induction exacts with
  | nil => simp
  | cons exactOld exacts ih =>
      have hset :
          {epsilon | ∃ other ∈ exactOld :: exacts,
            epsilon ∈ standardJacobianCriticalValueSet
              (sardianProjectionOldTuple other)} =
            standardJacobianCriticalValueSet
                (sardianProjectionOldTuple exactOld) ∪
              {epsilon | ∃ other ∈ exacts,
                epsilon ∈ standardJacobianCriticalValueSet
                  (sardianProjectionOldTuple other)} := by
        ext epsilon
        simp
      rw [hset]
      apply measure_union_null
      · have hcriticalMem :=
          standardJacobianCriticalValueSet_mem_literalZeroCharbonnel
            hG hderiv (by omega)
              (sardianProjectionOldTuple exactOld)
              (sardianProjectionOldTuple_inFamily hG exactOld)
        exact (h21 (by omega) hcriticalMem).1.mp
          (standardJacobianCriticalValueSet_interior_eq_empty_of_charbonnel
            hG hsmooth hderiv hC hmem h21 h22 (by omega) (by omega)
            (sardianProjectionOldTuple exactOld)
            (sardianProjectionOldTuple_inFamily hG exactOld))
      · exact ih

/-- Consequently the exact-depth bad parameter set has empty interior. -/
theorem CharbonnelFiniteSardianFamily.interior_exactDepthProjectionCriticalParameterSet_eq_empty_of_charbonnel
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure (literalZeroSetFamily G)))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure (literalZeroSetFamily G)))
    {order n K : ℕ}
    (family : CharbonnelFiniteSardianFamily
      G (order + 1) (n + 1) K) :
    interior (family.exactDepthProjectionCriticalParameterSet hG hsmooth) =
      ∅ :=
  (volume : Measure (RealEuclidean (K + 1))).interior_eq_empty_of_null
    (family.volume_exactDepthProjectionCriticalParameterSet_eq_zero_of_charbonnel
      hG hsmooth hderiv hC hmem h21 h22)

/-- For an Abel family, Wilkie 2.7 discharges the complete positive-hidden-
arity projection constructor using Theorems 2.1 and 2.2 already present in
the source pipeline. -/
theorem IsAbel.charbonnelSardianProjectionConstructorInput_of_theorems21_22
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f)))) :
    CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily f) := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))) :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  apply hf.charbonnelSardianProjectionConstructorInput_of_criticalValues
    hUFF h21 h22
  intro order n _horder _hn A old
  exact old.family.interior_exactDepthProjectionCriticalParameterSet_eq_empty_of_charbonnel
    hG hsmooth hderiv hC hmem h21 h22

end AbelFormalization
