import AbelFormalization.CharbonnelSection5LocalVerticalStability
import AbelFormalization.CharbonnelBoundedSourceComplementPipeline

/-!
# Source reductions for the remaining Charbonnel section 5 analytic step

`CharbonnelSection5AnalyticStep` packages two final consequences of sections
5.4--5.7.  This file removes the measure-theoretic and topological glue from
that residual.

For the compact conclusion, it is enough to construct the locally closed
exceptional base used in the finite/infinite-fibre split: fibres off that base
are finite, and interior of the base lifts to interior of the compact set.
Fubini and `P'_n` then prove the required positive-volume conclusion.

For bounded `Q_n`, it is enough to extract one neighbourhood carrying a
finite continuous graph description from any hypothetical interior point of
the positive zero trace.  Positivity of the last coordinate makes such a
chart disjoint from a neighbourhood of height zero, contradicting closure.

The final adapters rebuild the whole maintained analytic interface from these
two source-shaped hypotheses and feed it to the bounded source pipeline.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## The compact 5.4--5.6 fibre reduction -/

/-- The exceptional-base output needed from the geometric part of the compact
argument.  The source's finite/infinite-fibre split produces a locally closed
base.  Away from it the vertical fibres are finite; once that base has
interior, the preceding slab argument gives interior of the original set. -/
structure CharbonnelCompactExceptionalFiberBase
    (C : EuclideanSetFamily) {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) where
  base : Set (RealEuclidean n)
  base_mem : base ∈ C n
  base_locallyClosed : IsLocallyClosed base
  fiber_finite_off : ∀ x ∉ base, (charbonnelVerticalFiber S x).Finite
  interior_lift : (interior base).Nonempty → (interior S).Nonempty

/-- Family-wide availability of the exceptional-base reduction for compact
members.  It contains no measure conclusion and does not assume `P'_n`. -/
def CharbonnelSection56CompactFiberReduction
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ S : Set (RealEuclidean (n + 1)),
    IsCompact S → S ∈ C (n + 1) →
      Nonempty (CharbonnelCompactExceptionalFiberBase C S)

/-- The scalar product-coordinate equivalence preserves the measure of every
set, not only null sets. -/
theorem maxwellScalarRelationProductCoordinates_volume
    {p : ℕ} (S : Set (RealEuclidean (p + 1))) :
    (volume : Measure (RealEuclidean p × ℝ))
        (maxwellScalarRelationProductCoordinates S) =
      (volume : Measure (RealEuclidean (p + 1))) S := by
  let E := maxwellScalarRelationProductEquiv p
  rw [maxwellScalarRelationProductCoordinates,
    E.image_eq_preimage_symm]
  exact ((maxwellScalarRelationProductEquiv_measurePreserving p).symm E)
    |>.measure_preimage_equiv S

/-- The Fubini and `P'_n` part of 5.5--5.6.  All remaining information about
the compact set is concentrated in its exceptional-base witness. -/
theorem charbonnelCompactPositiveVolumeInterior_of_exceptionalFiberBase
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (hmem : CharbonnelSection5TraceMembership C)
    (hPPrime : CharbonnelPPrime C n)
    {S : Set (RealEuclidean (n + 1))}
    (hScompact : IsCompact S)
    (witness : CharbonnelCompactExceptionalFiberBase C S)
    (hSpositive : 0 < (volume : Measure (RealEuclidean (n + 1))) S) :
    (interior S).Nonempty := by
  let T : Set (RealEuclidean n × ℝ) :=
    maxwellScalarRelationProductCoordinates S
  have hTmeasurable : MeasurableSet T := by
    exact (maxwellScalarRelationProductEquiv n).measurableEmbedding
      |>.measurableSet_image' hScompact.measurableSet
  have hsection : ∀ x : RealEuclidean n,
      Prod.mk x ⁻¹' T = charbonnelVerticalFiber S x := by
    intro x
    ext t
    exact mem_maxwellScalarRelationProductCoordinates_iff S x t
  have hbaseNe :
      (volume : Measure (RealEuclidean n)) witness.base ≠ 0 := by
    intro hbaseNull
    have hTnull : (volume : Measure (RealEuclidean n × ℝ)) T = 0 := by
      apply volume_prod_eq_zero_of_base_eq_zero_of_sections_off
        hTmeasurable hbaseNull
      intro x hx
      rw [hsection x]
      exact (witness.fiber_finite_off x hx).measure_zero volume
    have hSnull :
        (volume : Measure (RealEuclidean (n + 1))) S = 0 := by
      rw [← maxwellScalarRelationProductCoordinates_volume S]
      exact hTnull
    exact (ne_of_gt hSpositive) hSnull
  apply witness.interior_lift
  apply Set.nonempty_iff_ne_empty.mpr
  intro hbaseEmpty
  have hclosureEmpty : interior (closure witness.base) = ∅ :=
    IsLocallyClosed.interior_closure_eq_empty
      witness.base_locallyClosed hbaseEmpty
  have hclosureMem : closure witness.base ∈ C n :=
    hmem.closure_mem hn witness.base_mem
  have hclosureNull :
      (volume : Measure (RealEuclidean n)) (closure witness.base) = 0 :=
    (hPPrime (closure witness.base) isClosed_closure hclosureMem).mpr
      hclosureEmpty
  have hbaseNull :
      (volume : Measure (RealEuclidean n)) witness.base = 0 :=
    measure_mono_null subset_closure hclosureNull
  exact hbaseNe hbaseNull

/-- The source-shaped compact-fibre reduction supplies the first field of
`CharbonnelSection5AnalyticStep`. -/
theorem charbonnelCompactPositiveVolumeInterior_of_section56FiberReduction
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hreduction : CharbonnelSection56CompactFiberReduction C) :
    ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
      CharbonnelCompactPositiveVolumeInterior C (n + 1) := by
  intro n hn hPPrime S hScompact hSmem hSpositive
  let witness := Classical.choice (hreduction hn S hScompact hSmem)
  exact charbonnelCompactPositiveVolumeInterior_of_exceptionalFiberBase
    hn hmem hPPrime hScompact witness hSpositive

/-! ## The bounded 5.7 graph reduction -/

/-- A finite continuous graph chart on a neighbourhood of `x`. -/
def CharbonnelFiniteVerticalGraphChartAt {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (x : RealEuclidean n) : Prop :=
  ∃ U : Set (RealEuclidean n), U ∈ 𝓝 x ∧
    CharbonnelFiniteContinuousVerticalGraphsOn S U

/-- A positive-last-coordinate set cannot have height zero in its closure at
a base point admitting a finite continuous graph chart. -/
theorem not_mem_charbonnelPositiveZeroTrace_of_finiteVerticalGraphChartAt
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hpositive : S ⊆ charbonnelPositiveLastCoordinateLocus n)
    {x : RealEuclidean n}
    (hchart : CharbonnelFiniteVerticalGraphChartAt S x) :
    x ∉ charbonnelPositiveZeroTrace S := by
  rintro hxTrace
  rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure hpositive] at hxTrace
  change charbonnelAppendLastCoordinate x 0 ∈ closure S at hxTrace
  rcases hchart with ⟨U, hU, M, f, hfContinuous, hfiber, _hpairwise⟩
  let z₀ : RealEuclidean (n + 1) := charbonnelAppendLastCoordinate x 0
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hbase_z₀ : charbonnelVerticalBaseCoordinate z₀ = x := by
    simp [z₀, charbonnelVerticalBaseCoordinate,
      charbonnelAppendLastCoordinate]
  have hlast_z₀ : charbonnelVerticalLastCoordinate z₀ = 0 := by
    simp [z₀, charbonnelVerticalLastCoordinate]
  have hbaseEventually :
      ∀ᶠ z in 𝓝 z₀, charbonnelVerticalBaseCoordinate z ∈ U := by
    have hpre := continuous_charbonnelVerticalBaseCoordinate.continuousAt
      |>.eventually_mem (show U ∈ 𝓝 (charbonnelVerticalBaseCoordinate z₀) by
        simpa only [hbase_z₀] using hU)
    exact hpre
  have hgraphAboveEventually :
      ∀ᶠ z in 𝓝 z₀, ∀ i : Fin M,
        charbonnelVerticalLastCoordinate z <
          f i (charbonnelVerticalBaseCoordinate z) := by
    rw [Filter.eventually_all]
    intro i
    have hfiMem : f i x ∈ charbonnelVerticalFiber S x := by
      rw [hfiber x hxU]
      exact mem_range_self i
    have hfiPositive : 0 < f i x := by
      have hzPositive := hpositive hfiMem
      simpa [charbonnelPositiveLastCoordinateLocus,
        charbonnelVerticalFiber] using hzPositive
    have hfiAt : ContinuousAt (f i) x :=
      (hfContinuous i x hxU).continuousAt hU
    have hfiComp : ContinuousAt
        (fun z : RealEuclidean (n + 1) ↦
          f i (charbonnelVerticalBaseCoordinate z)) z₀ := by
      exact hfiAt.comp_of_eq
        continuous_charbonnelVerticalBaseCoordinate.continuousAt hbase_z₀
    exact continuous_charbonnelVerticalLastCoordinate.continuousAt.eventually_lt
      hfiComp (by simpa only [hlast_z₀, hbase_z₀] using hfiPositive)
  have hneighborhood :
      {z : RealEuclidean (n + 1) |
        charbonnelVerticalBaseCoordinate z ∈ U ∧
        ∀ i : Fin M, charbonnelVerticalLastCoordinate z <
          f i (charbonnelVerticalBaseCoordinate z)} ∈ 𝓝 z₀ :=
    hbaseEventually.and hgraphAboveEventually
  obtain ⟨z, hzNear, hzS⟩ :=
    (mem_closure_iff_nhds.mp hxTrace) _ hneighborhood
  have hzFiber : charbonnelVerticalLastCoordinate z ∈
      charbonnelVerticalFiber S (charbonnelVerticalBaseCoordinate z) := by
    change charbonnelAppendLastCoordinate
      (charbonnelVerticalBaseCoordinate z)
        (charbonnelVerticalLastCoordinate z) ∈ S
    simpa only [charbonnelVerticalBaseCoordinate,
      charbonnelVerticalLastCoordinate,
      charbonnelAppendLastCoordinate_takeLeft_last] using hzS
  rw [hfiber (charbonnelVerticalBaseCoordinate z) hzNear.1] at hzFiber
  rcases hzFiber with ⟨i, hi⟩
  have hlt := hzNear.2 i
  exact (ne_of_lt hlt) hi.symm

/-- The exact remaining extraction in bounded 5.7: if the zero trace had
interior, the stabilized finite branches would give one finite continuous
graph chart at a point of that interior. -/
def CharbonnelSection57BoundedGraphReduction
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
    ∀ S : Set (RealEuclidean (n + 1)), S ∈ C (n + 1) →
      CharbonnelRelativelyClosedInPositiveLast S →
      Bornology.IsBounded S → interior S = ∅ →
      (interior (charbonnelPositiveZeroTrace S)).Nonempty →
        ∃ x ∈ interior (charbonnelPositiveZeroTrace S),
          CharbonnelFiniteVerticalGraphChartAt S x

/-- The graph extraction reduces the bounded conclusion of 5.7 to the local
topological obstruction above. -/
theorem charbonnelBoundedQ_of_section57GraphReduction
    {C : EuclideanSetFamily}
    (hreduction : CharbonnelSection57BoundedGraphReduction C) :
    ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
      CharbonnelBoundedQ C n := by
  intro n hn hPPrime S hSmem hrelative hbounded hSempty
  apply Set.not_nonempty_iff_eq_empty.mp
  intro htraceInterior
  obtain ⟨x, hxInterior, hchart⟩ :=
    hreduction hn hPPrime S hSmem hrelative hbounded hSempty
      htraceInterior
  exact
    (not_mem_charbonnelPositiveZeroTrace_of_finiteVerticalGraphChartAt
      hrelative.1 hchart) (interior_subset hxInterior)

/-! ## Reassembly and source-pipeline adapters -/

/-- The two source-shaped reductions reconstruct the whole analytic package.
The formerly abstract fields are now theorems. -/
theorem charbonnelSection5AnalyticStep_of_fiberAndGraphReductions
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hcompact : CharbonnelSection56CompactFiberReduction C)
    (hbounded : CharbonnelSection57BoundedGraphReduction C) :
    CharbonnelSection5AnalyticStep C where
  compactPositiveVolumeInterior_of_pPrime :=
    charbonnelCompactPositiveVolumeInterior_of_section56FiberReduction
      hmem hcompact
  boundedQ_of_pPrime :=
    charbonnelBoundedQ_of_section57GraphReduction hbounded

/-- Literal-zero specialization: all family-membership input is already
proved, so only the exceptional-base and graph-extraction statements remain. -/
theorem literalZeroSet_charbonnelClosure_section5AnalyticStep_of_fiberAndGraphReductions
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hcompact : CharbonnelSection56CompactFiberReduction
      (charbonnelClosure (literalZeroSetFamily G)))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)) :=
  charbonnelSection5AnalyticStep_of_fiberAndGraphReductions
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
    hcompact hbounded

/-- The bounded source endpoint with the section 5 residual replaced by the
two source-shaped fibre reductions. -/
theorem IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers_and_section5Reductions
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcompact : CharbonnelSection56CompactFiberReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
      hUFF hselection
      (literalZeroSet_charbonnelClosure_section5AnalyticStep_of_fiberAndGraphReductions
        hG hsmooth hcompact hbounded)
      hcells

end AbelFormalization
