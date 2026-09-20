import AbelFormalization.CharbonnelTraceMembership
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Charbonnel section 5 reduction for approximation traces

This file separates the formal content of Charbonnel's section 5 into the
three predicates used in the paper.

* `CharbonnelPPrime C n` is `P'_n`: a closed member of `C n` is Lebesgue
  null exactly when it has empty interior.
* `CharbonnelQ C n` is `Q_n`: a relatively closed member of the positive
  half-space with empty interior has an empty-interior zero trace.
* `CharbonnelP C n` is `P_n`: the closure of a member is null if the member
  is null or if its closure has empty interior.

The purely topological and measure-theoretic parts of the induction are
proved here.  In particular, the file supplies the compact-truncation/Baire
passage from bounded `Q_n` to unrestricted `Q_n`, the Fubini lemmas for
finite or null vertical fibers, and the logical passage from `P_n`, `Q_n`,
and the four-way conclusion of Charbonnel--Wilkie 2.1 to
`CharbonnelApproximationTraceSmallness`.

The difficult geometric step in Charbonnel 5.3--5.6 is not a consequence of
measurability and a per-set component bound.  It is therefore exposed below
as reusable propositions: uniform local vertical-component bounds, stable
local component counts, finite continuous vertical-graph decompositions, and
the compact positive-measure conclusion.  None of these propositions is
assumed globally in this file.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Vertical fibers and compact truncations -/

/-- The vertical fiber of `S` over `x`, with the last coordinate singled
out. -/
def charbonnelVerticalFiber {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (x : RealEuclidean n) : Set ℝ :=
  {t | charbonnelAppendLastCoordinate x t ∈ S}

/-- The set of last coordinates occurring above a base set `B`. -/
def charbonnelVerticalImageOver {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n)) : Set ℝ :=
  {t | ∃ x ∈ B, charbonnelAppendLastCoordinate x t ∈ S}

/-- Truncate a Euclidean set by the closed ball of integral radius `m`. -/
def charbonnelCompactTruncation {d : ℕ}
    (S : Set (RealEuclidean d)) (m : ℕ) : Set (RealEuclidean d) :=
  S ∩ Metric.closedBall 0 (m : ℝ)

theorem charbonnelCompactTruncation_subset {d : ℕ}
    (S : Set (RealEuclidean d)) (m : ℕ) :
    charbonnelCompactTruncation S m ⊆ S :=
  inter_subset_left

theorem charbonnelCompactTruncation_isBounded {d : ℕ}
    (S : Set (RealEuclidean d)) (m : ℕ) :
    Bornology.IsBounded (charbonnelCompactTruncation S m) :=
  Metric.isBounded_closedBall.subset inter_subset_right

theorem charbonnelCompactTruncation_isClosed {d : ℕ}
    {S : Set (RealEuclidean d)} (hS : IsClosed S) (m : ℕ) :
    IsClosed (charbonnelCompactTruncation S m) :=
  hS.inter Metric.isClosed_closedBall

theorem charbonnelCompactTruncation_isCompact {d : ℕ}
    {S : Set (RealEuclidean d)} (hS : IsClosed S) (m : ℕ) :
    IsCompact (charbonnelCompactTruncation S m) :=
  (isCompact_closedBall (0 : RealEuclidean d) (m : ℝ)).of_isClosed_subset
    (charbonnelCompactTruncation_isClosed hS m) inter_subset_right

theorem iUnion_charbonnelCompactTruncation {d : ℕ}
    (S : Set (RealEuclidean d)) :
    ⋃ m : ℕ, charbonnelCompactTruncation S m = S := by
  simpa only [charbonnelCompactTruncation] using
    (Metric.iUnion_inter_closedBall_nat S (0 : RealEuclidean d))

/-! ## General closure and Baire glue -/

/-- Intersecting with a neighborhood does not remove a point from the
closure. -/
theorem mem_closure_inter_of_mem_nhds
    {X : Type*} [TopologicalSpace X]
    {s t : Set X} {x : X} (ht : t ∈ 𝓝 x) (hx : x ∈ closure s) :
    x ∈ closure (s ∩ t) := by
  rw [mem_closure_iff_nhds] at hx ⊢
  intro u hu
  obtain ⟨y, hyut, hys⟩ := hx (u ∩ t) (inter_mem hu ht)
  exact ⟨y, hyut.1, hys, hyut.2⟩

/-- Integral closed balls give a closure exhaustion.  The closures on the
right are essential: closure does not commute with arbitrary countable
unions. -/
theorem closure_eq_iUnion_closure_charbonnelCompactTruncation {d : ℕ}
    (S : Set (RealEuclidean d)) :
    closure S = ⋃ m : ℕ, closure (charbonnelCompactTruncation S m) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨m, hm⟩ := exists_nat_gt (dist x (0 : RealEuclidean d))
    have hxball : x ∈ Metric.ball (0 : RealEuclidean d) (m : ℝ) :=
      Metric.mem_ball.mpr hm
    have hclosedBall : Metric.closedBall (0 : RealEuclidean d) (m : ℝ) ∈ 𝓝 x :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hxball)
        Metric.ball_subset_closedBall
    have hx' : x ∈ closure (charbonnelCompactTruncation S m) := by
      simpa only [charbonnelCompactTruncation] using
        (mem_closure_inter_of_mem_nhds hclosedBall hx)
    exact mem_iUnion.mpr ⟨m, hx'⟩
  · refine iUnion_subset fun m ↦ ?_
    exact closure_mono (charbonnelCompactTruncation_subset S m)

/-- A countable union of closed empty-interior sets has empty interior in a
Baire space. -/
theorem interior_iUnion_eq_empty_of_closed
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {F : ℕ → Set X}
    (hclosed : ∀ m, IsClosed (F m))
    (hempty : ∀ m, interior (F m) = ∅) :
    interior (⋃ m, F m) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hmeagre : IsMeagre (⋃ m, F m) :=
    isMeagre_iUnion fun m ↦
      ((hclosed m).isNowhereDense_iff.mpr (hempty m)).isMeagre
  exact not_isMeagre_of_isOpen isOpen_interior ⟨x, hx⟩
    (hmeagre.mono interior_subset)

/-- For a locally closed set, empty interior passes to the closure.  This is
the elementary topological observation used in Charbonnel 5.1. -/
theorem IsLocallyClosed.interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsLocallyClosed S) (hinterior : interior S = ∅) :
    interior (closure S) = ∅ := by
  obtain ⟨U, hUopen, hSU⟩ :=
    ((isLocallyClosed_tfae S).out 1 5).mp hS
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxclosure : x ∈ closure S := interior_subset hx
  rw [mem_closure_iff_nhds] at hxclosure
  obtain ⟨y, hyclosureInterior, hyS⟩ := hxclosure
    (interior (closure S)) (isOpen_interior.mem_nhds hx)
  have hyU : y ∈ U := by
    rw [hSU] at hyS
    exact hyS.1
  have hopen : IsOpen (U ∩ interior (closure S)) :=
    hUopen.inter isOpen_interior
  have hsubset : U ∩ interior (closure S) ⊆ S := by
    intro z hz
    rw [hSU]
    exact ⟨hz.1, interior_subset hz.2⟩
  have hyInterior : y ∈ interior S :=
    (hopen.subset_interior_iff.mpr hsubset)
      ⟨hyU, hyclosureInterior⟩
  rw [hinterior] at hyInterior
  exact hyInterior

/-! ## Zero sections -/

/-- The zero section of a set whose last coordinate is distinguished. -/
def charbonnelZeroSection {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Set (RealEuclidean n) :=
  {x | charbonnelAppendLastCoordinate x 0 ∈ S}

theorem continuous_charbonnelAppendLastCoordinate_zero {n : ℕ} :
    Continuous
      (fun x : RealEuclidean n ↦ charbonnelAppendLastCoordinate x 0) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using
      (continuous_const : Continuous (fun _ : RealEuclidean n ↦ (0 : ℝ)))
  · simpa using (continuous_apply j :
      Continuous (fun x : RealEuclidean n ↦ x j))

theorem charbonnelZeroSection_isClosed {n : ℕ}
    {S : Set (RealEuclidean (n + 1))} (hS : IsClosed S) :
    IsClosed (charbonnelZeroSection S) :=
  hS.preimage continuous_charbonnelAppendLastCoordinate_zero

theorem charbonnelZeroSection_iUnion {n : ℕ}
    (F : ℕ → Set (RealEuclidean (n + 1))) :
    charbonnelZeroSection (⋃ m, F m) =
      ⋃ m, charbonnelZeroSection (F m) := by
  ext x
  simp only [charbonnelZeroSection, mem_ofPred_eq, mem_iUnion]

theorem charbonnelZeroSection_closure_eq_iUnion_truncations {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    charbonnelZeroSection (closure S) =
      ⋃ m : ℕ,
        charbonnelZeroSection
          (closure (charbonnelCompactTruncation S m)) := by
  rw [closure_eq_iUnion_closure_charbonnelCompactTruncation,
    charbonnelZeroSection_iUnion]

/-- This is the Baire step at the end of Charbonnel 5.7. -/
theorem charbonnelZeroSection_closure_interior_eq_empty_of_truncations
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (htrunc : ∀ m : ℕ,
      interior (charbonnelZeroSection
        (closure (charbonnelCompactTruncation S m))) = ∅) :
    interior (charbonnelZeroSection (closure S)) = ∅ := by
  rw [charbonnelZeroSection_closure_eq_iUnion_truncations]
  exact interior_iUnion_eq_empty_of_closed
    (fun m ↦ charbonnelZeroSection_isClosed isClosed_closure) htrunc

/-! ## Fubini lemmas already supplied by mathlib -/

/-- A measurable product set is null when every vertical section is null. -/
theorem volume_prod_eq_zero_of_verticalSections_eq_zero {n : ℕ}
    {S : Set (RealEuclidean n × ℝ)} (hS : MeasurableSet S)
    (hsections : ∀ x : RealEuclidean n,
      (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0) :
    (volume : Measure (RealEuclidean n × ℝ)) S = 0 := by
  rw [Measure.volume_eq_prod]
  exact Measure.measure_prod_null_of_ae_null hS
    (Eventually.of_forall hsections)

/-- In particular, a measurable set with finite vertical fibers is null. -/
theorem volume_prod_eq_zero_of_finite_verticalSections {n : ℕ}
    {S : Set (RealEuclidean n × ℝ)} (hS : MeasurableSet S)
    (hfinite : ∀ x : RealEuclidean n, (Prod.mk x ⁻¹' S).Finite) :
    (volume : Measure (RealEuclidean n × ℝ)) S = 0 := by
  apply volume_prod_eq_zero_of_verticalSections_eq_zero hS
  intro x
  exact (hfinite x).measure_zero volume

/-- If the exceptional base is null and all fibers off it are null, the
whole measurable product set is null. -/
theorem volume_prod_eq_zero_of_base_eq_zero_of_sections_off {n : ℕ}
    {S : Set (RealEuclidean n × ℝ)} (hS : MeasurableSet S)
    {B : Set (RealEuclidean n)}
    (hB : (volume : Measure (RealEuclidean n)) B = 0)
    (hsections : ∀ x ∉ B, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0) :
    (volume : Measure (RealEuclidean n × ℝ)) S = 0 := by
  rw [Measure.volume_eq_prod]
  exact Measure.measure_prod_null_of_ae_null hS
    ((measure_eq_zero_iff_ae_notMem.mp hB).mono fun x hx ↦
      hsections x hx)

/-- Conversely, if every fiber above `B` has positive measure, nullity of
the product set forces nullity of `B`. -/
theorem volume_base_eq_zero_of_prod_eq_zero_of_sections_ne_zero {n : ℕ}
    {S : Set (RealEuclidean n × ℝ)} (hS : MeasurableSet S)
    {B : Set (RealEuclidean n)}
    (hsections : ∀ x ∈ B,
      (volume : Measure ℝ) (Prod.mk x ⁻¹' S) ≠ 0)
    (hSnull : (volume : Measure (RealEuclidean n × ℝ)) S = 0) :
    (volume : Measure (RealEuclidean n)) B = 0 := by
  rw [Measure.volume_eq_prod] at hSnull
  have hae := (Measure.measure_prod_null hS).mp hSnull
  have hbad : (volume : Measure (RealEuclidean n))
      {x | (volume : Measure ℝ) (Prod.mk x ⁻¹' S) ≠ 0} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact hae.mono fun x hx ↦ by simpa using hx
  exact measure_mono_null (fun x hx ↦ hsections x hx) hbad

/-- The Fubini equivalence used in Charbonnel 5.5. -/
theorem volume_prod_eq_zero_iff_base_eq_zero_of_fiber_dichotomy {n : ℕ}
    {S : Set (RealEuclidean n × ℝ)} (hS : MeasurableSet S)
    {B : Set (RealEuclidean n)}
    (hon : ∀ x ∈ B, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) ≠ 0)
    (hoff : ∀ x ∉ B, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0) :
    (volume : Measure (RealEuclidean n × ℝ)) S = 0 ↔
      (volume : Measure (RealEuclidean n)) B = 0 := by
  constructor
  · exact volume_base_eq_zero_of_prod_eq_zero_of_sections_ne_zero hS hon
  · intro hB
    exact volume_prod_eq_zero_of_base_eq_zero_of_sections_off hS hB hoff

/-! ## The exact `P'_n`, `Q_n`, and `P_n` predicates -/

/-- Charbonnel's `P'_n`. -/
def CharbonnelPPrime (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean n), IsClosed S → S ∈ C n →
    ((volume : Measure (RealEuclidean n)) S = 0 ↔ interior S = ∅)

/-- Relative closedness in `ℝⁿ × ℝ₊*`, expressed in the subtype topology. -/
def CharbonnelRelativelyClosedInPositiveLast {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  S ⊆ charbonnelPositiveLastCoordinateLocus n ∧
    IsClosed
      ((fun z : charbonnelPositiveLastCoordinateLocus n ↦
          (z : RealEuclidean (n + 1))) ⁻¹' S)

/-- Charbonnel's `Q_n`. -/
def CharbonnelQ (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean (n + 1)), S ∈ C (n + 1) →
    CharbonnelRelativelyClosedInPositiveLast S →
    interior S = ∅ →
      interior (charbonnelPositiveZeroTrace S) = ∅

/-- The bounded assertion proved first in Charbonnel 5.7. -/
def CharbonnelBoundedQ (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean (n + 1)), S ∈ C (n + 1) →
    CharbonnelRelativelyClosedInPositiveLast S →
    Bornology.IsBounded S → interior S = ∅ →
      interior (charbonnelPositiveZeroTrace S) = ∅

/-- Charbonnel's `P_n`, in the exact two-hypothesis form stated at the
start of section 5. -/
def CharbonnelP (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean n), S ∈ C n →
    ((volume : Measure (RealEuclidean n)) S = 0 ∨
      interior (closure S) = ∅) →
        (volume : Measure (RealEuclidean n)) (closure S) = 0

/-- Empty interior is equivalent to nullity for all members, without the
closedness hypothesis in `P'_n`. -/
def CharbonnelInteriorNullity
    (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean n), S ∈ C n →
    ((volume : Measure (RealEuclidean n)) S = 0 ↔ interior S = ∅)

/-! ## Membership interfaces used by the reduction -/

/-- The membership operations needed after the analytic part of section 5.
They are separated from compact truncation membership because the latter
also needs an explicit semialgebraic closed-ball construction. -/
structure CharbonnelSection5TraceMembership
    (C : EuclideanSetFamily) : Prop where
  closure_mem : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean d)}, S ∈ C d → closure S ∈ C d
  positiveLastPart_mem : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean (d + 1))}, S ∈ C (d + 1) →
      charbonnelPositiveLastPart S ∈ C (d + 1)
  positiveZeroTrace_mem : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean (d + 1))}, S ∈ C (d + 1) →
      charbonnelPositiveZeroTrace S ∈ C d

/-- Membership of the closed-ball truncations used in the compact and Baire
arguments. -/
def CharbonnelCompactTruncationMembership
    (C : EuclideanSetFamily) : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ {S : Set (RealEuclidean d)},
    S ∈ C d → ∀ m : ℕ, charbonnelCompactTruncation S m ∈ C d

/-- The finite locally closed decomposition used immediately before
Charbonnel section 5.  Keeping membership of every piece explicit is what
allows `P'_n` to be applied to its closure. -/
def CharbonnelFiniteLocallyClosedDecomposition
    (C : EuclideanSetFamily) (d : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean d), S ∈ C d →
    ∃ (k : ℕ) (piece : Fin k → Set (RealEuclidean d)),
      (∀ i, piece i ∈ C d) ∧
      (∀ i, IsLocallyClosed (piece i)) ∧
      S = ⋃ i, piece i

/-- The positive part membership proof already implicit in
`CharbonnelTraceMembership`. -/
theorem literalZeroSet_charbonnelClosure_positiveLastPart_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {d : ℕ} {S : Set (RealEuclidean (d + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (d + 1)) :
    charbonnelPositiveLastPart S ∈
      charbonnelClosure (literalZeroSetFamily G) (d + 1) := by
  obtain ⟨positiveDescription, hpositiveCarrier, _hpositiveRank⟩ :=
    exists_rank_one_description_positiveLastCoordinateLocus hG d
  have hpositive : charbonnelPositiveLastCoordinateLocus d ∈
      charbonnelClosure (literalZeroSetFamily G) (d + 1) :=
    ⟨positiveDescription, hpositiveCarrier⟩
  let hbase : ClosedPositiveArityDescriptionBase (literalZeroSetFamily G) :=
    literalZeroSetFamily_closedDescriptionBase hG hsmooth
  rw [charbonnelPositiveLastPart_eq_inter_locus]
  exact hbase.charbonnelClosure_inter hS hpositive

/-- The three trace-membership operations are already available for the
literal-zero Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_section5TraceMembership
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    CharbonnelSection5TraceMembership
      (charbonnelClosure (literalZeroSetFamily G)) where
  closure_mem := by
    intro d _hd S hS
    exact literalZeroSet_charbonnelClosure_closure_mem hS
  positiveLastPart_mem := by
    intro d _hd S hS
    exact literalZeroSet_charbonnelClosure_positiveLastPart_mem
      hG hsmooth hS
  positiveZeroTrace_mem := by
    intro d hd S hS
    exact literalZeroSet_charbonnelClosure_positiveZeroTrace_mem
      hG hsmooth hd hS

/-! ## Relatively closed positive parts and the bounded-to-global `Q_n` step -/

theorem CharbonnelRelativelyClosedInPositiveLast.compactTruncation
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : CharbonnelRelativelyClosedInPositiveLast S) (m : ℕ) :
    CharbonnelRelativelyClosedInPositiveLast
      (charbonnelCompactTruncation S m) := by
  refine ⟨inter_subset_left.trans hS.1, ?_⟩
  rw [charbonnelCompactTruncation, preimage_inter]
  exact hS.2.inter
    (Metric.isClosed_closedBall.preimage continuous_subtype_val)

theorem interior_eq_empty_of_subset
    {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hst : s ⊆ t) (ht : interior t = ∅) : interior s = ∅ := by
  exact subset_empty_iff.mp <| by
    simpa only [ht] using (interior_mono hst)

theorem charbonnelPositiveZeroTrace_eq_zeroSection_closure
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ⊆ charbonnelPositiveLastCoordinateLocus n) :
    charbonnelPositiveZeroTrace S = charbonnelZeroSection (closure S) := by
  rw [charbonnelPositiveZeroTrace,
    charbonnelPositiveLastPart_eq_inter_locus,
    inter_eq_left.mpr hS]
  rfl

/-- Compact truncation plus Baire upgrades the bounded case of `Q_n` to the
full assertion. -/
theorem charbonnelQ_of_boundedQ
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hbounded : CharbonnelBoundedQ C n) : CharbonnelQ C n := by
  intro S hS hrelative hSempty
  rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure hrelative.1]
  apply charbonnelZeroSection_closure_interior_eq_empty_of_truncations
  intro m
  have hTmem := htrunc (by omega : 0 < n + 1) hS m
  have hTrelative := hrelative.compactTruncation m
  have hTbounded := charbonnelCompactTruncation_isBounded S m
  have hTempty := interior_eq_empty_of_subset
    (charbonnelCompactTruncation_subset S m) hSempty
  have h := hbounded (charbonnelCompactTruncation S m)
    hTmem hTrelative hTbounded hTempty
  rwa [charbonnelPositiveZeroTrace_eq_zeroSection_closure hTrelative.1] at h

/-! ## Explicit statements of the remaining section 5 analytic core -/

/-- Uniform boundedness of the component count of the vertical images over
all positive-radius closed balls.  Charbonnel 5.3 obtains this by applying
the uniform affine-section clause to one parameterized incidence set. -/
def CharbonnelUniformLocalVerticalComponentBound {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∃ N : ℕ, ∀ (x : RealEuclidean n) (r : ℝ), 0 < r →
    ENat.card (ConnectedComponents
      (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ)) ≤ N

/-- The stabilized component-count conclusion inside one ball.  The source
proves this by a well-founded induction on the maximal component count and
the number of components whose base projection is not the whole ball. -/
def CharbonnelStableLocalVerticalComponentCount {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∃ (M : ℕ) (x : RealEuclidean n) (r : ℝ), 0 < r ∧
    ∀ (y : RealEuclidean n) (s : ℝ), 0 < s →
      Metric.closedBall y s ⊆ Metric.closedBall x r →
        ENat.card (ConnectedComponents
          (charbonnelVerticalImageOver S
            (Metric.closedBall y s) : Set ℝ)) = M

/-- A finite continuous graph description of all vertical fibers over a
base set.  This is the precise output needed in 5.7 after the stable
components have been isolated by disjoint intervals. -/
def CharbonnelFiniteContinuousVerticalGraphsOn {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n)) : Prop :=
  ∃ (M : ℕ) (f : Fin M → RealEuclidean n → ℝ),
    (∀ i, ContinuousOn (f i) B) ∧
    (∀ x ∈ B, charbonnelVerticalFiber S x = Set.range fun i ↦ f i x) ∧
    (∀ x ∈ B, (Set.univ : Set (Fin M)).Pairwise
      fun i j ↦ f i x ≠ f j x)

/-- The compact positive-measure conclusion of Charbonnel 5.6.  Its proof
uses the preceding stabilization, the interval-slab argument of 5.2/5.4,
the finite/infinite fiber split of 5.5, and `P'_n`. -/
def CharbonnelCompactPositiveVolumeInterior
    (C : EuclideanSetFamily) (d : ℕ) : Prop :=
  ∀ S : Set (RealEuclidean d), IsCompact S → S ∈ C d →
    0 < (volume : Measure (RealEuclidean d)) S →
      (interior S).Nonempty

/-- The two genuinely geometric implications supplied by Charbonnel
5.3--5.7 after `P'_n` has been assumed.  The first field packages the
compact conclusion of 5.6; the second packages the bounded part of 5.7.
The later truncation, Baire, and induction steps are proved below rather
than included in this interface. -/
structure CharbonnelSection5AnalyticStep
    (C : EuclideanSetFamily) : Prop where
  compactPositiveVolumeInterior_of_pPrime : ∀ {n : ℕ}, 0 < n →
    CharbonnelPPrime C n →
      CharbonnelCompactPositiveVolumeInterior C (n + 1)
  boundedQ_of_pPrime : ∀ {n : ℕ}, 0 < n →
    CharbonnelPPrime C n → CharbonnelBoundedQ C n

/-! ## From the compact core to `P'_n` -/

/-- Closed-ball truncations reduce `P'_n` to the compact
positive-measure conclusion. -/
theorem charbonnelPPrime_of_compactPositiveVolumeInterior
    {C : EuclideanSetFamily} {d : ℕ} (hd : 0 < d)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hcompact : CharbonnelCompactPositiveVolumeInterior C d) :
    CharbonnelPPrime C d := by
  intro S hSclosed hS
  constructor
  · intro hnull
    exact (volume : Measure (RealEuclidean d)).interior_eq_empty_of_null hnull
  · intro hSempty
    rw [← iUnion_charbonnelCompactTruncation S]
    exact measure_iUnion_null fun m ↦ by
      have hKempty : interior (charbonnelCompactTruncation S m) = ∅ :=
        interior_eq_empty_of_subset
          (charbonnelCompactTruncation_subset S m) hSempty
      by_contra hKnull
      have hKinterior := hcompact (charbonnelCompactTruncation S m)
        (charbonnelCompactTruncation_isCompact hSclosed m)
        (htrunc hd hS m) (pos_iff_ne_zero.mpr hKnull)
      exact hKinterior.ne_empty hKempty

/-- The successor step `P'_n ⇒ P'_{n+1}` after the compact geometric
conclusion of 5.6 has been supplied. -/
theorem charbonnelPPrime_succ_of_pPrime
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hanalytic : CharbonnelSection5AnalyticStep C)
    (hPPrime : CharbonnelPPrime C n) :
    CharbonnelPPrime C (n + 1) :=
  charbonnelPPrime_of_compactPositiveVolumeInterior (by omega)
    htrunc
    (hanalytic.compactPositiveVolumeInterior_of_pPrime hn hPPrime)

/-- The `P'_1` base case and the analytic successor step prove `P'_n` in
every positive arity. -/
theorem charbonnelPPrime_all_of_one_and_analyticStep
    {C : EuclideanSetFamily}
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hbase : CharbonnelPPrime C 1)
    (hanalytic : CharbonnelSection5AnalyticStep C) :
    ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n := by
  intro n hn
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction k with
  | zero => exact hbase
  | succ k ih =>
      exact charbonnelPPrime_succ_of_pPrime (Nat.succ_pos k)
        htrunc hanalytic (ih (Nat.succ_pos k))

/-- Finite locally closed decomposition upgrades `P'_n` from closed sets
to the nullity/empty-interior equivalence for all family members.  This is
the logical use of Charbonnel 5.1 in the passage to Wilkie 2.1. -/
theorem charbonnelInteriorNullity_of_pPrime_and_finiteLocallyClosed
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (hmem : CharbonnelSection5TraceMembership C)
    (hdecomp : CharbonnelFiniteLocallyClosedDecomposition C n)
    (hPPrime : CharbonnelPPrime C n) :
    CharbonnelInteriorNullity C n := by
  intro S hS
  constructor
  · intro hSnull
    exact (volume : Measure (RealEuclidean n)).interior_eq_empty_of_null
      hSnull
  · intro hSempty
    obtain ⟨k, piece, hpieceMem, hpieceLocallyClosed, hSpieces⟩ :=
      hdecomp S hS
    rw [hSpieces]
    apply measure_iUnion_null
    intro i
    have hpieceSubset : piece i ⊆ S := by
      rw [hSpieces]
      exact subset_iUnion piece i
    have hpieceEmpty : interior (piece i) = ∅ :=
      interior_eq_empty_of_subset hpieceSubset hSempty
    have hclosureEmpty : interior (closure (piece i)) = ∅ :=
      IsLocallyClosed.interior_closure_eq_empty
        (hpieceLocallyClosed i) hpieceEmpty
    have hclosureMem : closure (piece i) ∈ C n :=
      hmem.closure_mem hn (hpieceMem i)
    exact measure_mono_null subset_closure
      ((hPPrime (closure (piece i)) isClosed_closure hclosureMem).mpr
        hclosureEmpty)

/-- This is the formal `P'_n ⇒ Q_n` implication: 5.7 supplies its
bounded geometric part, while compact truncation and Baire supply the
unbounded passage. -/
theorem charbonnelQ_of_pPrime_and_analyticStep
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hanalytic : CharbonnelSection5AnalyticStep C)
    (hPPrime : CharbonnelPPrime C n) : CharbonnelQ C n :=
  charbonnelQ_of_boundedQ hn htrunc
    (hanalytic.boundedQ_of_pPrime hn hPPrime)

/-- All the `Q_n` assertions obtained from the completed `P'_n`
induction. -/
theorem charbonnelQ_all_of_one_and_analyticStep
    {C : EuclideanSetFamily}
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hbase : CharbonnelPPrime C 1)
    (hanalytic : CharbonnelSection5AnalyticStep C) :
    ∀ {n : ℕ}, 0 < n → CharbonnelQ C n := by
  intro n hn
  exact charbonnelQ_of_pPrime_and_analyticStep hn htrunc hanalytic
    (charbonnelPPrime_all_of_one_and_analyticStep
      htrunc hbase hanalytic hn)

/-! ## The closed-lift witness used to prove `P_n` -/

/-- The output required from the closed-lift construction in Charbonnel
5.8.  In the paper, starting from a closed lift `T`, the carrier is

`M = {(x,ε) | ε > 0 ∧ ∃ y ∈ T, ‖y‖ ≤ 1 / ε}`.

The Fubini nullity implication and the identity of its zero trace with
`closure S` are stated explicitly rather than hidden in a theorem about
arbitrary weak structures. -/
structure CharbonnelClosureNullityWitness
    (C : EuclideanSetFamily) (n : ℕ)
    (S : Set (RealEuclidean n)) where
  carrier : Set (RealEuclidean (n + 1))
  mem : carrier ∈ C (n + 1)
  relativelyClosed : CharbonnelRelativelyClosedInPositiveLast carrier
  null_of_source_null :
    (volume : Measure (RealEuclidean n)) S = 0 →
      (volume : Measure (RealEuclidean (n + 1))) carrier = 0
  positiveZeroTrace_eq_closure :
    charbonnelPositiveZeroTrace carrier = closure S

/-- Availability of the 5.8 closed-lift witness for every positive-arity
member. -/
def HasCharbonnelClosureNullityWitnesses
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {S : Set (RealEuclidean n)}, S ∈ C n →
    Nonempty (CharbonnelClosureNullityWitness C n S)

/-- `P'_n`, `Q_n`, and the explicit closed-lift witness prove `P_n`. -/
theorem charbonnelP_of_pPrime_Q_and_closureWitness
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (hmem : CharbonnelSection5TraceMembership C)
    (hPPrime : CharbonnelPPrime C n)
    (hQ : CharbonnelQ C n)
    (hwitness : HasCharbonnelClosureNullityWitnesses C) :
    CharbonnelP C n := by
  intro S hS hsmall
  rcases hsmall with hSnull | hclosureEmpty
  · let witness := Classical.choice (hwitness hn hS)
    have hcarrierNull :
        (volume : Measure (RealEuclidean (n + 1))) witness.carrier = 0 :=
      witness.null_of_source_null hSnull
    have hcarrierEmpty : interior witness.carrier = ∅ :=
      (volume : Measure (RealEuclidean (n + 1))).interior_eq_empty_of_null
        hcarrierNull
    have htraceEmpty :
        interior (charbonnelPositiveZeroTrace witness.carrier) = ∅ :=
      hQ witness.carrier witness.mem witness.relativelyClosed hcarrierEmpty
    have htraceClosed :
        IsClosed (charbonnelPositiveZeroTrace witness.carrier) := by
      rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure
        witness.relativelyClosed.1]
      exact charbonnelZeroSection_isClosed isClosed_closure
    have htraceMem : charbonnelPositiveZeroTrace witness.carrier ∈ C n :=
      hmem.positiveZeroTrace_mem hn witness.mem
    have htraceNull : (volume : Measure (RealEuclidean n))
        (charbonnelPositiveZeroTrace witness.carrier) = 0 :=
      (hPPrime (charbonnelPositiveZeroTrace witness.carrier)
        htraceClosed htraceMem).mpr htraceEmpty
    rwa [witness.positiveZeroTrace_eq_closure] at htraceNull
  · exact (hPPrime (closure S) isClosed_closure
      (hmem.closure_mem hn hS)).mpr
      hclosureEmpty

/-! ## Wilkie 2.1 and 2.2 and the target smallness interface -/

/-- The four equivalent conditions in Wilkie's Theorem 2.1, written as a
chain in their printed order. -/
def CharbonnelTheorem21 (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {S : Set (RealEuclidean n)}, S ∈ C n →
    (interior S = ∅ ↔ (volume : Measure (RealEuclidean n)) S = 0) ∧
    ((volume : Measure (RealEuclidean n)) S = 0 ↔
      interior (closure S) = ∅) ∧
    (interior (closure S) = ∅ ↔
      (volume : Measure (RealEuclidean n)) (closure S) = 0)

/-- The exact positive-half-space statement of Wilkie's Theorem 2.2: the
zero trace is again a family member, and empty interior descends to it. -/
def CharbonnelTheorem22 (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ {S : Set (RealEuclidean (n + 1))}, S ∈ C (n + 1) →
      S ⊆ charbonnelPositiveLastCoordinateLocus n →
      charbonnelPositiveZeroTrace S ∈ C n ∧
        (interior S = ∅ →
          interior (charbonnelPositiveZeroTrace S) = ∅)

/-- `P_n` together with nullity/empty-interior equivalence gives all four
conditions of Wilkie 2.1. -/
theorem charbonnelTheorem21_of_interiorNullity_and_P
    {C : EuclideanSetFamily}
    (hnull : ∀ {n : ℕ}, 0 < n → CharbonnelInteriorNullity C n)
    (hP : ∀ {n : ℕ}, 0 < n → CharbonnelP C n) :
    CharbonnelTheorem21 C := by
  intro n hn S hS
  have hnullS := hnull hn S hS
  refine ⟨hnullS.symm, ?_, ?_⟩
  · constructor
    · intro hSzero
      exact (volume : Measure (RealEuclidean n)).interior_eq_empty_of_null
        (hP hn S hS (Or.inl hSzero))
    · intro hclosureEmpty
      exact measure_mono_null subset_closure
        (hP hn S hS (Or.inr hclosureEmpty))
  · constructor
    · intro hclosureEmpty
      exact hP hn S hS (Or.inr hclosureEmpty)
    · intro hclosureNull
      exact (volume : Measure (RealEuclidean n)).interior_eq_empty_of_null
        hclosureNull

/-- Closing the positive part and then restricting again to positive last
coordinate gives the relatively closed set used to pass from `Q_n` to
Wilkie 2.2. -/
def charbonnelPositiveClosureCore {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Set (RealEuclidean (n + 1)) :=
  closure (charbonnelPositiveLastPart S) ∩
    charbonnelPositiveLastCoordinateLocus n

theorem charbonnelPositiveClosureCore_subset_positive {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    charbonnelPositiveClosureCore S ⊆
      charbonnelPositiveLastCoordinateLocus n :=
  inter_subset_right

theorem charbonnelPositiveClosureCore_relativelyClosed {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    CharbonnelRelativelyClosedInPositiveLast
      (charbonnelPositiveClosureCore S) := by
  refine ⟨charbonnelPositiveClosureCore_subset_positive S, ?_⟩
  simpa [charbonnelPositiveClosureCore] using
    (isClosed_closure.preimage
      (continuous_subtype_val : Continuous
        (fun z : charbonnelPositiveLastCoordinateLocus n ↦
          (z : RealEuclidean (n + 1)))))

theorem closure_charbonnelPositiveClosureCore {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    closure (charbonnelPositiveClosureCore S) =
      closure (charbonnelPositiveLastPart S) := by
  apply Subset.antisymm
  · exact closure_minimal inter_subset_left isClosed_closure
  · apply closure_mono
    intro z hz
    exact ⟨subset_closure hz, hz.2⟩

theorem charbonnelPositiveZeroTrace_positiveLastPart {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    charbonnelPositiveZeroTrace (charbonnelPositiveLastPart S) =
      charbonnelPositiveZeroTrace S := by
  simp [charbonnelPositiveZeroTrace, charbonnelPositiveLastPart,
    inter_assoc]

theorem charbonnelPositiveZeroTrace_positiveClosureCore {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    charbonnelPositiveZeroTrace (charbonnelPositiveClosureCore S) =
      charbonnelPositiveZeroTrace S := by
  rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure
    (charbonnelPositiveClosureCore_subset_positive S),
    closure_charbonnelPositiveClosureCore]
  rfl

/-- The source's `Q_n`, plus the closure-smallness half of 2.1, implies the
more convenient arbitrary-member formulation 2.2. -/
theorem charbonnelTheorem22_of_Q
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hclosure : ∀ {d : ℕ}, 0 < d →
      ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
        interior S = ∅ → interior (closure S) = ∅)
    (hQ : ∀ {n : ℕ}, 0 < n → CharbonnelQ C n) :
    CharbonnelTheorem22 C := by
  intro n hn S hS hSpositive
  refine ⟨hmem.positiveZeroTrace_mem hn hS, ?_⟩
  intro hSempty
  have hpositiveMem : charbonnelPositiveLastPart S ∈ C (n + 1) :=
    hmem.positiveLastPart_mem hn hS
  have hpositiveEmpty : interior (charbonnelPositiveLastPart S) = ∅ :=
    interior_eq_empty_of_subset inter_subset_left hSempty
  have hclosureEmpty : interior (closure (charbonnelPositiveLastPart S)) = ∅ :=
    hclosure (by omega : 0 < n + 1) hpositiveMem hpositiveEmpty
  have hcoreMem : charbonnelPositiveClosureCore S ∈ C (n + 1) := by
    have hclosedMem := hmem.closure_mem (by omega : 0 < n + 1) hpositiveMem
    simpa only [charbonnelPositiveClosureCore,
      charbonnelPositiveLastPart_eq_inter_locus] using
      hmem.positiveLastPart_mem hn hclosedMem
  have hcoreEmpty : interior (charbonnelPositiveClosureCore S) = ∅ :=
    interior_eq_empty_of_subset inter_subset_left hclosureEmpty
  have h := hQ hn (charbonnelPositiveClosureCore S) hcoreMem
    (charbonnelPositiveClosureCore_relativelyClosed S) hcoreEmpty
  rwa [charbonnelPositiveZeroTrace_positiveClosureCore] at h

/-- Wilkie 2.1 and 2.2 give exactly the two analytic fields still missing
from `CharbonnelTraceMembership`. -/
theorem charbonnelApproximationTraceSmallness_of_theorems21_22
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (h21 : CharbonnelTheorem21 C)
    (h22 : CharbonnelTheorem22 C) :
    CharbonnelApproximationTraceSmallness C where
  closure_interior_eq_empty := by
    intro d hd S hS hSempty
    exact (h21 hd hS).2.1.mp ((h21 hd hS).1.mp hSempty)
  positiveZeroTrace_interior_eq_empty := by
    intro d hd S hS hSempty
    have hpositiveMem := hmem.positiveLastPart_mem hd hS
    have hpositiveEmpty : interior (charbonnelPositiveLastPart S) = ∅ :=
      interior_eq_empty_of_subset inter_subset_left hSempty
    have h := (h22 hd hpositiveMem inter_subset_right).2 hpositiveEmpty
    rwa [charbonnelPositiveZeroTrace_positiveLastPart] at h

/-- Final logical reduction from the outputs of Charbonnel section 5 to the
smallness interface used by Wilkie's approximation trace recursion. -/
theorem charbonnelApproximationTraceSmallness_of_section5
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hnull : ∀ {n : ℕ}, 0 < n → CharbonnelInteriorNullity C n)
    (hP : ∀ {n : ℕ}, 0 < n → CharbonnelP C n)
    (hQ : ∀ {n : ℕ}, 0 < n → CharbonnelQ C n) :
    CharbonnelApproximationTraceSmallness C := by
  let h21 : CharbonnelTheorem21 C :=
    charbonnelTheorem21_of_interiorNullity_and_P hnull hP
  have hclosure : ∀ {d : ℕ}, 0 < d →
      ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
        interior S = ∅ → interior (closure S) = ∅ := by
    intro d hd S hS hSempty
    exact (h21 hd hS).2.1.mp ((h21 hd hS).1.mp hSempty)
  let h22 : CharbonnelTheorem22 C :=
    charbonnelTheorem22_of_Q hmem hclosure hQ
  exact charbonnelApproximationTraceSmallness_of_theorems21_22
    hmem h21 h22

/-- The complete logical induction of Charbonnel section 5.  The only
non-elementary inputs are the explicitly named analytic step, the one
dimensional base case, the finite locally closed decomposition preceding
section 5, and the closed-lift witnesses of 5.8. -/
theorem charbonnelApproximationTraceSmallness_of_section5Induction
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hbase : CharbonnelPPrime C 1)
    (hanalytic : CharbonnelSection5AnalyticStep C)
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition C n)
    (hwitness : HasCharbonnelClosureNullityWitnesses C) :
    CharbonnelApproximationTraceSmallness C := by
  have hPPrime : ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n :=
    charbonnelPPrime_all_of_one_and_analyticStep
      htrunc hbase hanalytic
  have hQ : ∀ {n : ℕ}, 0 < n → CharbonnelQ C n := by
    intro n hn
    exact charbonnelQ_of_pPrime_and_analyticStep hn htrunc hanalytic
      (hPPrime hn)
  have hP : ∀ {n : ℕ}, 0 < n → CharbonnelP C n := by
    intro n hn
    exact charbonnelP_of_pPrime_Q_and_closureWitness
      hn hmem (hPPrime hn) (hQ hn) hwitness
  have hnull : ∀ {n : ℕ}, 0 < n → CharbonnelInteriorNullity C n := by
    intro n hn
    exact charbonnelInteriorNullity_of_pPrime_and_finiteLocallyClosed
      hn hmem (hdecomp hn) (hPPrime hn)
  exact charbonnelApproximationTraceSmallness_of_section5
    hmem hnull hP hQ

end AbelFormalization
