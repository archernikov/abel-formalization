import AbelFormalization.MaxwellChosenDifferentiability
import AbelFormalization.MaxwellOneSidedClusterCoverage

/-!
# Continuity bridge for Maxwell's chosen representative

The measure-theoretic predicate `IsMaxwellPseudofunctionOn` does not itself
make its canonical representative continuous.  The scalar closure sequence
dichotomy does, however, identify a relation-level exceptional locus outside
which continuity follows.  This file records that reduction and its
Charbonnel-family membership calculation.

The closure of this locus is the natural extra closed set to adjoin to the
current first-order exceptional locus before attempting the remaining
coordinate-line differentiability argument.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- The three relation-level alternatives which can obstruct continuity of
the canonical scalar representative.  The finite alternative uses
`closure R`, while escape to either infinity is already encoded by the
reciprocal closures of `R`. -/
def maxwellChosenContinuityBadLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  U ∩
    (maxwellMultivaluedLocus (closure R) ∪
      (maxwellPositiveInfinityBase R ∪
        maxwellNegativeInfinityBase R))

/-- Closing the relation-level continuity obstruction gives a closed set
whose complement in an open domain is again open. -/
def maxwellChosenContinuityExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  closure (maxwellChosenContinuityBadLocus U R)

theorem isClosed_maxwellChosenContinuityExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    IsClosed (maxwellChosenContinuityExceptionalLocus U R) := by
  exact isClosed_closure

/-- The chosen scalar graph is contained in the relation over its stated
domain. -/
theorem IsMaxwellPseudofunctionOn.chosenScalarFunctionGraph_subset
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) :
    maxwellFunctionGraph U
        (fun (x : RealEuclidean p) (_ : Fin 1) ↦
          maxwellChosenScalarValue R x) ⊆ R := by
  exact hR.chosenScalarGraph_subset

/-- Outside the relation-level closure alternatives, the canonical scalar
representative is continuous relative to the original domain. -/
theorem IsMaxwellPseudofunctionOn.continuousWithinAt_chosenScalarValue
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R)
    {x : RealEuclidean p} (hxU : x ∈ U)
    (hx : x ∉ maxwellChosenContinuityBadLocus U R) :
    ContinuousWithinAt (maxwellChosenScalarValue R) U x := by
  let f : RealEuclidean p → RealEuclidean 1 :=
    fun (z : RealEuclidean p) (_ : Fin 1) ↦
      maxwellChosenScalarValue R z
  let G : MaxwellRelation p 1 := maxwellFunctionGraph U f
  have hGR : G ⊆ R := by
    simpa only [G, f] using hR.chosenScalarFunctionGraph_subset
  have hnotBad :
      x ∉ maxwellMultivaluedLocus (closure R) ∪
        (maxwellPositiveInfinityBase R ∪
          maxwellNegativeInfinityBase R) := by
    intro hbad
    exact hx ⟨hxU, hbad⟩
  have hf : ContinuousWithinAt f U x := by
    by_contra hdiscontinuous
    rcases maxwellScalarClosureSequenceDichotomy_mathlib
      U f x hxU hdiscontinuous with hfinite | hpositive | hnegative
    · apply hnotBad
      apply Or.inl
      rcases hfinite with ⟨y₁, y₂, hy₁, hy₂, hne⟩
      exact ⟨y₁, y₂, closure_mono hGR hy₁,
        closure_mono hGR hy₂, hne⟩
    · apply hnotBad
      exact Or.inr <| Or.inl <|
        maxwellPositiveInfinityBase_mono hGR hpositive
    · apply hnotBad
      exact Or.inr <| Or.inr <|
        maxwellNegativeInfinityBase_mono hGR hnegative
  have hcoordinate :=
    (continuous_apply (0 : Fin 1)).continuousAt.comp_continuousWithinAt hf
  simpa only [f, Function.comp_def] using hcoordinate

/-- Pointwise continuity on the complement of the raw relation-level bad
locus. -/
theorem IsMaxwellPseudofunctionOn.continuousOn_chosenScalarValue_compl_bad
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) :
    ContinuousOn (maxwellChosenScalarValue R)
      (U \ maxwellChosenContinuityBadLocus U R) := by
  intro x hx
  exact (hR.continuousWithinAt_chosenScalarValue hx.1 hx.2).mono
    inter_subset_left

/-- Continuity on the complement of the closed enlargement. -/
theorem IsMaxwellPseudofunctionOn.continuousOn_chosenScalarValue_compl_exceptional
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) :
    ContinuousOn (maxwellChosenScalarValue R)
      (U \ maxwellChosenContinuityExceptionalLocus U R) := by
  intro x hx
  have hxBad : x ∉ maxwellChosenContinuityBadLocus U R := by
    intro h
    exact hx.2 (subset_closure h)
  exact (hR.continuousWithinAt_chosenScalarValue hx.1 hxBad).mono
    inter_subset_left

/-- If `U` is open, removing the closed continuity obstruction leaves an
open domain on which the chosen representative is continuous. -/
theorem isOpen_chosenScalarContinuityDomain {p : ℕ}
    {U : Set (RealEuclidean p)} (hU : IsOpen U)
    (R : MaxwellRelation p 1) :
    IsOpen (U \ maxwellChosenContinuityExceptionalLocus U R) := by
  exact hU.sdiff (isClosed_maxwellChosenContinuityExceptionalLocus U R)

/-- The relation-level continuity obstruction is itself a member of the
generated Charbonnel family.  This is the algebraic input needed before a
Theorem-2.1 nullity/interior argument can be attempted. -/
theorem maxwellChosenContinuityBadLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellChosenContinuityBadLocus U R ∈ charbonnelClosure S p := by
  have hclosureR : closure R ∈ charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hR
  have hfinite := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC hp hclosureR
  have hpositive := maxwellPositiveInfinityBase_mem_charbonnelClosure
    hC hp hR
  have hnegative := maxwellNegativeInfinityBase_mem_charbonnelClosure
    hC hp hR
  exact hC.ws1_inter hp hU
    (charbonnelClosure_union hfinite
      (charbonnelClosure_union hpositive hnegative))

/-- The closed enlargement is also a Charbonnel-closure member. -/
theorem maxwellChosenContinuityExceptionalLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellChosenContinuityExceptionalLocus U R ∈
      charbonnelClosure S p := by
  exact charbonnelClosure_topologicalClosure
    (maxwellChosenContinuityBadLocus_mem_charbonnelClosure
      hC hp hU hR)

/-- The open domain available for the remaining coordinate-line argument:
remove both the new continuity obstruction and the existing first-order
exceptional locus. -/
def maxwellChosenLineRegularDomain {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  U \ (maxwellChosenContinuityExceptionalLocus U R ∪
    maxwellFirstOrderExceptionalLocus U R)

theorem isOpen_maxwellChosenLineRegularDomain {p : ℕ}
    {U : Set (RealEuclidean p)} (hU : IsOpen U)
    (R : MaxwellRelation p 1) :
    IsOpen (maxwellChosenLineRegularDomain U R) := by
  exact hU.sdiff
    ((isClosed_maxwellChosenContinuityExceptionalLocus U R).union
      (isClosed_maxwellFirstOrderExceptionalLocus U R))

theorem IsMaxwellPseudofunctionOn.continuousOn_chosenScalarValue_lineRegularDomain
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) :
    ContinuousOn (maxwellChosenScalarValue R)
      (maxwellChosenLineRegularDomain U R) := by
  apply hR.continuousOn_chosenScalarValue_compl_exceptional.mono
  intro x hx
  exact ⟨hx.1, fun h ↦ hx.2 (Or.inl h)⟩

/-! ## Smallness of the relation-level continuity obstruction -/

/-- Closure membership localizes after restricting a relation to an open
base neighborhood. -/
theorem mem_closure_maxwellRelationRestrict_of_isOpen
    {p q : ℕ} {R : MaxwellRelation p q}
    {B : Set (RealEuclidean p)} (hB : IsOpen B)
    {x : RealEuclidean p} (hx : x ∈ B) {y : RealEuclidean q}
    (hxy : realEuclideanAppend x y ∈ closure R) :
    realEuclideanAppend x y ∈ closure (maxwellRelationRestrict R B) := by
  rw [mem_closure_iff] at hxy ⊢
  intro O hO hxyO
  let leftMap : RealEuclidean (p + q) →L[ℝ] RealEuclidean p :=
    (realEuclideanTakeLeftLinearMap p q).toContinuousLinearMap
  have hbaseOpen : IsOpen (leftMap ⁻¹' B) :=
    hB.preimage leftMap.continuous
  have hxyBase : realEuclideanAppend x y ∈ leftMap ⁻¹' B := by
    simpa [leftMap] using hx
  obtain ⟨z, ⟨⟨hzO, hzBase⟩, hzR⟩⟩ :=
    hxy (O ∩ leftMap ⁻¹' B) (hO.inter hbaseOpen) ⟨hxyO, hxyBase⟩
  refine ⟨z, hzO, hzR, ?_⟩
  simpa [maxwellRelationRestrict, leftMap] using hzBase

/-- Taking positive reciprocals commutes with restriction in the base
coordinates. -/
theorem maxwellPositiveReciprocalRelation_restrict
    {p : ℕ} (R : MaxwellRelation p 1)
    (B : Set (RealEuclidean p)) :
    maxwellPositiveReciprocalRelation (maxwellRelationRestrict R B) =
      maxwellRelationRestrict (maxwellPositiveReciprocalRelation R) B := by
  ext w
  simp only [maxwellPositiveReciprocalRelation,
    maxwellRelationRestrict, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hyR, hyB⟩, hyr, hr⟩
    exact ⟨⟨y, hyR, hyr, hr⟩, by simpa using hyB⟩
  · rintro ⟨⟨y, hyR, hyr, hr⟩, hwB⟩
    exact ⟨y, ⟨hyR, by simpa using hwB⟩, hyr, hr⟩

/-- Taking negative reciprocals commutes with restriction in the base
coordinates. -/
theorem maxwellNegativeReciprocalRelation_restrict
    {p : ℕ} (R : MaxwellRelation p 1)
    (B : Set (RealEuclidean p)) :
    maxwellNegativeReciprocalRelation (maxwellRelationRestrict R B) =
      maxwellRelationRestrict (maxwellNegativeReciprocalRelation R) B := by
  ext w
  simp only [maxwellNegativeReciprocalRelation,
    maxwellRelationRestrict, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hyR, hyB⟩, hyr, hr⟩
    exact ⟨⟨y, hyR, hyr, hr⟩, by simpa using hyB⟩
  · rintro ⟨⟨y, hyR, hyr, hr⟩, hwB⟩
    exact ⟨y, ⟨hyR, by simpa using hwB⟩, hyr, hr⟩

/-- A finite two-value closure obstruction localizes to any open base
neighborhood of its base point. -/
theorem mem_maxwellMultivaluedLocus_closure_restrict_of_isOpen
    {p : ℕ} {R : MaxwellRelation p 1}
    {B : Set (RealEuclidean p)} (hB : IsOpen B)
    {x : RealEuclidean p} (hx : x ∈ B)
    (h : x ∈ maxwellMultivaluedLocus (closure R)) :
    x ∈ maxwellMultivaluedLocus
      (closure (maxwellRelationRestrict R B)) := by
  rcases h with ⟨y₁, y₂, hy₁, hy₂, hne⟩
  exact ⟨y₁, y₂,
    mem_closure_maxwellRelationRestrict_of_isOpen hB hx hy₁,
    mem_closure_maxwellRelationRestrict_of_isOpen hB hx hy₂, hne⟩

/-- Positive escape to infinity localizes to any open base neighborhood of
its base point. -/
theorem mem_maxwellPositiveInfinityBase_restrict_of_isOpen
    {p : ℕ} {R : MaxwellRelation p 1}
    {B : Set (RealEuclidean p)} (hB : IsOpen B)
    {x : RealEuclidean p} (hx : x ∈ B)
    (h : x ∈ maxwellPositiveInfinityBase R) :
    x ∈ maxwellPositiveInfinityBase (maxwellRelationRestrict R B) := by
  have h' := mem_closure_maxwellRelationRestrict_of_isOpen
    (R := maxwellPositiveReciprocalRelation R) hB hx h
  rw [← maxwellPositiveReciprocalRelation_restrict] at h'
  exact h'

/-- Negative escape to infinity localizes to any open base neighborhood of
its base point. -/
theorem mem_maxwellNegativeInfinityBase_restrict_of_isOpen
    {p : ℕ} {R : MaxwellRelation p 1}
    {B : Set (RealEuclidean p)} (hB : IsOpen B)
    {x : RealEuclidean p} (hx : x ∈ B)
    (h : x ∈ maxwellNegativeInfinityBase R) :
    x ∈ maxwellNegativeInfinityBase (maxwellRelationRestrict R B) := by
  have h' := mem_closure_maxwellRelationRestrict_of_isOpen
    (R := maxwellNegativeReciprocalRelation R) hB hx h
  rw [← maxwellNegativeReciprocalRelation_restrict] at h'
  exact h'

/-- Away from the original multivalued locus, restricting a scalar
pseudofunction gives exactly the graph of its canonical representative. -/
theorem IsMaxwellPseudofunctionOn.restrict_eq_chosenScalarFunctionGraph
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R)
    (hB : B ⊆ U \ maxwellMultivaluedLocus R) :
    maxwellRelationRestrict R B =
      maxwellFunctionGraph B
        (fun (x : RealEuclidean p) (_ : Fin 1) ↦
          maxwellChosenScalarValue R x) := by
  ext z
  rw [← realEuclideanAppend_takeLeft_takeRight z]
  rw [realEuclideanAppend_mem_maxwellRelationRestrict_iff,
    realEuclideanAppend_mem_maxwellFunctionGraph_iff]
  constructor
  · rintro ⟨hzR, hxB⟩
    have hxGood := hB hxB
    refine ⟨hxB, ?_⟩
    rw [← maxwellChosenValue_eq_scalar R (realEuclideanTakeLeft z)]
    exact eq_maxwellChosenValue_of_not_mem_multivaluedLocus
      hxGood.2 hzR
  · rintro ⟨hxB, hy⟩
    refine ⟨?_, hxB⟩
    rw [hy, ← maxwellChosenValue_eq_scalar R (realEuclideanTakeLeft z)]
    exact hR.full_fibers.maxwellChosenValue_mem (hB hxB).1

/-- A scalar pseudofunction relation in the Charbonnel closure has a
Charbonnel-closure domain. -/
theorem IsMaxwellPseudofunctionOn.domain_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R)
    (hRmem : R ∈ charbonnelClosure S (p + 1)) :
    U ∈ charbonnelClosure S p := by
  have hdomain : maxwellRelationDomain R = U :=
    (isMaxwellPseudofunctionOn_iff_domain_eq U R).mp hR |>.1
  rw [← hdomain, maxwellRelationDomain_eq_existentialProjection]
  exact charbonnelClosure_projection hp hRmem

/-- Under Theorem 2.1 and WS5, the raw relation-level obstruction to
continuity of the chosen representative has empty interior.  No separate
family-membership assumption on `U` is needed: it follows by projecting
`R`, whose domain is `U`. -/
theorem maxwellChosenContinuityBadLocus_interior_eq_empty_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) :
    interior (maxwellChosenContinuityBadLocus U R) = ∅ := by
  have hmultiMem : maxwellMultivaluedLocus R ∈
      charbonnelClosure S p :=
    maxwellMultivaluedLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hRmem
  have hmultiClosureEmpty :
      interior (closure (maxwellMultivaluedLocus R)) = ∅ :=
    (h21 hp hmultiMem).2.1.mp hR.multivalued_null
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hbadInterior
  obtain ⟨x₀, ε, hε, hball⟩ :=
    exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
      isOpen_interior hbadInterior isClosed_closure hmultiClosureEmpty
  let B : Set (RealEuclidean p) := Metric.ball x₀ ε
  let f : RealEuclidean p → RealEuclidean 1 :=
    fun (x : RealEuclidean p) (_ : Fin 1) ↦
      maxwellChosenScalarValue R x
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBnonempty : B.Nonempty := ⟨x₀, Metric.mem_ball_self hε⟩
  have hBmem : B ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp
      (polynomialSignConstructible_ball x₀ hε)
  have hBbad : B ⊆ maxwellChosenContinuityBadLocus U R := by
    intro x hx
    exact interior_subset (hball hx).1
  have hBgood : B ⊆ U \ maxwellMultivaluedLocus R := by
    intro x hx
    exact ⟨(hBbad hx).1,
      fun hxMulti ↦ (hball hx).2 (subset_closure hxMulti)⟩
  have hgraphEq : maxwellRelationRestrict R B =
      maxwellFunctionGraph B f := by
    simpa only [f] using hR.restrict_eq_chosenScalarFunctionGraph hBgood
  have hgraphMem : maxwellFunctionGraph B f ∈
      charbonnelClosure S (p + 1) := by
    rw [← hgraphEq]
    exact maxwellRelationRestrict_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hRmem
  have hscalarEmpty :
      interior (maxwellScalarClosureBadLocus B f) = ∅ :=
    maxwellScalarClosureBadLocus_interior_eq_empty
      (maxwellScalarClosureBadLocusEscapeSelection_of_theorem21 hC h21)
      hp hBmem hgraphMem
  have hBscalar : B ⊆ maxwellScalarClosureBadLocus B f := by
    intro x hx
    have hxBad := hBbad hx
    refine ⟨hx, ?_⟩
    rcases hxBad.2 with hfinite | hpositive | hnegative
    · left
      rw [← hgraphEq]
      exact mem_maxwellMultivaluedLocus_closure_restrict_of_isOpen
        hBopen hx hfinite
    · right; left
      rw [← hgraphEq]
      exact mem_maxwellPositiveInfinityBase_restrict_of_isOpen
        hBopen hx hpositive
    · right; right
      rw [← hgraphEq]
      exact mem_maxwellNegativeInfinityBase_restrict_of_isOpen
        hBopen hx hnegative
  have hBinterior :
      B ⊆ interior (maxwellScalarClosureBadLocus B f) :=
    hBopen.subset_interior_iff.mpr hBscalar
  obtain ⟨x, hx⟩ := hBnonempty
  simpa [hscalarEmpty] using hBinterior hx

/-- Membership, nullity, and empty interior for both the raw continuity
obstruction and its closed enlargement. -/
structure MaxwellChosenContinuityBadLocusSmallness
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) : Prop where
  badLocus_mem :
    maxwellChosenContinuityBadLocus U R ∈ charbonnelClosure S p
  badLocus_volume_eq_zero :
    (volume : Measure (RealEuclidean p))
      (maxwellChosenContinuityBadLocus U R) = 0
  badLocus_interior_eq_empty :
    interior (maxwellChosenContinuityBadLocus U R) = ∅
  exceptionalLocus_mem :
    maxwellChosenContinuityExceptionalLocus U R ∈ charbonnelClosure S p
  exceptionalLocus_interior_eq_empty :
    interior (maxwellChosenContinuityExceptionalLocus U R) = ∅
  exceptionalLocus_volume_eq_zero :
    (volume : Measure (RealEuclidean p))
      (maxwellChosenContinuityExceptionalLocus U R) = 0

/-- The full continuity-bad-locus smallness package follows from Theorem
2.1, WS5, family membership of the relation, and the pseudofunction
hypothesis. -/
theorem maxwellChosenContinuityBadLocusSmallness_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) :
    MaxwellChosenContinuityBadLocusSmallness S U R := by
  have hUmem := hR.domain_mem_charbonnelClosure hp hRmem
  have hbadMem := maxwellChosenContinuityBadLocus_mem_charbonnelClosure
    hC.toPositiveArityWeakSetStructure hp hUmem hRmem
  have hbadEmpty :=
    maxwellChosenContinuityBadLocus_interior_eq_empty_of_theorem21
      hC h21 hp hRmem hR
  have hbadNull :
      (volume : Measure (RealEuclidean p))
        (maxwellChosenContinuityBadLocus U R) = 0 :=
    (h21 hp hbadMem).1.mp hbadEmpty
  have hexceptionalMem :=
    maxwellChosenContinuityExceptionalLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hUmem hRmem
  have hexceptionalEmpty :
      interior (maxwellChosenContinuityExceptionalLocus U R) = ∅ :=
    (h21 hp hbadMem).2.1.mp hbadNull
  have hexceptionalNull :
      (volume : Measure (RealEuclidean p))
        (maxwellChosenContinuityExceptionalLocus U R) = 0 :=
    (h21 hp hbadMem).2.2.mp hexceptionalEmpty
  exact
    { badLocus_mem := hbadMem
      badLocus_volume_eq_zero := hbadNull
      badLocus_interior_eq_empty := hbadEmpty
      exceptionalLocus_mem := hexceptionalMem
      exceptionalLocus_interior_eq_empty := hexceptionalEmpty
      exceptionalLocus_volume_eq_zero := hexceptionalNull }

theorem maxwellChosenContinuityBadLocus_volume_eq_zero_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) :
    (volume : Measure (RealEuclidean p))
      (maxwellChosenContinuityBadLocus U R) = 0 :=
  (maxwellChosenContinuityBadLocusSmallness_of_theorem21
    hC h21 hp hRmem hR).badLocus_volume_eq_zero

theorem maxwellChosenContinuityExceptionalLocus_interior_eq_empty_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) :
    interior (maxwellChosenContinuityExceptionalLocus U R) = ∅ :=
  (maxwellChosenContinuityBadLocusSmallness_of_theorem21
    hC h21 hp hRmem hR).exceptionalLocus_interior_eq_empty

theorem maxwellChosenContinuityExceptionalLocus_volume_eq_zero_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) :
    (volume : Measure (RealEuclidean p))
      (maxwellChosenContinuityExceptionalLocus U R) = 0 :=
  (maxwellChosenContinuityBadLocusSmallness_of_theorem21
    hC h21 hp hRmem hR).exceptionalLocus_volume_eq_zero

/-! ## The remaining one-sided infinity obstruction -/

/-- At a fixed base point and coordinate, neither one-sided quotient has a
source-defined cluster at either signed infinity.  This is stronger than
excluding the reciprocal closures of the already-formed finite zero-step
trace: reciprocation and taking the zero-step trace need not commute. -/
def MaxwellNoOneSidedInfiniteSlopeClustersAt {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (x : RealEuclidean p) : Prop :=
  ∀ side infinity,
    x ∉ maxwellOneSidedInfinityBase U R i side infinity

/-- Pointwise absence of the four source-defined infinite slope clusters on
a base set. -/
def MaxwellNoOneSidedInfiniteSlopeClustersOn {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (B : Set (RealEuclidean p)) : Prop :=
  ∀ x ∈ B, ∀ i : Fin p,
    MaxwellNoOneSidedInfiniteSlopeClustersAt U R i x

/-- The union of all four source-defined one-sided infinity bases over all
coordinates.  This is the exact obstruction not represented by the older
full-zero-trace exceptional locus. -/
def maxwellChosenOneSidedInfinityBadLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  ⋃ i : Fin p, ⋃ side : MaxwellOneSidedStep,
    ⋃ infinity : MaxwellSlopeInfinitySign,
      maxwellOneSidedInfinityBase U R i side infinity

/-- Closing the source-defined infinity obstruction gives an open
complement suitable for the continuous-partials argument. -/
def maxwellChosenOneSidedInfinityExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  closure (maxwellChosenOneSidedInfinityBadLocus U R)

theorem isClosed_maxwellChosenOneSidedInfinityExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    IsClosed (maxwellChosenOneSidedInfinityExceptionalLocus U R) := by
  exact isClosed_closure

/-- The fully corrected open domain removes the continuity obstruction, the
old full-trace first-order obstruction, and the residual source-defined
one-sided infinity obstruction. -/
def maxwellChosenDerivativeRegularDomain {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  maxwellChosenLineRegularDomain U R \
    maxwellChosenOneSidedInfinityExceptionalLocus U R

theorem isOpen_maxwellChosenDerivativeRegularDomain {p : ℕ}
    {U : Set (RealEuclidean p)} (hU : IsOpen U)
    (R : MaxwellRelation p 1) :
    IsOpen (maxwellChosenDerivativeRegularDomain U R) := by
  exact (isOpen_maxwellChosenLineRegularDomain hU R).sdiff
    (isClosed_maxwellChosenOneSidedInfinityExceptionalLocus U R)

theorem maxwellNoOneSidedInfiniteSlopeClustersOn_derivativeRegularDomain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    MaxwellNoOneSidedInfiniteSlopeClustersOn U R
      (maxwellChosenDerivativeRegularDomain U R) := by
  intro x hx i side infinity hinfinity
  apply hx.2
  apply subset_closure
  exact Set.mem_iUnion_of_mem i <|
    Set.mem_iUnion_of_mem side <|
      Set.mem_iUnion_of_mem infinity hinfinity

/-- If the two infinite alternatives are unavailable, the trichotomy behind
`exists_maxwellOneSidedExtendedSlopeCluster_of_sequence` retains an actual
convergent subsequence of the supplied slopes. -/
theorem exists_maxwellOneSidedFiniteSlopeCluster_subseq_of_sequence
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p}
    {source : ℕ → RealEuclidean p × ℝ} {slope : ℕ → ℝ}
    (hsource : Tendsto source atTop (nhds (x, 0)))
    (hstep : ∀ n, 0 < (source n).2)
    (hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i)
    (hpositive : x ∉
      maxwellOneSidedInfinityBase U R i side .positive)
    (hnegative : x ∉
      maxwellOneSidedInfinityBase U R i side .negative) :
    ∃ y : ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (slope ∘ φ) atTop (nhds y) ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side := by
  have hbounded : Bornology.IsBounded (Set.range slope) := by
    by_contra hnotBounded
    by_cases hbelow : BddBelow (Set.range slope)
    · have habove : ¬ BddAbove (Set.range slope) := by
        intro h
        exact hnotBounded
          (isBounded_iff_bddBelow_bddAbove.mpr ⟨hbelow, h⟩)
      have hextract : ∀ n : ℕ, ∃ k : ℕ,
          n ≤ k ∧ (n : ℝ) < slope k :=
        fun n ↦ exists_index_ge_natCast_lt_of_not_bddAbove_range
          slope habove n
      choose φ hφge hφlarge using hextract
      have hφTop : Tendsto φ atTop atTop := by
        rw [tendsto_atTop]
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hφge n)
      have hslopeTop : Tendsto (fun n ↦ slope (φ n)) atTop atTop :=
        tendsto_atTop_mono (fun n ↦ (hφlarge n).le)
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have hinvLimit :
          Tendsto (fun n ↦ (slope (φ n))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hslopeTop
      let hinfinite : MaxwellOneSidedInfiniteSlopeApproach
          U R i side .positive x :=
        { point := fun n ↦
            realEuclideanAppend
              (realEuclideanAppend (source (φ n)).1
                (fun _ : Fin 1 ↦ (slope (φ n))⁻¹))
              (fun _ : Fin 1 ↦ side.sign * (source (φ n)).2)
          point_mem := fun n ↦ by
            apply
              (realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
                U R i .positive (source (φ n)).1
                (side.sign * (source (φ n)).2)
                ((slope (φ n))⁻¹)).2
            have hpos : 0 < slope (φ n) :=
              lt_of_le_of_lt (Nat.cast_nonneg n) (hφlarge n)
            exact ⟨slope (φ n), hpoint (φ n),
              mul_inv_cancel₀ (ne_of_gt hpos), by
                simpa [MaxwellSlopeInfinitySign.AcceptsReciprocal] using
                  inv_pos.mpr hpos⟩
          step_sign := fun n ↦ by
            cases side <;>
              simpa [MaxwellOneSidedStep.Accepts,
                MaxwellOneSidedStep.sign] using hstep (φ n)
          tendsto_zeroReciprocalStep :=
            tendsto_stepLastPoint_of_source_and_value_tendsto side
              (hsource.comp hφTop) hinvLimit }
      exact hpositive
        ((mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
          U R i side .positive x).2 ⟨hinfinite⟩)
    · have hextract : ∀ n : ℕ, ∃ k : ℕ,
          n ≤ k ∧ slope k < -(n : ℝ) :=
        fun n ↦ exists_index_ge_lt_neg_natCast_of_not_bddBelow_range
          slope hbelow n
      choose φ hφge hφsmall using hextract
      have hφTop : Tendsto φ atTop atTop := by
        rw [tendsto_atTop]
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hφge n)
      have hnegNat : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have hslopeBot : Tendsto (fun n ↦ slope (φ n)) atTop atBot :=
        tendsto_atBot_mono (fun n ↦ (hφsmall n).le) hnegNat
      have hinvLimit :
          Tendsto (fun n ↦ (slope (φ n))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atBot_zero.comp hslopeBot
      let hinfinite : MaxwellOneSidedInfiniteSlopeApproach
          U R i side .negative x :=
        { point := fun n ↦
            realEuclideanAppend
              (realEuclideanAppend (source (φ n)).1
                (fun _ : Fin 1 ↦ (slope (φ n))⁻¹))
              (fun _ : Fin 1 ↦ side.sign * (source (φ n)).2)
          point_mem := fun n ↦ by
            apply
              (realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
                U R i .negative (source (φ n)).1
                (side.sign * (source (φ n)).2)
                ((slope (φ n))⁻¹)).2
            have hneg : slope (φ n) < 0 :=
              lt_of_lt_of_le (hφsmall n)
                (neg_nonpos.mpr (Nat.cast_nonneg n))
            exact ⟨slope (φ n), hpoint (φ n),
              mul_inv_cancel₀ (ne_of_lt hneg), by
                simpa [MaxwellSlopeInfinitySign.AcceptsReciprocal] using
                  (inv_lt_zero.mpr hneg)⟩
          step_sign := fun n ↦ by
            cases side <;>
              simpa [MaxwellOneSidedStep.Accepts,
                MaxwellOneSidedStep.sign] using hstep (φ n)
          tendsto_zeroReciprocalStep :=
            tendsto_stepLastPoint_of_source_and_value_tendsto side
              (hsource.comp hφTop) hinvLimit }
      exact hnegative
        ((mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
          U R i side .negative x).2 ⟨hinfinite⟩)
  obtain ⟨y, _hyClosure, φ, hφmono, hslopeLimit⟩ :=
    tendsto_subseq_of_bounded hbounded
      (fun n ↦ Set.mem_range_self n)
  have hφTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  let hfinite : MaxwellOneSidedSlopeApproach U R i side x y :=
    { point := fun n ↦
        realEuclideanAppend
          (realEuclideanAppend (source (φ n)).1
            (fun _ : Fin 1 ↦ slope (φ n)))
          (fun _ : Fin 1 ↦ side.sign * (source (φ n)).2)
      point_mem := fun n ↦ hpoint (φ n)
      step_sign := fun n ↦ by
        cases side <;>
          simpa [MaxwellOneSidedStep.Accepts,
            MaxwellOneSidedStep.sign] using hstep (φ n)
      tendsto_zeroStep :=
        tendsto_stepLastPoint_of_source_and_value_tendsto side
          (hsource.comp hφTop)
          (by simpa only [Function.comp_def] using hslopeLimit) }
  exact ⟨y, φ, hφmono, hslopeLimit,
    (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
      U R i side x y).2 ⟨hfinite⟩⟩

/-- A real sequence converges if every subsequence has a further subsequence
converging to the same point. -/
private theorem tendsto_atTop_of_subseq_has_subseq_tendsto
    {u : ℕ → ℝ} {d : ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (u ∘ φ ∘ ψ) atTop (nhds d)) :
    Tendsto u atTop (nhds d) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hnot
  push Not at hnot
  have hfrequent : ∃ᶠ n in atTop, ε ≤ dist (u n) d := by
    rw [frequently_atTop]
    exact hnot
  obtain ⟨φ, hφmono, hφfar⟩ :=
    extraction_of_frequently_atTop hfrequent
  obtain ⟨ψ, _hψmono, hlimit⟩ := h φ hφmono
  have hnear : ∀ᶠ n in atTop, dist ((u ∘ φ ∘ ψ) n) d < ε := by
    simpa only [Metric.mem_ball] using
      hlimit.eventually (Metric.ball_mem_nhds d hε)
  have hnearExists : ∃ n, dist ((u ∘ φ ∘ ψ) n) d < ε :=
    Filter.Eventually.exists hnear
  obtain ⟨n, hn⟩ := hnearExists
  exact (not_lt_of_ge (hφfar (ψ n))) hn

/-- Once the source-defined infinite alternatives are excluded, uniqueness
of the full finite zero-step trace forces convergence of the chosen
representative's quotient on either selected side. -/
theorem IsMaxwellPseudofunctionOn.tendsto_oneSidedDifferenceQuotient_of_noInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p} (hxU : x ∈ U) {d : ℝ}
    (hunique : ∀ y : ℝ,
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
          maxwellDifferenceQuotientZeroTrace U R i →
        y = d)
    (hnoInfinity : MaxwellNoOneSidedInfiniteSlopeClustersAt U R i x) :
    Tendsto
      (fun t : ℝ ↦ maxwellOneSidedDifferenceQuotient
        (maxwellChosenScalarValue R) i side (x, t))
      (𝓝[>] 0) (nhds d) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro t ht
  have htParts := tendsto_nhdsWithin_iff.mp ht
  have htZero : Tendsto t atTop (nhds 0) := htParts.1
  have htPositive : ∀ᶠ n in atTop, 0 < t n := by
    simpa only [Set.mem_Ioi] using htParts.2
  let v : RealEuclidean p := Pi.single i 1
  have hshift : Tendsto
      (fun n ↦ x + (side.sign * t n) • v) atTop (nhds x) := by
    have hsigned : Tendsto (fun n ↦ side.sign * t n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul htZero)
    simpa using
      (tendsto_const_nhds.add
        (hsigned.smul
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ v) atTop (nhds v))))
  have hshiftU : ∀ᶠ n in atTop,
      x + (side.sign * t n) • v ∈ U :=
    hshift.eventually (hU.mem_nhds hxU)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htPositive.and hshiftU)
  let step : ℕ → ℝ := fun n ↦ t (n + N)
  let source : ℕ → RealEuclidean p × ℝ := fun n ↦ (x, step n)
  let slope : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (source n)
  have hstepPositive (n : ℕ) : 0 < step n := by
    exact (hN (n + N) (by omega)).1
  have hshiftStep (n : ℕ) :
      x + (side.sign * step n) • v ∈ U := by
    exact (hN (n + N) (by omega)).2
  have hstepZero : Tendsto step atTop (nhds 0) := by
    exact htZero.comp (tendsto_add_atTop_nat N)
  have hsource : Tendsto source atTop (nhds (x, 0)) := by
    simpa only [source, nhds_prod_eq] using
      tendsto_const_nhds.prodMk hstepZero
  let G : MaxwellRelation p 1 :=
    maxwellFunctionGraph U
      (fun z : RealEuclidean p ↦
        fun _ : Fin 1 ↦ maxwellChosenScalarValue R z)
  have hGrep : MaxwellRelation.RepresentsOn G U
      (fun z : RealEuclidean p ↦
        fun _ : Fin 1 ↦ maxwellChosenScalarValue R z) :=
    MaxwellRelation.representsOn_functionGraph U
      (fun z : RealEuclidean p ↦
        fun _ : Fin 1 ↦ maxwellChosenScalarValue R z)
  have hGR : G ⊆ R := by
    simpa only [G] using hR.chosenScalarFunctionGraph_subset
  have hpoint (n : ℕ) :
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i := by
    apply maxwellStepLastDifferenceQuotientRelation_mono hGR i
    exact
      ((realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
        i hGrep side (source n).1 (source n).2 (slope n)).2
          ⟨⟨hxU, by simpa only [source, v] using hshiftStep n,
              hstepPositive n⟩,
            rfl⟩).1
  have hslope : Tendsto slope atTop (nhds d) := by
    apply tendsto_atTop_of_subseq_has_subseq_tendsto
    intro φ hφmono
    have hφTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    obtain ⟨y, ψ, hψmono, hlimit, hyTrace⟩ :=
      exists_maxwellOneSidedFiniteSlopeCluster_subseq_of_sequence
        i side
        (source := source ∘ φ) (slope := slope ∘ φ)
        (hsource.comp hφTop)
        (fun n ↦ hstepPositive (φ n))
        (fun n ↦ hpoint (φ n))
        (hnoInfinity side .positive)
        (hnoInfinity side .negative)
    have hyFull : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellDifferenceQuotientZeroTrace U R i := by
      rw [← maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i]
      cases side with
      | positive =>
          exact Or.inl (by
            simpa only [maxwellOneSidedStepZeroTrace] using hyTrace)
      | negative =>
          exact Or.inr (by
            simpa only [maxwellOneSidedStepZeroTrace] using hyTrace)
    have hyd : y = d := hunique y hyFull
    subst y
    exact ⟨ψ, hψmono, by
      simpa only [Function.comp_def] using hlimit⟩
  have htail : Tendsto
      (fun n ↦ maxwellOneSidedDifferenceQuotient
        (maxwellChosenScalarValue R) i side (x, t (n + N)))
      atTop (nhds d) := by
    simpa only [slope, source, step] using hslope
  have hall : Tendsto
      (fun n ↦ maxwellOneSidedDifferenceQuotient
        (maxwellChosenScalarValue R) i side (x, t n))
      atTop (nhds d) :=
    (tendsto_add_atTop_iff_nat N).mp htail
  simpa only [Function.comp_def] using hall

/-- Off the existing first-order exceptional locus, absence of the four
source-defined one-sided infinite clusters gives the actual coordinate line
derivative of the chosen scalar representative. -/
theorem IsMaxwellPseudofunctionOn.hasLineDerivAt_chosenScalarValue_of_noOneSidedInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (i : Fin p) {x : RealEuclidean p}
    (hx : x ∈ maxwellChosenLineRegularDomain U R)
    (hnoInfinity : MaxwellNoOneSidedInfiniteSlopeClustersAt U R i x) :
    ∃ d : ℝ, HasLineDerivAt ℝ (maxwellChosenScalarValue R) d x
      ((Pi.basisFun ℝ (Fin p)) i) := by
  have hnotCoordinate :
      x ∉ maxwellCoordinateExceptionalLocus U R i := by
    intro h
    exact hx.2 (Or.inr
      (maxwellCoordinateExceptionalLocus_subset_firstOrder U R i h))
  have hnotRaw : x ∉ maxwellCoordinateRawBadLocus U R i := by
    intro h
    exact hnotCoordinate (subset_closure h)
  have hnotMulti : x ∉ maxwellMultivaluedLocus
      (maxwellDifferenceQuotientZeroTrace U R i) := by
    intro h
    apply hnotRaw
    unfold maxwellCoordinateRawBadLocus
    aesop
  have hcluster :=
    hR.oneSidedExtendedSlopeFiber_nonempty hU i .positive hx.1
  obtain ⟨a, ha⟩ := hcluster
  cases a with
  | positiveInfinity =>
      exact False.elim <| hnoInfinity .positive .positive <|
        (positiveInfinity_mem_maxwellExtendedSlopeFiber_iff
          (maxwellPositiveStepZeroTrace U R i)
          (maxwellPositiveStepPositiveInfinityBase U R i)
          (maxwellPositiveStepNegativeInfinityBase U R i) x).mp ha
  | negativeInfinity =>
      exact False.elim <| hnoInfinity .positive .negative <|
        (negativeInfinity_mem_maxwellExtendedSlopeFiber_iff
          (maxwellPositiveStepZeroTrace U R i)
          (maxwellPositiveStepPositiveInfinityBase U R i)
          (maxwellPositiveStepNegativeInfinityBase U R i) x).mp ha
  | finite d =>
      have hdPositive : realEuclideanAppend x (fun _ : Fin 1 ↦ d) ∈
          maxwellPositiveStepZeroTrace U R i :=
        (finite_mem_maxwellExtendedSlopeFiber_iff
          (maxwellPositiveStepZeroTrace U R i)
          (maxwellPositiveStepPositiveInfinityBase U R i)
          (maxwellPositiveStepNegativeInfinityBase U R i) x d).mp ha
      have hdFull : realEuclideanAppend x (fun _ : Fin 1 ↦ d) ∈
          maxwellDifferenceQuotientZeroTrace U R i := by
        rw [← maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i]
        exact Or.inl hdPositive
      have hunique : ∀ y : ℝ,
          realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
              maxwellDifferenceQuotientZeroTrace U R i →
            y = d := by
        intro y hy
        by_contra hyd
        apply hnotMulti
        refine ⟨(fun _ : Fin 1 ↦ y), (fun _ : Fin 1 ↦ d),
          hy, hdFull, ?_⟩
        intro hfunctions
        exact hyd (congrFun hfunctions 0)
      have hright :=
        hR.tendsto_oneSidedDifferenceQuotient_of_noInfinity
          hU i .positive hx.1 hunique hnoInfinity
      have hleftPositiveParameter :=
        hR.tendsto_oneSidedDifferenceQuotient_of_noInfinity
          hU i .negative hx.1 hunique hnoInfinity
      let v : RealEuclidean p := Pi.single i 1
      let quotient : ℝ → ℝ := fun t ↦
        t⁻¹ • (maxwellChosenScalarValue R (x + t • v) -
          maxwellChosenScalarValue R x)
      have hright' : Tendsto quotient (𝓝[>] 0) (nhds d) := by
        simpa only [quotient, v, maxwellOneSidedDifferenceQuotient,
          MaxwellOneSidedStep.sign_positive, one_mul, div_eq_inv_mul,
          smul_eq_mul] using hright
      have hneg : Tendsto (fun t : ℝ ↦ -t) (𝓝[<] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have hcont : ContinuousAt (fun t : ℝ ↦ -t) 0 :=
            continuous_neg.continuousAt
          simpa using hcont.mono_left
            (show (𝓝[<] (0 : ℝ)) ≤ nhds 0 from inf_le_left)
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact neg_pos.mpr (Set.mem_Iio.mp ht)
      have hleft' : Tendsto quotient (𝓝[<] 0) (nhds d) := by
        have hcomp := hleftPositiveParameter.comp hneg
        simpa only [quotient, v, maxwellOneSidedDifferenceQuotient,
          MaxwellOneSidedStep.sign_negative, neg_mul, one_mul,
          neg_neg, div_eq_inv_mul, smul_eq_mul,
          Function.comp_def] using hcomp
      refine ⟨d, ?_⟩
      rw [hasLineDerivAt_iff_tendsto_slope_zero,
        ← nhdsLT_sup_nhdsGT, tendsto_sup]
      simpa only [quotient, v, pi_basisFun_eq_single] using
        And.intro hleft' hright'

/-- Coordinate line differentiability on the corrected regular domain,
conditional only on excluding the source-defined one-sided infinity
obstruction. -/
theorem IsMaxwellPseudofunctionOn.chosenScalar_coordinateLineDifferentiableOn_lineRegularDomain
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (hnoInfinity : MaxwellNoOneSidedInfiniteSlopeClustersOn U R
      (maxwellChosenLineRegularDomain U R)) :
    ∀ x ∈ maxwellChosenLineRegularDomain U R, ∀ i : Fin p,
      LineDifferentiableAt ℝ (maxwellChosenScalarValue R) x
        ((Pi.basisFun ℝ (Fin p)) i) := by
  intro x hx i
  obtain ⟨d, hd⟩ :=
    hR.hasLineDerivAt_chosenScalarValue_of_noOneSidedInfinity
      hU i hx (hnoInfinity x hx i)
  exact hd.lineDifferentiableAt

/-- Closedness and single-valuedness of the full zero-step trace make the
canonical coordinate line derivative continuous on any set contained in the
old first-order regular domain, once the line derivatives exist there. -/
theorem maxwellChosenCoordinateLineDerivative_continuousOn_of_subset
    {p : ℕ} {U V : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (hVU : V ⊆ U \ maxwellFirstOrderExceptionalLocus U R)
    (hline : ∀ x ∈ V, ∀ i : Fin p,
      LineDifferentiableAt ℝ (maxwellChosenScalarValue R) x
        ((Pi.basisFun ℝ (Fin p)) i))
    (i : Fin p) :
    ContinuousOn (maxwellChosenCoordinateLineDerivative R i) V := by
  let d : RealEuclidean p → ℝ :=
    maxwellChosenCoordinateLineDerivative R i
  let D : RealEuclidean p → RealEuclidean 1 :=
    fun x _ ↦ d x
  let G : MaxwellRelation p 1 :=
    maxwellDifferenceQuotientZeroTrace U R i
  have hgraph : maxwellFunctionGraph V D ⊆ G := by
    rintro _ ⟨x, hx, rfl⟩
    change realEuclideanAppend x (fun _ : Fin 1 ↦ d x) ∈ G
    exact hR.chosenScalar_coordinateLineDeriv_mem_trace hU i (hVU hx).1
      ((hline x hx i).hasLineDerivAt)
  have hclosure : closure (maxwellFunctionGraph V D) ⊆ G := by
    exact isClosed_maxwellDifferenceQuotientZeroTrace U R i
      |>.closure_subset_iff.mpr hgraph
  intro x hx
  have hnotRaw : x ∉ maxwellCoordinateRawBadLocus U R i := by
    intro hraw
    exact (hVU hx).2
      (maxwellCoordinateExceptionalLocus_subset_firstOrder U R i
        (subset_closure hraw))
  have hDcontinuous : ContinuousWithinAt D V x := by
    by_contra hbad
    rcases maxwellScalarClosureSequenceDichotomy_mathlib V D x hx hbad with
      hfinite | hpositive | hnegative
    · rcases hfinite with ⟨y₁, y₂, hy₁, hy₂, hne⟩
      have hGmulti : x ∈ maxwellMultivaluedLocus G :=
        ⟨y₁, y₂, hclosure hy₁, hclosure hy₂, hne⟩
      apply hnotRaw
      unfold maxwellCoordinateRawBadLocus
      aesop
    · have hGpositive : x ∈ maxwellPositiveInfinityBase G :=
        maxwellPositiveInfinityBase_mono hgraph hpositive
      apply hnotRaw
      unfold maxwellCoordinateRawBadLocus
      aesop
    · have hGnegative : x ∈ maxwellNegativeInfinityBase G :=
        maxwellNegativeInfinityBase_mono hgraph hnegative
      apply hnotRaw
      unfold maxwellCoordinateRawBadLocus
      aesop
  have hscalar : ContinuousWithinAt d V x := by
    have h :=
      (continuous_apply (0 : Fin 1)).continuousAt.comp_continuousWithinAt
        hDcontinuous
    simpa [D, d, Function.comp_def] using h
  simpa [d] using hscalar

/-- The corrected differentiability bridge.  The continuity-locus removal
supplies the correct open domain.  The sole remaining analytic hypothesis is
that none of the four source-defined one-sided infinite slope clusters occurs
there. -/
theorem IsMaxwellPseudofunctionOn.differentiableAt_chosenScalarValue_lineRegularDomain
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (hnoInfinity : MaxwellNoOneSidedInfiniteSlopeClustersOn U R
      (maxwellChosenLineRegularDomain U R))
    {x : RealEuclidean p}
    (hx : x ∈ maxwellChosenLineRegularDomain U R) :
    DifferentiableAt ℝ (maxwellChosenScalarValue R) x := by
  let V : Set (RealEuclidean p) :=
    maxwellChosenLineRegularDomain U R
  have hV : IsOpen V := isOpen_maxwellChosenLineRegularDomain hU R
  have hline : ∀ y ∈ V, ∀ i : Fin p,
      LineDifferentiableAt ℝ (maxwellChosenScalarValue R) y
        ((Pi.basisFun ℝ (Fin p)) i) :=
    hR.chosenScalar_coordinateLineDifferentiableOn_lineRegularDomain
      hU hnoInfinity
  have hVU : V ⊆ U \ maxwellFirstOrderExceptionalLocus U R := by
    intro y hy
    exact ⟨hy.1, fun h ↦ hy.2 (Or.inr h)⟩
  apply differentiableAt_of_continuous_coordinateLineDerivatives
    (V := V) (d := fun i ↦ maxwellChosenCoordinateLineDerivative R i)
    hV
  · intro y hy i
    exact (hline y hy i).hasLineDerivAt
  · intro i
    exact maxwellChosenCoordinateLineDerivative_continuousOn_of_subset
      hU hR hVU hline i
  · exact hx

/-- Unconditional differentiability on the fully corrected domain.  The
extra closed set makes the residual no-infinity premise of the preceding
bridge automatic. -/
theorem IsMaxwellPseudofunctionOn.differentiableAt_chosenScalarValue_derivativeRegularDomain
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    {x : RealEuclidean p}
    (hx : x ∈ maxwellChosenDerivativeRegularDomain U R) :
    DifferentiableAt ℝ (maxwellChosenScalarValue R) x := by
  let V : Set (RealEuclidean p) :=
    maxwellChosenDerivativeRegularDomain U R
  have hV : IsOpen V := isOpen_maxwellChosenDerivativeRegularDomain hU R
  have hnoInfinity : MaxwellNoOneSidedInfiniteSlopeClustersOn U R V := by
    exact maxwellNoOneSidedInfiniteSlopeClustersOn_derivativeRegularDomain
      U R
  have hline : ∀ y ∈ V, ∀ i : Fin p,
      LineDifferentiableAt ℝ (maxwellChosenScalarValue R) y
        ((Pi.basisFun ℝ (Fin p)) i) := by
    intro y hy i
    obtain ⟨d, hd⟩ :=
      hR.hasLineDerivAt_chosenScalarValue_of_noOneSidedInfinity
        hU i hy.1 (hnoInfinity y hy i)
    exact hd.lineDifferentiableAt
  have hVU : V ⊆ U \ maxwellFirstOrderExceptionalLocus U R := by
    intro y hy
    exact ⟨hy.1.1, fun h ↦ hy.1.2 (Or.inr h)⟩
  apply differentiableAt_of_continuous_coordinateLineDerivatives
    (V := V) (d := fun i ↦ maxwellChosenCoordinateLineDerivative R i)
    hV
  · intro y hy i
    exact (hline y hy i).hasLineDerivAt
  · intro i
    exact maxwellChosenCoordinateLineDerivative_continuousOn_of_subset
      hU hR hVU hline i
  · exact hx

end AbelFormalization
