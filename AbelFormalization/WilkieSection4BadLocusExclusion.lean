import AbelFormalization.WilkieSection4EndpointLoci
import AbelFormalization.WilkieSection4CardinalityStability

/-!
# Wilkie Section 4: exclusion of collision and endpoint loci

On a nonempty open base cell where the scalar fibres are finite, the positive
gap relations for collisions and for the two endpoints have empty interior.
Wilkie--Charbonnel Theorem 2.2 therefore makes their zero traces interiorless.
Simultaneous cell compatibility cannot choose the containment alternative for
an interiorless trace, so the cell avoids all three closed bad loci.

The ambient loci are formed over `C`, while fibre finiteness is only assumed
over the refined open cell `B`.  The localization lemmas below bridge that
gap: closure and positive zero-trace membership localize to an open base
restriction, and each restricted ambient gap relation is exactly the gap
relation formed over `B`.
-/

noncomputable section

open Set Filter

namespace AbelFormalization

set_option autoImplicit false

/-- A scalar relation with finite fibres has empty interior. -/
theorem interior_maxwellRelation_eq_empty_of_finite_fibers
    {p : ℕ} {R : MaxwellRelation p 1}
    (hfinite : ∀ x : RealEuclidean p, (maxwellScalarFiber R x).Finite) :
    interior R = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  let x := realEuclideanTakeLeft z
  let y := realEuclideanTakeRight z 0
  have hzEq : z = realEuclideanAppend x (fun _ : Fin 1 ↦ y) := by
    dsimp [x, y]
    rw [show (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z by
      funext i
      exact congrArg (realEuclideanTakeRight z) (Fin.eq_zero i).symm]
    exact (realEuclideanAppend_takeLeft_takeRight z).symm
  have hopen : IsOpen ((fun t : ℝ ↦
      realEuclideanAppend x (fun _ : Fin 1 ↦ t)) ⁻¹' interior R) := by
    apply (isOpen_interior : IsOpen (interior R)).preimage
    have hpair : Continuous (fun t : ℝ ↦ (x, t)) :=
      continuous_const.prodMk continuous_id
    have hcontinuous :=
      (realEuclideanAppendScalarContinuousLinearEquiv p).continuous.comp
        hpair
    simpa [Function.comp_def, realEuclideanAppendScalar] using hcontinuous
  have hy : y ∈ ((fun t : ℝ ↦
      realEuclideanAppend x (fun _ : Fin 1 ↦ t)) ⁻¹' interior R) := by
    simpa [hzEq] using hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen y hy
  have hIooSubset : Set.Ioo (y - ε) (y + ε) ⊆ maxwellScalarFiber R x := by
    intro t ht
    change realEuclideanAppend x (fun _ : Fin 1 ↦ t) ∈ R
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  exact (hfinite x).not_infinite
    ((Set.Ioo_infinite (by linarith : y - ε < y + ε)).mono hIooSubset)

theorem wilkieSection4CollisionGapRelation_finite_fibers
    {p : ℕ} {B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite) :
    ∀ x : RealEuclidean p,
      (maxwellScalarFiber
        (wilkieSection4CollisionGapRelation B A) x).Finite := by
  intro x
  by_cases hx : x ∈ B
  · let F := maxwellScalarFiber A x
    have hproduct : (F ×ˢ F).Finite := (hfinite x hx).prod (hfinite x hx)
    have himage : ((fun q : ℝ × ℝ ↦ q.2 - q.1) '' (F ×ˢ F)).Finite :=
      hproduct.image _
    apply himage.subset
    intro ε hε
    rw [mem_maxwellScalarFiber_iff,
      realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff] at hε
    rcases hε.2 with ⟨y, z, hy, hz, _hyz, rfl⟩
    exact ⟨(y, z), ⟨hy, hz⟩, rfl⟩
  · have hempty : maxwellScalarFiber
        (wilkieSection4CollisionGapRelation B A) x = ∅ := by
      ext ε
      rw [Set.mem_empty_iff_false, mem_maxwellScalarFiber_iff,
        realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff]
      simp [hx]
    rw [hempty]
    exact Set.finite_empty

theorem wilkieSection4LowerEndpointGapRelation_finite_fibers
    {p : ℕ} {B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ}
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite) :
    ∀ x : RealEuclidean p,
      (maxwellScalarFiber
        (wilkieSection4LowerEndpointGapRelation B A f) x).Finite := by
  intro x
  by_cases hx : x ∈ B
  · have himage := (hfinite x hx).image (fun y : ℝ ↦ y - f x)
    apply himage.subset
    intro ε hε
    rw [mem_maxwellScalarFiber_iff,
      realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff] at hε
    rcases hε.2.2 with ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · have hempty : maxwellScalarFiber
        (wilkieSection4LowerEndpointGapRelation B A f) x = ∅ := by
      ext ε
      rw [Set.mem_empty_iff_false, mem_maxwellScalarFiber_iff,
        realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff]
      simp [hx]
    rw [hempty]
    exact Set.finite_empty

theorem wilkieSection4UpperEndpointGapRelation_finite_fibers
    {p : ℕ} {B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ}
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite) :
    ∀ x : RealEuclidean p,
      (maxwellScalarFiber
        (wilkieSection4UpperEndpointGapRelation B A g) x).Finite := by
  intro x
  by_cases hx : x ∈ B
  · have himage := (hfinite x hx).image (fun y : ℝ ↦ g x - y)
    apply himage.subset
    intro ε hε
    rw [mem_maxwellScalarFiber_iff,
      realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff] at hε
    rcases hε.2.2 with ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · have hempty : maxwellScalarFiber
        (wilkieSection4UpperEndpointGapRelation B A g) x = ∅ := by
      ext ε
      rw [Set.mem_empty_iff_false, mem_maxwellScalarFiber_iff,
        realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff]
      simp [hx]
    rw [hempty]
    exact Set.finite_empty

theorem maxwellRelationRestrict_wilkieSection4CollisionGapRelation
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hBC : B ⊆ C) :
    maxwellRelationRestrict (wilkieSection4CollisionGapRelation C A) B =
      wilkieSection4CollisionGapRelation B A := by
  ext z
  let x := realEuclideanTakeLeft z
  let ε := realEuclideanTakeRight z 0
  have hzEq : z = realEuclideanAppend x (fun _ : Fin 1 ↦ ε) := by
    dsimp [x, ε]
    rw [show (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z by
      funext i
      exact congrArg (realEuclideanTakeRight z) (Fin.eq_zero i).symm]
    exact (realEuclideanAppend_takeLeft_takeRight z).symm
  rw [hzEq, realEuclideanAppend_mem_maxwellRelationRestrict_iff,
    realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff,
    realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff]
  constructor
  · rintro ⟨⟨_hxC, hdata⟩, hxB⟩
    exact ⟨hxB, hdata⟩
  · rintro ⟨hxB, hdata⟩
    exact ⟨⟨hBC hxB, hdata⟩, hxB⟩

theorem maxwellRelationRestrict_wilkieSection4LowerEndpointGapRelation
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (hBC : B ⊆ C) :
    maxwellRelationRestrict
        (wilkieSection4LowerEndpointGapRelation C A f) B =
      wilkieSection4LowerEndpointGapRelation B A f := by
  ext z
  let x := realEuclideanTakeLeft z
  let ε := realEuclideanTakeRight z 0
  have hzEq : z = realEuclideanAppend x (fun _ : Fin 1 ↦ ε) := by
    dsimp [x, ε]
    rw [show (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z by
      funext i
      exact congrArg (realEuclideanTakeRight z) (Fin.eq_zero i).symm]
    exact (realEuclideanAppend_takeLeft_takeRight z).symm
  rw [hzEq, realEuclideanAppend_mem_maxwellRelationRestrict_iff,
    realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff,
    realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff]
  constructor
  · rintro ⟨⟨_hxC, hdata⟩, hxB⟩
    exact ⟨hxB, hdata⟩
  · rintro ⟨hxB, hdata⟩
    exact ⟨⟨hBC hxB, hdata⟩, hxB⟩

theorem maxwellRelationRestrict_wilkieSection4UpperEndpointGapRelation
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ} (hBC : B ⊆ C) :
    maxwellRelationRestrict
        (wilkieSection4UpperEndpointGapRelation C A g) B =
      wilkieSection4UpperEndpointGapRelation B A g := by
  ext z
  let x := realEuclideanTakeLeft z
  let ε := realEuclideanTakeRight z 0
  have hzEq : z = realEuclideanAppend x (fun _ : Fin 1 ↦ ε) := by
    dsimp [x, ε]
    rw [show (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z by
      funext i
      exact congrArg (realEuclideanTakeRight z) (Fin.eq_zero i).symm]
    exact (realEuclideanAppend_takeLeft_takeRight z).symm
  rw [hzEq, realEuclideanAppend_mem_maxwellRelationRestrict_iff,
    realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff,
    realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff]
  constructor
  · rintro ⟨⟨_hxC, hdata⟩, hxB⟩
    exact ⟨hxB, hdata⟩
  · rintro ⟨hxB, hdata⟩
    exact ⟨⟨hBC hxB, hdata⟩, hxB⟩

/-- Restricting the base of a known graph preserves family membership. -/
theorem charbonnelRestrictedGraph_mem_charbonnelClosure_of_subset
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {C B : Set (RealEuclidean p)}
    (hBC : B ⊆ C) (hBmem : B ∈ charbonnelClosure S p)
    {f : RealEuclidean p → ℝ}
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1)) :
    charbonnelRestrictedGraph B f ∈ charbonnelClosure S (p + 1) := by
  have hpreimage : realEuclideanTakeLeftLinearMap p 1 ⁻¹' B ∈
      charbonnelClosure S (p + 1) :=
    hC.linear_preimage_mem (by omega) hp hBmem
      (realEuclideanTakeLeftLinearMap p 1)
  have heq : charbonnelRestrictedGraph B f =
      charbonnelRestrictedGraph C f ∩
        realEuclideanTakeLeftLinearMap p 1 ⁻¹' B := by
    ext z
    simp only [charbonnelRestrictedGraph, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_preimage,
      realEuclideanTakeLeftLinearMap_apply]
    constructor
    · rintro ⟨hzB, hvalue⟩
      exact ⟨⟨hBC hzB, hvalue⟩, hzB⟩
    · rintro ⟨⟨_hzC, hvalue⟩, hzB⟩
      exact ⟨hzB, hvalue⟩
  rw [heq]
  exact hC.ws1_inter (by omega) hfGraph hpreimage

/-- Closure membership localizes after restricting the base to an open set. -/
theorem mem_closure_maxwellRelationRestrict_of_isOpen_base
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

theorem maxwellRelationRestrict_charbonnelPositiveLastPart
    {p : ℕ} (R : MaxwellRelation p 1)
    (B : Set (RealEuclidean p)) :
    maxwellRelationRestrict (charbonnelPositiveLastPart R) B =
      charbonnelPositiveLastPart (maxwellRelationRestrict R B) := by
  ext z
  simp [maxwellRelationRestrict, charbonnelPositiveLastPart,
    and_left_comm, and_comm]

/-- The positive zero trace of a scalar relation localizes to every open
base neighbourhood. -/
theorem mem_charbonnelPositiveZeroTrace_restrict_of_isOpen
    {p : ℕ} {R : MaxwellRelation p 1}
    {B : Set (RealEuclidean p)} (hB : IsOpen B)
    {x : RealEuclidean p} (hxB : x ∈ B)
    (hx : x ∈ charbonnelPositiveZeroTrace R) :
    x ∈ charbonnelPositiveZeroTrace (maxwellRelationRestrict R B) := by
  change charbonnelAppendLastCoordinate x 0 ∈
    closure (charbonnelPositiveLastPart R) at hx
  change charbonnelAppendLastCoordinate x 0 ∈
    closure (charbonnelPositiveLastPart (maxwellRelationRestrict R B))
  rw [← maxwellRelationRestrict_charbonnelPositiveLastPart]
  exact mem_closure_maxwellRelationRestrict_of_isOpen_base hB hxB hx

/-- Every collision gap has positive displayed coordinate. -/
theorem wilkieSection4CollisionGapRelation_output_pos
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {z : RealEuclidean (p + 1)}
    (hz : z ∈ wilkieSection4CollisionGapRelation C A) :
    0 < realEuclideanTakeRight z 0 := by
  have hrightConst :
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  have hz' : realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) ∈
        wilkieSection4CollisionGapRelation C A := by
    rw [hrightConst, realEuclideanAppend_takeLeft_takeRight]
    exact hz
  rcases (realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff
    C A (realEuclideanTakeLeft z) (realEuclideanTakeRight z 0)).mp hz' with
    ⟨_hx, y, w, _hy, _hw, hyw, heq⟩
  linarith

theorem wilkieSection4CollisionGapRelation_subset_positive
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    wilkieSection4CollisionGapRelation C A ⊆
      charbonnelPositiveLastCoordinateLocus p := by
  intro z hz
  change 0 < z (Fin.last p)
  have h := wilkieSection4CollisionGapRelation_output_pos hz
  have hindex : Fin.natAdd p (0 : Fin 1) = Fin.last p := Fin.ext rfl
  simpa [realEuclideanTakeRight, hindex] using h

theorem wilkieSection4LowerEndpointGapRelation_subset_positive
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) :
    wilkieSection4LowerEndpointGapRelation C A f ⊆
      charbonnelPositiveLastCoordinateLocus p := by
  intro z hz
  change 0 < z (Fin.last p)
  have h := wilkieSection4LowerEndpointGapRelation_output_pos hz
  have hindex : Fin.natAdd p (0 : Fin 1) = Fin.last p := Fin.ext rfl
  simpa [realEuclideanTakeRight, hindex] using h

theorem wilkieSection4UpperEndpointGapRelation_subset_positive
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) :
    wilkieSection4UpperEndpointGapRelation C A g ⊆
      charbonnelPositiveLastCoordinateLocus p := by
  intro z hz
  change 0 < z (Fin.last p)
  have h := wilkieSection4UpperEndpointGapRelation_output_pos hz
  have hindex : Fin.natAdd p (0 : Fin 1) = Fin.last p := Fin.ext rfl
  simpa [realEuclideanTakeRight, hindex] using h

theorem mem_charbonnelPositiveZeroTrace_collisionGapRelation_of_mem_locus
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBC : B ⊆ C)
    {x : RealEuclidean p} (hxB : x ∈ B)
    (hx : x ∈ wilkieSection4CollisionLocus C A) :
    x ∈ charbonnelPositiveZeroTrace
      (wilkieSection4CollisionGapRelation B A) := by
  have hxTrace : x ∈ charbonnelPositiveZeroTrace
      (wilkieSection4CollisionGapRelation C A) := by
    rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure
      (wilkieSection4CollisionGapRelation_subset_positive C A)]
    exact hx
  have hxLocal :=
    mem_charbonnelPositiveZeroTrace_restrict_of_isOpen hBopen hxB hxTrace
  rwa [maxwellRelationRestrict_wilkieSection4CollisionGapRelation hBC]
    at hxLocal

theorem mem_charbonnelPositiveZeroTrace_lowerEndpointGapRelation_of_mem_locus
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ}
    (hBopen : IsOpen B) (hBC : B ⊆ C)
    {x : RealEuclidean p} (hxB : x ∈ B)
    (hx : x ∈ wilkieSection4LowerEndpointLocus C A f) :
    x ∈ charbonnelPositiveZeroTrace
      (wilkieSection4LowerEndpointGapRelation B A f) := by
  have hxTrace : x ∈ charbonnelPositiveZeroTrace
      (wilkieSection4LowerEndpointGapRelation C A f) := by
    rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure
      (wilkieSection4LowerEndpointGapRelation_subset_positive C A f)]
    exact hx
  have hxLocal :=
    mem_charbonnelPositiveZeroTrace_restrict_of_isOpen hBopen hxB hxTrace
  rwa [maxwellRelationRestrict_wilkieSection4LowerEndpointGapRelation hBC]
    at hxLocal

theorem mem_charbonnelPositiveZeroTrace_upperEndpointGapRelation_of_mem_locus
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ}
    (hBopen : IsOpen B) (hBC : B ⊆ C)
    {x : RealEuclidean p} (hxB : x ∈ B)
    (hx : x ∈ wilkieSection4UpperEndpointLocus C A g) :
    x ∈ charbonnelPositiveZeroTrace
      (wilkieSection4UpperEndpointGapRelation B A g) := by
  have hxTrace : x ∈ charbonnelPositiveZeroTrace
      (wilkieSection4UpperEndpointGapRelation C A g) := by
    rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure
      (wilkieSection4UpperEndpointGapRelation_subset_positive C A g)]
    exact hx
  have hxLocal :=
    mem_charbonnelPositiveZeroTrace_restrict_of_isOpen hBopen hxB hxTrace
  rwa [maxwellRelationRestrict_wilkieSection4UpperEndpointGapRelation hBC]
    at hxLocal

theorem interior_charbonnelPositiveZeroTrace_collisionGapRelation_eq_empty
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {B : Set (RealEuclidean p)}
    (hBmem : B ∈ charbonnelClosure S p)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite) :
    interior (charbonnelPositiveZeroTrace
      (wilkieSection4CollisionGapRelation B A)) = ∅ := by
  have hRmem : wilkieSection4CollisionGapRelation B A ∈
      charbonnelClosure S (p + 1) :=
    wilkieSection4CollisionGapRelation_mem_charbonnelClosure
      hC hp hBmem hAmem
  exact (h22 hp hRmem
    (wilkieSection4CollisionGapRelation_subset_positive B A)).2
      (interior_maxwellRelation_eq_empty_of_finite_fibers
        (wilkieSection4CollisionGapRelation_finite_fibers hfinite))

theorem interior_charbonnelPositiveZeroTrace_lowerEndpointGapRelation_eq_empty
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {B : Set (RealEuclidean p)}
    (hBmem : B ∈ charbonnelClosure S p)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    {f : RealEuclidean p → ℝ}
    (hfGraph : charbonnelRestrictedGraph B f ∈
      charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite) :
    interior (charbonnelPositiveZeroTrace
      (wilkieSection4LowerEndpointGapRelation B A f)) = ∅ := by
  have hRmem : wilkieSection4LowerEndpointGapRelation B A f ∈
      charbonnelClosure S (p + 1) :=
    wilkieSection4LowerEndpointGapRelation_mem_charbonnelClosure
      hC hp hBmem hAmem hfGraph
  exact (h22 hp hRmem
    (wilkieSection4LowerEndpointGapRelation_subset_positive B A f)).2
      (interior_maxwellRelation_eq_empty_of_finite_fibers
        (wilkieSection4LowerEndpointGapRelation_finite_fibers hfinite))

theorem interior_charbonnelPositiveZeroTrace_upperEndpointGapRelation_eq_empty
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {B : Set (RealEuclidean p)}
    (hBmem : B ∈ charbonnelClosure S p)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    {g : RealEuclidean p → ℝ}
    (hgGraph : charbonnelRestrictedGraph B g ∈
      charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite) :
    interior (charbonnelPositiveZeroTrace
      (wilkieSection4UpperEndpointGapRelation B A g)) = ∅ := by
  have hRmem : wilkieSection4UpperEndpointGapRelation B A g ∈
      charbonnelClosure S (p + 1) :=
    wilkieSection4UpperEndpointGapRelation_mem_charbonnelClosure
      hC hp hBmem hAmem hgGraph
  exact (h22 hp hRmem
    (wilkieSection4UpperEndpointGapRelation_subset_positive B A g)).2
      (interior_maxwellRelation_eq_empty_of_finite_fibers
        (wilkieSection4UpperEndpointGapRelation_finite_fibers hfinite))

/-- Compatibility with a set that localizes into an interiorless set forces
the disjoint alternative on a nonempty open base. -/
theorem disjoint_of_compatible_of_local_subset_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {B L T : Set X}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hlocal : B ∩ L ⊆ T) (hTempty : interior T = ∅)
    (hcompatible : B ⊆ L ∨ Disjoint B L) :
    Disjoint B L := by
  rcases hcompatible with hsubset | hdisjoint
  · have hBT : B ⊆ T := fun x hxB ↦ hlocal ⟨hxB, hsubset hxB⟩
    have hBInterior : B ⊆ interior T := interior_maximal hBT hBopen
    obtain ⟨x, hxB⟩ := hBnonempty
    have hxEmpty : x ∈ (∅ : Set X) := by
      rw [← hTempty]
      exact hBInterior hxB
    exact hxEmpty.elim
  · exact hdisjoint

theorem disjoint_wilkieSection4CollisionLocus_of_finite_fibers_of_compatible
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {C B : Set (RealEuclidean p)}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p) (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite)
    (hcompatible : B ⊆ wilkieSection4CollisionLocus C A ∨
      Disjoint B (wilkieSection4CollisionLocus C A)) :
    Disjoint B (wilkieSection4CollisionLocus C A) := by
  apply disjoint_of_compatible_of_local_subset_interior_eq_empty
    hBopen hBnonempty
    (T := charbonnelPositiveZeroTrace
      (wilkieSection4CollisionGapRelation B A))
  · rintro x ⟨hxB, hxLocus⟩
    exact mem_charbonnelPositiveZeroTrace_collisionGapRelation_of_mem_locus
      hBopen hBC hxB hxLocus
  · exact interior_charbonnelPositiveZeroTrace_collisionGapRelation_eq_empty
      hC h22 hp hBmem hAmem hfinite
  · exact hcompatible

theorem disjoint_wilkieSection4LowerEndpointLocus_of_finite_fibers_of_compatible
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {C B : Set (RealEuclidean p)}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p) (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    {f : RealEuclidean p → ℝ}
    (hfGraph : charbonnelRestrictedGraph B f ∈
      charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite)
    (hcompatible : B ⊆ wilkieSection4LowerEndpointLocus C A f ∨
      Disjoint B (wilkieSection4LowerEndpointLocus C A f)) :
    Disjoint B (wilkieSection4LowerEndpointLocus C A f) := by
  apply disjoint_of_compatible_of_local_subset_interior_eq_empty
    hBopen hBnonempty
    (T := charbonnelPositiveZeroTrace
      (wilkieSection4LowerEndpointGapRelation B A f))
  · rintro x ⟨hxB, hxLocus⟩
    exact mem_charbonnelPositiveZeroTrace_lowerEndpointGapRelation_of_mem_locus
      hBopen hBC hxB hxLocus
  · exact interior_charbonnelPositiveZeroTrace_lowerEndpointGapRelation_eq_empty
      hC h22 hp hBmem hAmem hfGraph hfinite
  · exact hcompatible

theorem disjoint_wilkieSection4UpperEndpointLocus_of_finite_fibers_of_compatible
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {C B : Set (RealEuclidean p)}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p) (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    {g : RealEuclidean p → ℝ}
    (hgGraph : charbonnelRestrictedGraph B g ∈
      charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite)
    (hcompatible : B ⊆ wilkieSection4UpperEndpointLocus C A g ∨
      Disjoint B (wilkieSection4UpperEndpointLocus C A g)) :
    Disjoint B (wilkieSection4UpperEndpointLocus C A g) := by
  apply disjoint_of_compatible_of_local_subset_interior_eq_empty
    hBopen hBnonempty
    (T := charbonnelPositiveZeroTrace
      (wilkieSection4UpperEndpointGapRelation B A g))
  · rintro x ⟨hxB, hxLocus⟩
    exact mem_charbonnelPositiveZeroTrace_upperEndpointGapRelation_of_mem_locus
      hBopen hBC hxB hxLocus
  · exact interior_charbonnelPositiveZeroTrace_upperEndpointGapRelation_eq_empty
      hC h22 hp hBmem hAmem hgGraph hfinite
  · exact hcompatible

/-- On a nonempty open base with finite fibres, simultaneous compatibility
with Wilkie's collision and endpoint zero-trace loci forces avoidance of all
three loci. -/
theorem disjoint_wilkieSection4_badLoci_of_finite_fibers_of_compatible
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {C B : Set (RealEuclidean p)}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p) (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    {f g : RealEuclidean p → ℝ}
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    (hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite)
    (hcollisionCompatible :
      B ⊆ wilkieSection4CollisionLocus C A ∨
        Disjoint B (wilkieSection4CollisionLocus C A))
    (hlowerCompatible :
      B ⊆ wilkieSection4LowerEndpointLocus C A f ∨
        Disjoint B (wilkieSection4LowerEndpointLocus C A f))
    (hupperCompatible :
      B ⊆ wilkieSection4UpperEndpointLocus C A g ∨
        Disjoint B (wilkieSection4UpperEndpointLocus C A g)) :
    Disjoint B (wilkieSection4CollisionLocus C A) ∧
      Disjoint B (wilkieSection4LowerEndpointLocus C A f) ∧
      Disjoint B (wilkieSection4UpperEndpointLocus C A g) := by
  have hfGraphB : charbonnelRestrictedGraph B f ∈
      charbonnelClosure S (p + 1) :=
    charbonnelRestrictedGraph_mem_charbonnelClosure_of_subset
      hC hp hBC hBmem hfGraph
  have hgGraphB : charbonnelRestrictedGraph B g ∈
      charbonnelClosure S (p + 1) :=
    charbonnelRestrictedGraph_mem_charbonnelClosure_of_subset
      hC hp hBC hBmem hgGraph
  exact ⟨
    disjoint_wilkieSection4CollisionLocus_of_finite_fibers_of_compatible
      hC h22 hp hBopen hBnonempty hBmem hBC hAmem hfinite
        hcollisionCompatible,
    disjoint_wilkieSection4LowerEndpointLocus_of_finite_fibers_of_compatible
      hC h22 hp hBopen hBnonempty hBmem hBC hAmem hfGraphB hfinite
        hlowerCompatible,
    disjoint_wilkieSection4UpperEndpointLocus_of_finite_fibers_of_compatible
      hC h22 hp hBopen hBnonempty hBmem hBC hAmem hgGraphB hfinite
        hupperCompatible⟩

/-- Uniform finite-cardinality version of the simultaneous bad-locus
exclusion theorem. -/
theorem disjoint_wilkieSection4_badLoci_of_uniform_cardinality_of_compatible
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) {C B : Set (RealEuclidean p)}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p) (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    {f g : RealEuclidean p → ℝ}
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    (hcard : ∀ x ∈ B, (maxwellScalarFiber A x).encard < (N : ℕ∞))
    (hcollisionCompatible :
      B ⊆ wilkieSection4CollisionLocus C A ∨
        Disjoint B (wilkieSection4CollisionLocus C A))
    (hlowerCompatible :
      B ⊆ wilkieSection4LowerEndpointLocus C A f ∨
        Disjoint B (wilkieSection4LowerEndpointLocus C A f))
    (hupperCompatible :
      B ⊆ wilkieSection4UpperEndpointLocus C A g ∨
        Disjoint B (wilkieSection4UpperEndpointLocus C A g)) :
    Disjoint B (wilkieSection4CollisionLocus C A) ∧
      Disjoint B (wilkieSection4LowerEndpointLocus C A f) ∧
      Disjoint B (wilkieSection4UpperEndpointLocus C A g) := by
  have hfinite : ∀ x ∈ B, (maxwellScalarFiber A x).Finite := by
    intro x hxB
    rw [← Set.encard_lt_top_iff]
    exact (hcard x hxB).trans (by simp)
  exact disjoint_wilkieSection4_badLoci_of_finite_fibers_of_compatible
    hC h22 hp hBopen hBnonempty hBmem hBC hAmem hfGraph hgGraph hfinite
      hcollisionCompatible hlowerCompatible hupperCompatible

end AbelFormalization
