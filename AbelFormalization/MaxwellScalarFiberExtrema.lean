import AbelFormalization.MaxwellLocalFiberCardinality

/-!
# Extremal selectors for finite scalar fibers

Figueiredo's proof of Lemma 2.2.2 uses both endpoints of a finite vertical
fiber of the closed graph.  `MaxwellWeakSelection` already constructs the
minimum by increasingly ordering the fiber.  This file obtains the maximum
without a second incidence calculation: reflect the final coordinate, apply
the minimum construction, and reflect back.

The results below are deliberately independent of the discontinuity-locus
assembly.  They provide the reflected relation, exact-cardinality transport,
minimum/maximum order properties, a Charbonnel-family maximum graph, and the
elementary closure approximation used after an extremal value has been
selected.
-/

noncomputable section

open Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Reflection of scalar relations -/

/-- Reflect the unique output coordinate of a scalar relation. -/
def maxwellScalarRelationReflection {p : ℕ}
    (R : MaxwellRelation p 1) : MaxwellRelation p 1 :=
  maxwellLastCoordinateReflection p '' R

@[simp]
theorem maxwellLastCoordinateReflection_apply_apply {p : ℕ}
    (z : RealEuclidean (p + 1)) :
    maxwellLastCoordinateReflection p
        (maxwellLastCoordinateReflection p z) = z := by
  simpa only [maxwellLastCoordinateReflection_symm] using
    (maxwellLastCoordinateReflection p).symm_apply_apply z

@[simp]
theorem maxwellLastCoordinateReflection_apply_append_scalar {p : ℕ}
    (x : RealEuclidean p) (y : ℝ) :
    maxwellLastCoordinateReflection p
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ -y) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [maxwellLastCoordinateReflection]
  · have hj : j.castSucc = Fin.castAdd 1 j := by
      apply Fin.ext
      rfl
    have hne : Fin.castAdd 1 j ≠ Fin.last p := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    rw [hj]
    simp [maxwellLastCoordinateReflection, realEuclideanAppend, hne]

@[simp]
theorem mem_maxwellLastCoordinateReflection_image_iff
    {p : ℕ} {A : Set (RealEuclidean (p + 1))}
    {z : RealEuclidean (p + 1)} :
    z ∈ maxwellLastCoordinateReflection p '' A ↔
      maxwellLastCoordinateReflection p z ∈ A := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨maxwellLastCoordinateReflection p z, hz, by simp⟩

@[simp]
theorem realEuclideanAppend_mem_maxwellScalarRelationReflection_iff
    {p : ℕ} (R : MaxwellRelation p 1)
    (x : RealEuclidean p) (y : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellScalarRelationReflection R ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ -y) ∈ R := by
  rw [maxwellScalarRelationReflection,
    mem_maxwellLastCoordinateReflection_image_iff,
    maxwellLastCoordinateReflection_apply_append_scalar]

@[simp]
theorem mem_maxwellScalarFiber_reflection_iff
    {p : ℕ} (R : MaxwellRelation p 1)
    (x : RealEuclidean p) (y : ℝ) :
    y ∈ maxwellScalarFiber (maxwellScalarRelationReflection R) x ↔
      -y ∈ maxwellScalarFiber R x := by
  exact realEuclideanAppend_mem_maxwellScalarRelationReflection_iff R x y

theorem maxwellScalarFiber_reflection_eq {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    maxwellScalarFiber (maxwellScalarRelationReflection R) x =
      (fun y : ℝ ↦ -y) '' maxwellScalarFiber R x := by
  ext y
  constructor
  · intro hy
    refine ⟨-y, ?_, by simp⟩
    simpa using
      (mem_maxwellScalarFiber_reflection_iff R x y).mp hy
  · rintro ⟨z, hz, rfl⟩
    apply (mem_maxwellScalarFiber_reflection_iff R x (-z)).mpr
    simpa using hz

theorem maxwellScalarFiber_reflection_finite {p : ℕ}
    {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite) :
    (maxwellScalarFiber (maxwellScalarRelationReflection R) x).Finite := by
  rw [maxwellScalarFiber_reflection_eq]
  exact hfinite.image (fun y : ℝ ↦ -y)

theorem maxwellScalarFiber_reflection_ncard {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    (maxwellScalarFiber (maxwellScalarRelationReflection R) x).ncard =
      (maxwellScalarFiber R x).ncard := by
  rw [maxwellScalarFiber_reflection_eq,
    Set.ncard_image_of_injective _ neg_injective]

theorem maxwellScalarRelationReflection_exactFiberCardinality
    {p k : ℕ} {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ U,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k + 1) :
    ∀ x ∈ U,
      (maxwellScalarFiber (maxwellScalarRelationReflection R) x).Finite ∧
      (maxwellScalarFiber (maxwellScalarRelationReflection R) x).ncard =
        k + 1 := by
  intro x hx
  exact ⟨maxwellScalarFiber_reflection_finite (hfiber x hx).1,
    (maxwellScalarFiber_reflection_ncard R x).trans (hfiber x hx).2⟩

/-! ## Order properties of the existing minimum selector -/

/-- The first entry of a full increasing enumeration is below every point
of the fiber. -/
theorem maxwellOrderedScalarFiberWitness_le_of_mem
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    {y z : ℝ}
    (hwitness : MaxwellOrderedScalarFiberWitness R k x y)
    (hz : z ∈ maxwellScalarFiber R x) :
    y ≤ z := by
  obtain ⟨values, hzero, hstep, hvalues⟩ := hwitness
  have hmono : StrictMono values :=
    Fin.strictMono_iff_lt_succ.mpr hstep
  have hrange : Set.range values = maxwellScalarFiber R x := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨i, rfl⟩
      exact hvalues i
    · rw [hcard, Set.ncard_range_of_injective hmono.injective]
      simp
    · exact hfinite
  have hzrange : z ∈ Set.range values := by
    rw [hrange]
    exact hz
  obtain ⟨i, rfl⟩ := hzrange
  rw [← hzero]
  exact hmono.monotone (Fin.zero_le i)

/-- The value constructed by the positive-increment formula is the minimum
of an exact finite fiber. -/
theorem maxwellOrderedScalarValue_le_of_mem
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    {z : ℝ} (hz : z ∈ maxwellScalarFiber R x) :
    maxwellOrderedScalarValue R k x ≤ z := by
  have hex : ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y :=
    exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ hfinite hcard
  exact maxwellOrderedScalarFiberWitness_le_of_mem hfinite hcard
    (maxwellOrderedScalarValue_spec hex) hz

theorem maxwellOrderedScalarValue_mem
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellOrderedScalarValue R k x ∈ maxwellScalarFiber R x := by
  have hex : ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y :=
    exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ hfinite hcard
  obtain ⟨values, hzero, _hstep, hvalues⟩ :=
    maxwellOrderedScalarValue_spec hex
  have hfirst := hvalues 0
  rwa [hzero] at hfirst

theorem maxwellOrderedScalarValue_lt_of_mem_of_ne
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    {z : ℝ} (hz : z ∈ maxwellScalarFiber R x)
    (hne : maxwellOrderedScalarValue R k x ≠ z) :
    maxwellOrderedScalarValue R k x < z :=
  lt_of_le_of_ne (maxwellOrderedScalarValue_le_of_mem hfinite hcard hz) hne

/-! ## The reflected maximum selector -/

/-- Maximum of an exact finite scalar fiber, totalized in the same way as
the existing ordered minimum outside the exact-cardinality locus. -/
noncomputable def maxwellOrderedScalarMaximumValue {p : ℕ}
    (R : MaxwellRelation p 1) (k : ℕ)
    (x : RealEuclidean p) : ℝ :=
  -maxwellOrderedScalarValue (maxwellScalarRelationReflection R) k x

/-- One-dimensional Euclidean form of the reflected maximum. -/
noncomputable def maxwellOrderedScalarMaximumSelector {p : ℕ}
    (R : MaxwellRelation p 1) (k : ℕ) :
    RealEuclidean p → RealEuclidean 1 :=
  fun x _ ↦ maxwellOrderedScalarMaximumValue R k x

theorem maxwellOrderedScalarMaximumValue_mem
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellOrderedScalarMaximumValue R k x ∈ maxwellScalarFiber R x := by
  have hrefFinite :
      (maxwellScalarFiber (maxwellScalarRelationReflection R) x).Finite :=
    maxwellScalarFiber_reflection_finite hfinite
  have hrefCard :
      (maxwellScalarFiber (maxwellScalarRelationReflection R) x).ncard =
        k + 1 :=
    (maxwellScalarFiber_reflection_ncard R x).trans hcard
  have hmin := maxwellOrderedScalarValue_mem hrefFinite hrefCard
  have hreflected :=
    (mem_maxwellScalarFiber_reflection_iff R x
      (maxwellOrderedScalarValue
        (maxwellScalarRelationReflection R) k x)).mp hmin
  simpa only [maxwellOrderedScalarMaximumValue] using hreflected

theorem le_maxwellOrderedScalarMaximumValue_of_mem
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    {z : ℝ} (hz : z ∈ maxwellScalarFiber R x) :
    z ≤ maxwellOrderedScalarMaximumValue R k x := by
  have hrefFinite :
      (maxwellScalarFiber (maxwellScalarRelationReflection R) x).Finite :=
    maxwellScalarFiber_reflection_finite hfinite
  have hrefCard :
      (maxwellScalarFiber (maxwellScalarRelationReflection R) x).ncard =
        k + 1 :=
    (maxwellScalarFiber_reflection_ncard R x).trans hcard
  have hzreflected : -z ∈
      maxwellScalarFiber (maxwellScalarRelationReflection R) x := by
    apply (mem_maxwellScalarFiber_reflection_iff R x (-z)).mpr
    simpa using hz
  have hmin := maxwellOrderedScalarValue_le_of_mem
    hrefFinite hrefCard hzreflected
  have hneg := neg_le_neg hmin
  simpa only [neg_neg, maxwellOrderedScalarMaximumValue] using hneg

theorem lt_maxwellOrderedScalarMaximumValue_of_mem_of_ne
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    {z : ℝ} (hz : z ∈ maxwellScalarFiber R x)
    (hne : z ≠ maxwellOrderedScalarMaximumValue R k x) :
    z < maxwellOrderedScalarMaximumValue R k x :=
  lt_of_le_of_ne (le_maxwellOrderedScalarMaximumValue_of_mem
    hfinite hcard hz) hne

/-! ## A family-member graph for the maximum -/

/-- Reflect the minimum-selection graph of the reflected relation back to
the original scalar coordinates. -/
def maxwellOrderedScalarMaximumSelectionGraph {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (k : ℕ) :
    Set (RealEuclidean (p + 1)) :=
  maxwellLastCoordinateReflection p ''
    maxwellOrderedScalarSelectionGraph U
      (maxwellScalarRelationReflection R) k

@[simp]
theorem realEuclideanAppend_mem_maxwellOrderedScalarMaximumSelectionGraph_iff
    {p k : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (x : RealEuclidean p) (y : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOrderedScalarMaximumSelectionGraph U R k ↔
      x ∈ U ∧
        MaxwellOrderedScalarFiberWitness
          (maxwellScalarRelationReflection R) k x (-y) := by
  rw [maxwellOrderedScalarMaximumSelectionGraph,
    mem_maxwellLastCoordinateReflection_image_iff,
    maxwellLastCoordinateReflection_apply_append_scalar,
    realEuclideanAppend_mem_maxwellOrderedScalarSelectionGraph_iff]

theorem maxwellOrderedScalarMaximumSelectionGraph_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p k : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellOrderedScalarMaximumSelectionGraph U R k ∈
      charbonnelClosure S (p + 1) := by
  have hreflected : maxwellScalarRelationReflection R ∈
      charbonnelClosure S (p + 1) :=
    hC.ws4_linearEquiv (by omega) hR
      (maxwellLastCoordinateReflection p)
  have hminimum :=
    maxwellOrderedScalarSelectionGraph_mem_charbonnelClosure
      hC hp hU hreflected (k := k)
  exact hC.ws4_linearEquiv (by omega) hminimum
    (maxwellLastCoordinateReflection p)

theorem maxwellOrderedScalarMaximumSelectionGraph_subset
    {p k : ℕ} {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} :
    maxwellOrderedScalarMaximumSelectionGraph U R k ⊆ R := by
  intro z hz
  have hzminimum : maxwellLastCoordinateReflection p z ∈
      maxwellOrderedScalarSelectionGraph U
        (maxwellScalarRelationReflection R) k :=
    (mem_maxwellLastCoordinateReflection_image_iff).mp hz
  have hzreflected : maxwellLastCoordinateReflection p z ∈
      maxwellScalarRelationReflection R :=
    maxwellOrderedScalarSelectionGraph_subset hzminimum
  have hzoriginal : maxwellLastCoordinateReflection p
      (maxwellLastCoordinateReflection p z) ∈ R :=
    (mem_maxwellLastCoordinateReflection_image_iff).mp hzreflected
  simpa using hzoriginal

/-- Exact fiber cardinality identifies the reflected incidence graph with
the graph of the maximum selector. -/
theorem maxwellOrderedScalarMaximumSelectionGraph_eq_functionGraph
    {p k : ℕ} {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ U,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellOrderedScalarMaximumSelectionGraph U R k =
      maxwellFunctionGraph U
        (maxwellOrderedScalarMaximumSelector R k) := by
  have hrefiber :=
    maxwellScalarRelationReflection_exactFiberCardinality hfiber
  ext z
  have hyCoordinates : realEuclideanTakeRight z =
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) := by
    funext i
    rw [show i = 0 from Fin.eq_zero i]
  rw [← realEuclideanAppend_takeLeft_takeRight (n := p) (m := 1) z,
    hyCoordinates,
    realEuclideanAppend_mem_maxwellOrderedScalarMaximumSelectionGraph_iff,
    realEuclideanAppend_mem_maxwellFunctionGraph_iff]
  constructor
  · rintro ⟨hx, hy⟩
    have hex : ∃ a : ℝ,
        MaxwellOrderedScalarFiberWitness
          (maxwellScalarRelationReflection R) k
          (realEuclideanTakeLeft z) a :=
      exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ
        (hrefiber (realEuclideanTakeLeft z) hx).1
        (hrefiber (realEuclideanTakeLeft z) hx).2
    have hselected := maxwellOrderedScalarValue_spec
      (R := maxwellScalarRelationReflection R) (k := k) hex
    have heq : -realEuclideanTakeRight z 0 =
        maxwellOrderedScalarValue (maxwellScalarRelationReflection R) k
          (realEuclideanTakeLeft z) :=
      maxwellOrderedScalarFiberWitness_unique
        (hrefiber (realEuclideanTakeLeft z) hx).1
        (hrefiber (realEuclideanTakeLeft z) hx).2 hy hselected
    refine ⟨hx, ?_⟩
    funext i
    rw [show i = 0 from Fin.eq_zero i]
    simpa only [maxwellOrderedScalarMaximumSelector,
      maxwellOrderedScalarMaximumValue, neg_neg] using
        congrArg (fun t : ℝ ↦ -t) heq
  · rintro ⟨hx, hy⟩
    have hex : ∃ a : ℝ,
        MaxwellOrderedScalarFiberWitness
          (maxwellScalarRelationReflection R) k
          (realEuclideanTakeLeft z) a :=
      exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ
        (hrefiber (realEuclideanTakeLeft z) hx).1
        (hrefiber (realEuclideanTakeLeft z) hx).2
    refine ⟨hx, ?_⟩
    have hselected := maxwellOrderedScalarValue_spec
      (R := maxwellScalarRelationReflection R) (k := k) hex
    have hy0 : realEuclideanTakeRight z 0 =
        maxwellOrderedScalarMaximumValue R k
          (realEuclideanTakeLeft z) := by
      simpa only [maxwellOrderedScalarMaximumSelector] using congrFun hy 0
    rw [hy0]
    simpa only [maxwellOrderedScalarMaximumValue, neg_neg] using hselected

theorem maxwellFunctionGraph_orderedScalarMaximumSelector_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p k : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hfiber : ∀ x ∈ U,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellFunctionGraph U (maxwellOrderedScalarMaximumSelector R k) ∈
      charbonnelClosure S (p + 1) := by
  rw [← maxwellOrderedScalarMaximumSelectionGraph_eq_functionGraph hfiber]
  exact maxwellOrderedScalarMaximumSelectionGraph_mem_charbonnelClosure
    hC hp hU hR

theorem maxwellFunctionGraph_orderedScalarMaximumSelector_subset
    {p k : ℕ} {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ U,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellFunctionGraph U (maxwellOrderedScalarMaximumSelector R k) ⊆ R := by
  rw [← maxwellOrderedScalarMaximumSelectionGraph_eq_functionGraph hfiber]
  exact maxwellOrderedScalarMaximumSelectionGraph_subset

/-! ## Approximating closure-graph values inside an open base -/

/-- A finite closure-graph value can be approximated from above a prescribed
strict lower threshold while retaining any open base neighborhood. -/
theorem exists_functionGraph_value_gt_of_mem_closure
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p} {y a : ℝ}
    (hBopen : IsOpen B) (hxB : x ∈ B)
    (hy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      closure (maxwellFunctionGraph U f))
    (ha : a < y) :
    ∃ u : RealEuclidean p, u ∈ U ∧ u ∈ B ∧ a < f u 0 := by
  let baseMap : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
    realEuclideanTakeLeftContinuousLinearMap p 1
  let N : Set (RealEuclidean (p + 1)) :=
    baseMap ⁻¹' B ∩ {z | a < realEuclideanTakeRight z 0}
  have hbase : baseMap ⁻¹' B ∈
      𝓝 (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    apply baseMap.continuous.continuousAt.preimage_mem_nhds
    simpa [baseMap] using hBopen.mem_nhds hxB
  have houtputContinuous : Continuous
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeRight z 0) := by
    change Continuous (fun z : RealEuclidean (p + 1) ↦
      z (Fin.natAdd p (0 : Fin 1)))
    exact continuous_apply _
  have houtputOpen : IsOpen
      {z : RealEuclidean (p + 1) | a < realEuclideanTakeRight z 0} :=
    isOpen_lt continuous_const houtputContinuous
  have houtputMem : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      {z : RealEuclidean (p + 1) | a < realEuclideanTakeRight z 0} := by
    simpa using ha
  have hN : N ∈ 𝓝 (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) :=
    Filter.inter_mem hbase (houtputOpen.mem_nhds houtputMem)
  rw [mem_closure_iff_nhds] at hy
  obtain ⟨z, hzN, hzGraph⟩ := hy N hN
  have hzGraph' : realEuclideanAppend (realEuclideanTakeLeft z)
      (realEuclideanTakeRight z) ∈ maxwellFunctionGraph U f := by
    simpa only [realEuclideanAppend_takeLeft_takeRight] using hzGraph
  have hgraph :=
    (realEuclideanAppend_mem_maxwellFunctionGraph_iff U f
      (realEuclideanTakeLeft z) (realEuclideanTakeRight z)).mp hzGraph'
  refine ⟨realEuclideanTakeLeft z, hgraph.1, ?_, ?_⟩
  · exact hzN.1
  · have hout : a < realEuclideanTakeRight z 0 := by
      simpa [N] using hzN.2
    rw [hgraph.2] at hout
    exact hout

/-- The downward counterpart of
`exists_functionGraph_value_gt_of_mem_closure`. -/
theorem exists_functionGraph_value_lt_of_mem_closure
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p} {y a : ℝ}
    (hBopen : IsOpen B) (hxB : x ∈ B)
    (hy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      closure (maxwellFunctionGraph U f))
    (ha : y < a) :
    ∃ u : RealEuclidean p, u ∈ U ∧ u ∈ B ∧ f u 0 < a := by
  let baseMap : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
    realEuclideanTakeLeftContinuousLinearMap p 1
  let N : Set (RealEuclidean (p + 1)) :=
    baseMap ⁻¹' B ∩ {z | realEuclideanTakeRight z 0 < a}
  have hbase : baseMap ⁻¹' B ∈
      𝓝 (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    apply baseMap.continuous.continuousAt.preimage_mem_nhds
    simpa [baseMap] using hBopen.mem_nhds hxB
  have houtputContinuous : Continuous
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeRight z 0) := by
    change Continuous (fun z : RealEuclidean (p + 1) ↦
      z (Fin.natAdd p (0 : Fin 1)))
    exact continuous_apply _
  have houtputOpen : IsOpen
      {z : RealEuclidean (p + 1) | realEuclideanTakeRight z 0 < a} :=
    isOpen_lt houtputContinuous continuous_const
  have houtputMem : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      {z : RealEuclidean (p + 1) | realEuclideanTakeRight z 0 < a} := by
    simpa using ha
  have hN : N ∈ 𝓝 (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) :=
    Filter.inter_mem hbase (houtputOpen.mem_nhds houtputMem)
  rw [mem_closure_iff_nhds] at hy
  obtain ⟨z, hzN, hzGraph⟩ := hy N hN
  have hzGraph' : realEuclideanAppend (realEuclideanTakeLeft z)
      (realEuclideanTakeRight z) ∈ maxwellFunctionGraph U f := by
    simpa only [realEuclideanAppend_takeLeft_takeRight] using hzGraph
  have hgraph :=
    (realEuclideanAppend_mem_maxwellFunctionGraph_iff U f
      (realEuclideanTakeLeft z) (realEuclideanTakeRight z)).mp hzGraph'
  refine ⟨realEuclideanTakeLeft z, hgraph.1, ?_, ?_⟩
  · exact hzN.1
  · have hout : realEuclideanTakeRight z 0 < a := by
      simpa [N] using hzN.2
    rw [hgraph.2] at hout
    exact hout

end AbelFormalization
