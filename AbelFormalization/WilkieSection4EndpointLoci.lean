import AbelFormalization.CharbonnelOrderedSelectorContinuity
import AbelFormalization.CharbonnelOrderedSelectorMembership
import Mathlib.Topology.Constructions

/-!
# Wilkie Section 4 endpoint loci

For a scalar relation `A` contained in the open band between `f` and `g`,
Wilkie considers the positive distances from points of `A` to the two band
endpoints.  This file constructs those two relations by WS1--WS4 and
projection, forms their closed zero traces, and proves the endpoint-exclusion
argument used on pages 418--419.

The final theorem says that relative closedness of `A` inside the band,
together with avoidance of the two zero traces, makes every vertical fibre
of `A` stable under closure.  The existing compactness theorem then gives
the no-escape hypothesis used by the ordered-selector construction.
-/

noncomputable section

open Set Filter
open scoped Set.Notation

namespace AbelFormalization

set_option autoImplicit false

/-! ## Polynomial endpoint-gap incidences -/

/-- In coordinates `(x, ε, y, t)`, the equation `ε = y - t` and the
positivity condition `0 < ε`. -/
def wilkieSection4LowerEndpointGapConstraint (p : ℕ) :
    Set (RealEuclidean ((p + 1) + 2)) :=
  {w | MvPolynomial.eval w
      (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1) -
        (MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 0) -
          MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 1))) = 0} ∩
    {w | 0 < MvPolynomial.eval w
      (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1))}

/-- In coordinates `(x, ε, y, t)`, the equation `ε = t - y` and the
positivity condition `0 < ε`. -/
def wilkieSection4UpperEndpointGapConstraint (p : ℕ) :
    Set (RealEuclidean ((p + 1) + 2)) :=
  {w | MvPolynomial.eval w
      (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1) -
        (MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 1) -
          MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 0))) = 0} ∩
    {w | 0 < MvPolynomial.eval w
      (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1))}

theorem polynomialSignConstructible_wilkieSection4LowerEndpointGapConstraint
    (p : ℕ) :
    PolynomialSignConstructible ((p + 1) + 2)
      (wilkieSection4LowerEndpointGapConstraint p) := by
  exact .inter
    (.zero (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1) -
      (MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 0) -
        MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 1))))
    (.pos (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1)))

theorem polynomialSignConstructible_wilkieSection4UpperEndpointGapConstraint
    (p : ℕ) :
    PolynomialSignConstructible ((p + 1) + 2)
      (wilkieSection4UpperEndpointGapConstraint p) := by
  exact .inter
    (.zero (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1) -
      (MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 1) -
        MvPolynomial.X (maxwellOrderedWitnessValueIndex p 1 0))))
    (.pos (MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1)))

@[simp]
theorem realEuclideanAppend_append_mem_wilkieSection4LowerEndpointGapConstraint_iff
    {p : ℕ} (x : RealEuclidean p) (ε : ℝ)
    (values : RealEuclidean 2) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4LowerEndpointGapConstraint p ↔
      0 < ε ∧ ε = values 0 - values 1 := by
  simp [wilkieSection4LowerEndpointGapConstraint,
    maxwellOrderedWitnessOutputIndex, maxwellOrderedWitnessValueIndex,
    map_sub, MvPolynomial.eval_X, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd, sub_eq_zero, and_comm]

@[simp]
theorem realEuclideanAppend_append_mem_wilkieSection4UpperEndpointGapConstraint_iff
    {p : ℕ} (x : RealEuclidean p) (ε : ℝ)
    (values : RealEuclidean 2) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4UpperEndpointGapConstraint p ↔
      0 < ε ∧ ε = values 1 - values 0 := by
  simp [wilkieSection4UpperEndpointGapConstraint,
    maxwellOrderedWitnessOutputIndex, maxwellOrderedWitnessValueIndex,
    map_sub, MvPolynomial.eval_X, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd, sub_eq_zero, and_comm]

/-- Incidence for a point `y ∈ A` at positive distance `ε = y - f(x)`
from the lower endpoint.  The last witness coordinate is constrained to the
restricted graph of `f`. -/
def wilkieSection4LowerEndpointGapIncidence {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) :
    Set (RealEuclidean ((p + 1) + 2)) :=
  (((maxwellOrderedWitnessBaseLinearMap p 1 ⁻¹' C ∩
      maxwellOrderedWitnessRelationLinearMap p 1 0 ⁻¹' A) ∩
      maxwellOrderedWitnessRelationLinearMap p 1 1 ⁻¹'
        charbonnelRestrictedGraph C f) ∩
    wilkieSection4LowerEndpointGapConstraint p)

/-- Incidence for a point `y ∈ A` at positive distance `ε = g(x) - y`
from the upper endpoint.  The last witness coordinate is constrained to the
restricted graph of `g`. -/
def wilkieSection4UpperEndpointGapIncidence {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) :
    Set (RealEuclidean ((p + 1) + 2)) :=
  (((maxwellOrderedWitnessBaseLinearMap p 1 ⁻¹' C ∩
      maxwellOrderedWitnessRelationLinearMap p 1 0 ⁻¹' A) ∩
      maxwellOrderedWitnessRelationLinearMap p 1 1 ⁻¹'
        charbonnelRestrictedGraph C g) ∩
    wilkieSection4UpperEndpointGapConstraint p)

@[simp]
theorem realEuclideanAppend_append_mem_wilkieSection4LowerEndpointGapIncidence_iff
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) (x : RealEuclidean p) (ε : ℝ)
    (values : RealEuclidean 2) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4LowerEndpointGapIncidence C A f ↔
      x ∈ C ∧ values 0 ∈ maxwellScalarFiber A x ∧
        values 1 = f x ∧ 0 < ε ∧ ε = values 0 - values 1 := by
  simp only [wilkieSection4LowerEndpointGapIncidence, Set.mem_inter_iff,
    Set.mem_preimage,
    maxwellOrderedWitnessBaseLinearMap_apply_append,
    maxwellOrderedWitnessRelationLinearMap_apply_append,
    realEuclideanAppend_append_mem_wilkieSection4LowerEndpointGapConstraint_iff,
    charbonnelRestrictedGraph, Set.mem_ofPred_eq,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
  aesop

@[simp]
theorem realEuclideanAppend_append_mem_wilkieSection4UpperEndpointGapIncidence_iff
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) (x : RealEuclidean p) (ε : ℝ)
    (values : RealEuclidean 2) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4UpperEndpointGapIncidence C A g ↔
      x ∈ C ∧ values 0 ∈ maxwellScalarFiber A x ∧
        values 1 = g x ∧ 0 < ε ∧ ε = values 1 - values 0 := by
  simp only [wilkieSection4UpperEndpointGapIncidence, Set.mem_inter_iff,
    Set.mem_preimage,
    maxwellOrderedWitnessBaseLinearMap_apply_append,
    maxwellOrderedWitnessRelationLinearMap_apply_append,
    realEuclideanAppend_append_mem_wilkieSection4UpperEndpointGapConstraint_iff,
    charbonnelRestrictedGraph, Set.mem_ofPred_eq,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
  aesop

/-! ## The projected relations `H_f` and `H_g` -/

/-- Wilkie's positive lower-endpoint gap relation `H_f`. -/
def wilkieSection4LowerEndpointGapRelation {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) : MaxwellRelation p 1 :=
  realEuclideanExistentialProjection
    (wilkieSection4LowerEndpointGapIncidence C A f)

/-- Wilkie's positive upper-endpoint gap relation `H_g`. -/
def wilkieSection4UpperEndpointGapRelation {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) : MaxwellRelation p 1 :=
  realEuclideanExistentialProjection
    (wilkieSection4UpperEndpointGapIncidence C A g)

@[simp]
theorem realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) (x : RealEuclidean p) (ε : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ ε) ∈
        wilkieSection4LowerEndpointGapRelation C A f ↔
      x ∈ C ∧ 0 < ε ∧ ∃ y : ℝ,
        y ∈ maxwellScalarFiber A x ∧ ε = y - f x := by
  change (∃ values : RealEuclidean 2,
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4LowerEndpointGapIncidence C A f) ↔ _
  constructor
  · rintro ⟨values, hvalues⟩
    rcases (realEuclideanAppend_append_mem_wilkieSection4LowerEndpointGapIncidence_iff
      C A f x ε values).mp hvalues with ⟨hx, hy, ht, hε, heq⟩
    exact ⟨hx, hε, values 0, hy, by simpa [ht] using heq⟩
  · rintro ⟨hx, hε, y, hy, heq⟩
    refine ⟨![y, f x],
      (realEuclideanAppend_append_mem_wilkieSection4LowerEndpointGapIncidence_iff
        C A f x ε ![y, f x]).mpr ?_⟩
    exact ⟨hx, by simpa using hy, by simp, hε, by simpa using heq⟩

@[simp]
theorem realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) (x : RealEuclidean p) (ε : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ ε) ∈
        wilkieSection4UpperEndpointGapRelation C A g ↔
      x ∈ C ∧ 0 < ε ∧ ∃ y : ℝ,
        y ∈ maxwellScalarFiber A x ∧ ε = g x - y := by
  change (∃ values : RealEuclidean 2,
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4UpperEndpointGapIncidence C A g) ↔ _
  constructor
  · rintro ⟨values, hvalues⟩
    rcases (realEuclideanAppend_append_mem_wilkieSection4UpperEndpointGapIncidence_iff
      C A g x ε values).mp hvalues with ⟨hx, hy, ht, hε, heq⟩
    exact ⟨hx, hε, values 0, hy, by simpa [ht] using heq⟩
  · rintro ⟨hx, hε, y, hy, heq⟩
    refine ⟨![y, g x],
      (realEuclideanAppend_append_mem_wilkieSection4UpperEndpointGapIncidence_iff
        C A g x ε ![y, g x]).mpr ?_⟩
    exact ⟨hx, by simpa using hy, by simp, hε, by simpa using heq⟩

theorem wilkieSection4LowerEndpointGapRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1)) :
    wilkieSection4LowerEndpointGapRelation C A f ∈
      charbonnelClosure S (p + 1) := by
  have hambient : 0 < (p + 1) + 2 := by omega
  have hbase := hC.linear_preimage_mem hambient hp hCmem
    (maxwellOrderedWitnessBaseLinearMap p 1)
  have hrelation := hC.linear_preimage_mem hambient (by omega) hAmem
    (maxwellOrderedWitnessRelationLinearMap p 1 0)
  have hgraph := hC.linear_preimage_mem hambient (by omega) hfGraph
    (maxwellOrderedWitnessRelationLinearMap p 1 1)
  have hconstraint : wilkieSection4LowerEndpointGapConstraint p ∈
      charbonnelClosure S ((p + 1) + 2) :=
    hC.ws2_polynomialSign hambient
      (polynomialSignConstructible_wilkieSection4LowerEndpointGapConstraint p)
  exact charbonnelClosure_projection (by omega)
    (hC.ws1_inter hambient
      (hC.ws1_inter hambient
        (hC.ws1_inter hambient hbase hrelation) hgraph) hconstraint)

theorem wilkieSection4UpperEndpointGapRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1)) :
    wilkieSection4UpperEndpointGapRelation C A g ∈
      charbonnelClosure S (p + 1) := by
  have hambient : 0 < (p + 1) + 2 := by omega
  have hbase := hC.linear_preimage_mem hambient hp hCmem
    (maxwellOrderedWitnessBaseLinearMap p 1)
  have hrelation := hC.linear_preimage_mem hambient (by omega) hAmem
    (maxwellOrderedWitnessRelationLinearMap p 1 0)
  have hgraph := hC.linear_preimage_mem hambient (by omega) hgGraph
    (maxwellOrderedWitnessRelationLinearMap p 1 1)
  have hconstraint : wilkieSection4UpperEndpointGapConstraint p ∈
      charbonnelClosure S ((p + 1) + 2) :=
    hC.ws2_polynomialSign hambient
      (polynomialSignConstructible_wilkieSection4UpperEndpointGapConstraint p)
  exact charbonnelClosure_projection (by omega)
    (hC.ws1_inter hambient
      (hC.ws1_inter hambient
        (hC.ws1_inter hambient hbase hrelation) hgraph) hconstraint)

/-! ## Closed zero-trace loci -/

/-- The lower endpoint locus: the zero section of `closure H_f`. -/
def wilkieSection4LowerEndpointLocus {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (closure (wilkieSection4LowerEndpointGapRelation C A f))

/-- The upper endpoint locus: the zero section of `closure H_g`. -/
def wilkieSection4UpperEndpointLocus {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (closure (wilkieSection4UpperEndpointGapRelation C A g))

theorem wilkieSection4LowerEndpointLocus_isClosed
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f : RealEuclidean p → ℝ) :
    IsClosed (wilkieSection4LowerEndpointLocus C A f) :=
  charbonnelZeroSection_isClosed isClosed_closure

theorem wilkieSection4UpperEndpointLocus_isClosed
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (g : RealEuclidean p → ℝ) :
    IsClosed (wilkieSection4UpperEndpointLocus C A g) :=
  charbonnelZeroSection_isClosed isClosed_closure

theorem wilkieSection4LowerEndpointLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1)) :
    wilkieSection4LowerEndpointLocus C A f ∈ charbonnelClosure S p := by
  apply charbonnelZeroSection_mem_charbonnelClosure hp
  exact charbonnelClosure_topologicalClosure
    (wilkieSection4LowerEndpointGapRelation_mem_charbonnelClosure
      hC hp hCmem hAmem hfGraph)

theorem wilkieSection4UpperEndpointLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1)) :
    wilkieSection4UpperEndpointLocus C A g ∈ charbonnelClosure S p := by
  apply charbonnelZeroSection_mem_charbonnelClosure hp
  exact charbonnelClosure_topologicalClosure
    (wilkieSection4UpperEndpointGapRelation_mem_charbonnelClosure
      hC hp hCmem hAmem hgGraph)

/-! ## Endpoint limits of the relation -/

/-- Send `(x,y)` to the lower endpoint gap `(x,y-f(x))`. -/
def wilkieSection4LowerEndpointGapMap {p : ℕ}
    (f : RealEuclidean p → ℝ) (z : RealEuclidean (p + 1)) :
    RealEuclidean (p + 1) :=
  realEuclideanAppendScalarContinuousLinearEquiv p
    (realEuclideanTakeLeft z,
      realEuclideanTakeRight z 0 - f (realEuclideanTakeLeft z))

/-- Send `(x,y)` to the upper endpoint gap `(x,g(x)-y)`. -/
def wilkieSection4UpperEndpointGapMap {p : ℕ}
    (g : RealEuclidean p → ℝ) (z : RealEuclidean (p + 1)) :
    RealEuclidean (p + 1) :=
  realEuclideanAppendScalarContinuousLinearEquiv p
    (realEuclideanTakeLeft z,
      g (realEuclideanTakeLeft z) - realEuclideanTakeRight z 0)

@[simp]
theorem wilkieSection4LowerEndpointGapMap_append
    {p : ℕ} (f : RealEuclidean p → ℝ)
    (x : RealEuclidean p) (y : ℝ) :
    wilkieSection4LowerEndpointGapMap f
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ y - f x) := by
  simp [wilkieSection4LowerEndpointGapMap, realEuclideanAppendScalar]

@[simp]
theorem wilkieSection4UpperEndpointGapMap_append
    {p : ℕ} (g : RealEuclidean p → ℝ)
    (x : RealEuclidean p) (y : ℝ) :
    wilkieSection4UpperEndpointGapMap g
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ g x - y) := by
  simp [wilkieSection4UpperEndpointGapMap, realEuclideanAppendScalar]

/-- Continuity of the lower-gap coordinate at a point over `C`, relative to
a relation whose base projection lies in `C`. -/
theorem continuousWithinAt_wilkieSection4LowerEndpointGapMap
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {x : RealEuclidean p} {y : ℝ}
    (hf : ContinuousOn f C)
    (hbase : MapsTo realEuclideanTakeLeft A C)
    (hx : x ∈ C) :
    ContinuousWithinAt (wilkieSection4LowerEndpointGapMap f) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
  let R := (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have hleftFun :
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeLeft z) =
        (realEuclideanTakeLeftContinuousLinearMap p 1 :
          RealEuclidean (p + 1) → RealEuclidean p) := by
    funext z
    exact (realEuclideanTakeLeftContinuousLinearMap_apply z).symm
  have hleft : ContinuousWithinAt
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeLeft z) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    rw [hleftFun]
    exact (realEuclideanTakeLeftContinuousLinearMap p 1).continuous.continuousWithinAt
  have hright : ContinuousWithinAt
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeRight z 0) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    have hcontinuous : Continuous
        (fun z : RealEuclidean (p + 1) ↦ R z 0) :=
      (continuous_apply 0).comp R.continuous
    simpa [R] using hcontinuous.continuousWithinAt
  have hfcomp : ContinuousWithinAt
      (fun z : RealEuclidean (p + 1) ↦ f (realEuclideanTakeLeft z)) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    have h := (hf x hx).comp_of_eq hleft hbase (by simp)
    simpa [Function.comp_def] using h
  have hpair := hleft.prodMk (hright.sub hfcomp)
  have h :=
    (realEuclideanAppendScalarContinuousLinearEquiv p).continuous.continuousAt
      |>.comp_continuousWithinAt hpair
  change ContinuousWithinAt
    (fun z : RealEuclidean (p + 1) ↦
      realEuclideanAppendScalar (realEuclideanTakeLeft z)
        (realEuclideanTakeRight z 0 - f (realEuclideanTakeLeft z))) A
    (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
  simpa [Function.comp_def] using h

/-- Continuity of the upper-gap coordinate at a point over `C`, relative to
a relation whose base projection lies in `C`. -/
theorem continuousWithinAt_wilkieSection4UpperEndpointGapMap
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ} {x : RealEuclidean p} {y : ℝ}
    (hg : ContinuousOn g C)
    (hbase : MapsTo realEuclideanTakeLeft A C)
    (hx : x ∈ C) :
    ContinuousWithinAt (wilkieSection4UpperEndpointGapMap g) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
  let R := (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have hleftFun :
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeLeft z) =
        (realEuclideanTakeLeftContinuousLinearMap p 1 :
          RealEuclidean (p + 1) → RealEuclidean p) := by
    funext z
    exact (realEuclideanTakeLeftContinuousLinearMap_apply z).symm
  have hleft : ContinuousWithinAt
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeLeft z) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    rw [hleftFun]
    exact (realEuclideanTakeLeftContinuousLinearMap p 1).continuous.continuousWithinAt
  have hright : ContinuousWithinAt
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeRight z 0) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    have hcontinuous : Continuous
        (fun z : RealEuclidean (p + 1) ↦ R z 0) :=
      (continuous_apply 0).comp R.continuous
    simpa [R] using hcontinuous.continuousWithinAt
  have hgcomp : ContinuousWithinAt
      (fun z : RealEuclidean (p + 1) ↦ g (realEuclideanTakeLeft z)) A
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) := by
    have h := (hg x hx).comp_of_eq hleft hbase (by simp)
    simpa [Function.comp_def] using h
  have hpair := hleft.prodMk (hgcomp.sub hright)
  have h :=
    (realEuclideanAppendScalarContinuousLinearEquiv p).continuous.continuousAt
      |>.comp_continuousWithinAt hpair
  change ContinuousWithinAt
    (fun z : RealEuclidean (p + 1) ↦
      realEuclideanAppendScalar (realEuclideanTakeLeft z)
        (g (realEuclideanTakeLeft z) - realEuclideanTakeRight z 0)) A
    (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
  simpa [Function.comp_def] using h

/-- Points of a relation lying above `f` map to the positive lower-endpoint
gap relation. -/
theorem wilkieSection4LowerEndpointGapMap_mapsTo
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ}
    (hA : A ⊆ charbonnelUpperRayCell C f) :
    MapsTo (wilkieSection4LowerEndpointGapMap f) A
      (wilkieSection4LowerEndpointGapRelation C A f) := by
  intro z hz
  have hzRay := hA hz
  have hzBase : realEuclideanTakeLeft z ∈ C := hzRay.1
  have hzAbove :
      f (realEuclideanTakeLeft z) < realEuclideanTakeRight z 0 :=
    hzRay.2
  have hrightConst :
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  have hzFiber : realEuclideanTakeRight z 0 ∈
      maxwellScalarFiber A (realEuclideanTakeLeft z) := by
    change realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) ∈ A
    rw [hrightConst, realEuclideanAppend_takeLeft_takeRight]
    exact hz
  rw [show wilkieSection4LowerEndpointGapMap f z =
      realEuclideanAppend (realEuclideanTakeLeft z)
        (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0 -
          f (realEuclideanTakeLeft z)) by
    simp [wilkieSection4LowerEndpointGapMap, realEuclideanAppendScalar]]
  rw [realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff]
  exact ⟨hzBase, sub_pos.mpr hzAbove,
    realEuclideanTakeRight z 0, hzFiber, rfl⟩

/-- Points of a relation lying below `g` map to the positive upper-endpoint
gap relation. -/
theorem wilkieSection4UpperEndpointGapMap_mapsTo
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ}
    (hA : A ⊆ charbonnelLowerRayCell C g) :
    MapsTo (wilkieSection4UpperEndpointGapMap g) A
      (wilkieSection4UpperEndpointGapRelation C A g) := by
  intro z hz
  have hzRay := hA hz
  have hzBase : realEuclideanTakeLeft z ∈ C := hzRay.1
  have hzBelow :
      realEuclideanTakeRight z 0 < g (realEuclideanTakeLeft z) :=
    hzRay.2
  have hrightConst :
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  have hzFiber : realEuclideanTakeRight z 0 ∈
      maxwellScalarFiber A (realEuclideanTakeLeft z) := by
    change realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) ∈ A
    rw [hrightConst, realEuclideanAppend_takeLeft_takeRight]
    exact hz
  rw [show wilkieSection4UpperEndpointGapMap g z =
      realEuclideanAppend (realEuclideanTakeLeft z)
        (fun _ : Fin 1 ↦ g (realEuclideanTakeLeft z) -
          realEuclideanTakeRight z 0) by
    simp [wilkieSection4UpperEndpointGapMap, realEuclideanAppendScalar]]
  rw [realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff]
  exact ⟨hzBase, sub_pos.mpr hzBelow,
    realEuclideanTakeRight z 0, hzFiber, rfl⟩

/-- A closure point of `A` induces a closure point of `H_f`. -/
theorem mem_closure_wilkieSection4LowerEndpointGapRelation
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {x : RealEuclidean p} {y : ℝ}
    (hf : ContinuousOn f C)
    (hA : A ⊆ charbonnelUpperRayCell C f)
    (hx : x ∈ C)
    (hxy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ closure A) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y - f x) ∈
      closure (wilkieSection4LowerEndpointGapRelation C A f) := by
  have hbase : MapsTo realEuclideanTakeLeft A C := by
    intro z hz
    exact (hA hz).1
  have hcontinuous :=
    continuousWithinAt_wilkieSection4LowerEndpointGapMap hf hbase hx
      (y := y)
  have hclosure := hcontinuous.mem_closure hxy
    (wilkieSection4LowerEndpointGapMap_mapsTo hA)
  simpa using hclosure

/-- A closure point of `A` induces a closure point of `H_g`. -/
theorem mem_closure_wilkieSection4UpperEndpointGapRelation
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ} {x : RealEuclidean p} {y : ℝ}
    (hg : ContinuousOn g C)
    (hA : A ⊆ charbonnelLowerRayCell C g)
    (hx : x ∈ C)
    (hxy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ closure A) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ g x - y) ∈
      closure (wilkieSection4UpperEndpointGapRelation C A g) := by
  have hbase : MapsTo realEuclideanTakeLeft A C := by
    intro z hz
    exact (hA hz).1
  have hcontinuous :=
    continuousWithinAt_wilkieSection4UpperEndpointGapMap hg hbase hx
      (y := y)
  have hclosure := hcontinuous.mem_closure hxy
    (wilkieSection4UpperEndpointGapMap_mapsTo hA)
  simpa using hclosure

/-- Every point of `H_f` has positive displayed coordinate. -/
theorem wilkieSection4LowerEndpointGapRelation_output_pos
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {z : RealEuclidean (p + 1)}
    (hz : z ∈ wilkieSection4LowerEndpointGapRelation C A f) :
    0 < realEuclideanTakeRight z 0 := by
  have hrightConst :
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  have hz' : realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) ∈
        wilkieSection4LowerEndpointGapRelation C A f := by
    rw [hrightConst, realEuclideanAppend_takeLeft_takeRight]
    exact hz
  exact (realEuclideanAppend_mem_wilkieSection4LowerEndpointGapRelation_iff
    C A f (realEuclideanTakeLeft z) (realEuclideanTakeRight z 0)).mp hz' |>.2.1

/-- Every point of `H_g` has positive displayed coordinate. -/
theorem wilkieSection4UpperEndpointGapRelation_output_pos
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ} {z : RealEuclidean (p + 1)}
    (hz : z ∈ wilkieSection4UpperEndpointGapRelation C A g) :
    0 < realEuclideanTakeRight z 0 := by
  have hrightConst :
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  have hz' : realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) ∈
        wilkieSection4UpperEndpointGapRelation C A g := by
    rw [hrightConst, realEuclideanAppend_takeLeft_takeRight]
    exact hz
  exact (realEuclideanAppend_mem_wilkieSection4UpperEndpointGapRelation_iff
    C A g (realEuclideanTakeLeft z) (realEuclideanTakeRight z 0)).mp hz' |>.2.1

/-- Closure points of a relation above a continuous lower endpoint remain
weakly above that endpoint. -/
theorem wilkieSection4_lowerEndpoint_le_of_mem_closure
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {x : RealEuclidean p} {y : ℝ}
    (hf : ContinuousOn f C)
    (hA : A ⊆ charbonnelUpperRayCell C f)
    (hx : x ∈ C)
    (hxy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ closure A) :
    f x ≤ y := by
  have hgap := mem_closure_wilkieSection4LowerEndpointGapRelation
    hf hA hx hxy
  let R := (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have houtputContinuous : Continuous
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeRight z 0) := by
    have h : Continuous (fun z : RealEuclidean (p + 1) ↦ R z 0) :=
      (continuous_apply 0).comp R.continuous
    simpa [R] using h
  have hclosed : IsClosed
      {z : RealEuclidean (p + 1) | 0 ≤ realEuclideanTakeRight z 0} :=
    isClosed_Ici.preimage houtputContinuous
  have hnonneg : closure (wilkieSection4LowerEndpointGapRelation C A f) ⊆
      {z : RealEuclidean (p + 1) | 0 ≤ realEuclideanTakeRight z 0} :=
    closure_minimal
      (fun _ hz ↦ (wilkieSection4LowerEndpointGapRelation_output_pos hz).le)
      hclosed
  have := hnonneg hgap
  simpa using this

/-- Closure points of a relation below a continuous upper endpoint remain
weakly below that endpoint. -/
theorem wilkieSection4_le_upperEndpoint_of_mem_closure
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ} {x : RealEuclidean p} {y : ℝ}
    (hg : ContinuousOn g C)
    (hA : A ⊆ charbonnelLowerRayCell C g)
    (hx : x ∈ C)
    (hxy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ closure A) :
    y ≤ g x := by
  have hgap := mem_closure_wilkieSection4UpperEndpointGapRelation
    hg hA hx hxy
  let R := (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have houtputContinuous : Continuous
      (fun z : RealEuclidean (p + 1) ↦ realEuclideanTakeRight z 0) := by
    have h : Continuous (fun z : RealEuclidean (p + 1) ↦ R z 0) :=
      (continuous_apply 0).comp R.continuous
    simpa [R] using h
  have hclosed : IsClosed
      {z : RealEuclidean (p + 1) | 0 ≤ realEuclideanTakeRight z 0} :=
    isClosed_Ici.preimage houtputContinuous
  have hnonneg : closure (wilkieSection4UpperEndpointGapRelation C A g) ⊆
      {z : RealEuclidean (p + 1) | 0 ≤ realEuclideanTakeRight z 0} :=
    closure_minimal
      (fun _ hz ↦ (wilkieSection4UpperEndpointGapRelation_output_pos hz).le)
      hclosed
  have := hnonneg hgap
  simpa using this

/-- If the lower endpoint itself lies in `closure A`, its base point lies in
the closed zero trace of `H_f`. -/
theorem mem_wilkieSection4LowerEndpointLocus_of_endpoint_mem_closure
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {x : RealEuclidean p}
    (hf : ContinuousOn f C)
    (hA : A ⊆ charbonnelUpperRayCell C f)
    (hx : x ∈ C)
    (hxf : realEuclideanAppend x (fun _ : Fin 1 ↦ f x) ∈ closure A) :
    x ∈ wilkieSection4LowerEndpointLocus C A f := by
  have hgap := mem_closure_wilkieSection4LowerEndpointGapRelation
    hf hA hx hxf
  change charbonnelAppendLastCoordinate x 0 ∈
    closure (wilkieSection4LowerEndpointGapRelation C A f)
  simpa [charbonnelAppendLastCoordinate] using hgap

/-- If the upper endpoint itself lies in `closure A`, its base point lies in
the closed zero trace of `H_g`. -/
theorem mem_wilkieSection4UpperEndpointLocus_of_endpoint_mem_closure
    {p : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {g : RealEuclidean p → ℝ} {x : RealEuclidean p}
    (hg : ContinuousOn g C)
    (hA : A ⊆ charbonnelLowerRayCell C g)
    (hx : x ∈ C)
    (hxg : realEuclideanAppend x (fun _ : Fin 1 ↦ g x) ∈ closure A) :
    x ∈ wilkieSection4UpperEndpointLocus C A g := by
  have hgap := mem_closure_wilkieSection4UpperEndpointGapRelation
    hg hA hx hxg
  change charbonnelAppendLastCoordinate x 0 ∈
    closure (wilkieSection4UpperEndpointGapRelation C A g)
  simpa [charbonnelAppendLastCoordinate] using hgap

/-! ## Relative closedness plus endpoint avoidance -/

/-- Operational core of the endpoint argument.  The relation is contained in
the continuous open band over the ambient base `C`.  On a refined base `B`,
avoiding both closed endpoint loci upgrades relative closedness in that band
to vertical closure stability. -/
theorem
    maxwellScalarFiberClosureStableOver_of_closure_inter_band_of_disjoint_endpointLoci
    {p : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hBC : B ⊆ C)
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hrelative : closure A ∩ charbonnelOpenBand C f g ⊆ A)
    (hf : ContinuousOn f C)
    (hg : ContinuousOn g C)
    (hlower : Disjoint B
      (wilkieSection4LowerEndpointLocus C A f))
    (hupper : Disjoint B
      (wilkieSection4UpperEndpointLocus C A g)) :
    MaxwellScalarFiberClosureStableOver B A := by
  have hAupper : A ⊆ charbonnelUpperRayCell C f := by
    intro z hz
    have hband := hAsub hz
    exact ⟨hband.1, hband.2.1⟩
  have hAlower : A ⊆ charbonnelLowerRayCell C g := by
    intro z hz
    have hband := hAsub hz
    exact ⟨hband.1, hband.2.2⟩
  intro x hxB y hxy
  have hxC : x ∈ C := hBC hxB
  have hfy : f x ≤ y :=
    wilkieSection4_lowerEndpoint_le_of_mem_closure hf hAupper hxC hxy
  have hyg : y ≤ g x :=
    wilkieSection4_le_upperEndpoint_of_mem_closure hg hAlower hxC hxy
  have hyNeLower : y ≠ f x := by
    intro hy
    have hxf : realEuclideanAppend x (fun _ : Fin 1 ↦ f x) ∈
        closure A := by
      simpa [hy] using hxy
    have hxLocus :=
      mem_wilkieSection4LowerEndpointLocus_of_endpoint_mem_closure
        hf hAupper hxC hxf
    exact (Set.disjoint_left.mp hlower hxB) hxLocus
  have hyNeUpper : y ≠ g x := by
    intro hy
    have hxg : realEuclideanAppend x (fun _ : Fin 1 ↦ g x) ∈
        closure A := by
      simpa [hy] using hxy
    have hxLocus :=
      mem_wilkieSection4UpperEndpointLocus_of_endpoint_mem_closure
        hg hAlower hxC hxg
    exact (Set.disjoint_left.mp hupper hxB) hxLocus
  have hfyStrict : f x < y :=
    lt_of_le_of_ne hfy hyNeLower.symm
  have hygStrict : y < g x :=
    lt_of_le_of_ne hyg hyNeUpper
  apply hrelative
  refine ⟨hxy, ?_⟩
  simpa [charbonnelOpenBand] using
    (show x ∈ C ∧ f x < y ∧ y < g x from
      ⟨hxC, hfyStrict, hygStrict⟩)

/-- Source-shaped version of the preceding theorem.  Here relative
closedness is stated literally: the preimage of `A` in the subtype of the
open band is closed. -/
theorem
    maxwellScalarFiberClosureStableOver_of_relativelyClosedBand_of_disjoint_endpointLoci
    {p : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hBC : B ⊆ C)
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g)))
    (hf : ContinuousOn f C)
    (hg : ContinuousOn g C)
    (hlower : Disjoint B
      (wilkieSection4LowerEndpointLocus C A f))
    (hupper : Disjoint B
      (wilkieSection4UpperEndpointLocus C A g)) :
    MaxwellScalarFiberClosureStableOver B A := by
  have hrelative : closure A ∩ charbonnelOpenBand C f g ⊆ A := by
    have hclosed := isClosed_preimage_val.mp hAclosed
    intro z hz
    apply hclosed
    refine ⟨hz.2, ?_⟩
    have hinter : charbonnelOpenBand C f g ∩ A = A :=
      inter_eq_right.mpr hAsub
    simpa only [hinter] using hz.1
  exact
    maxwellScalarFiberClosureStableOver_of_closure_inter_band_of_disjoint_endpointLoci
      hBC hAsub hrelative hf hg hlower hupper

/-- Wilkie's endpoint-locus argument supplies exactly the no-escape premise
needed for continuity of the ordered finite-fibre selectors. -/
theorem
    maxwellScalarFiberNoEscape_of_relativelyClosedBand_of_disjoint_endpointLoci
    {p : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hBC : B ⊆ C)
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g)))
    (hf : ContinuousOn f C)
    (hg : ContinuousOn g C)
    (hlower : Disjoint B
      (wilkieSection4LowerEndpointLocus C A f))
    (hupper : Disjoint B
      (wilkieSection4UpperEndpointLocus C A g)) :
    MaxwellScalarFiberNoEscape B A := by
  apply maxwellScalarFiberNoEscape_of_continuousBand_of_closureStable
    (lower := f) (upper := g)
    (maxwellScalarFiberClosureStableOver_of_relativelyClosedBand_of_disjoint_endpointLoci
      hBC hAsub hAclosed hf hg hlower hupper)
    (hf.mono hBC) (hg.mono hBC)
  intro x hxB y hy
  have hband := hAsub hy
  simpa [charbonnelOpenBand] using hband.2

end AbelFormalization
