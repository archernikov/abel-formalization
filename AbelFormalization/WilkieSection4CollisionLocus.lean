import AbelFormalization.CharbonnelOrderedSelectorGraph
import AbelFormalization.MaxwellExtendedSlopeClusterMembership

/-!
# Wilkie Section 4 collision locus

For a scalar relation `A`, Wilkie introduces the positive gap relation `H`:
`(x, ε) ∈ H` when one fibre of `A` contains two points whose positive
difference is `ε`.  Avoiding the zero section of `closure H` gives exactly the
uniform local separation of distinct fibre points used by the ordered-selector
continuity argument.

This file constructs `H` by a polynomial ordered-pair incidence, proves its
Charbonnel-closure membership using only WS1--WS4 and projection, and proves
the topological no-collision consequence.  No complement closure or cell
decomposition is used.
-/

noncomputable section

open Set Filter

namespace AbelFormalization

set_option autoImplicit false

/-! ## The positive gap relation -/

/-- The polynomial `(z - y) - ε` in flat coordinates `(x, ε, y, z)`. -/
def wilkieSection4GapPolynomial (p : ℕ) :
    MvPolynomial (Fin ((p + 1) + 2)) ℝ :=
  MvPolynomial.X (maxwellOrderedWitnessOutputIndex p 1) -
    maxwellOrderedWitnessIncrementPolynomial p 1 0

/-- The equality `ε = z - y` together with the strict order `y < z`. -/
def wilkieSection4GapConstraint (p : ℕ) :
    Set (RealEuclidean ((p + 1) + 2)) :=
  {w | MvPolynomial.eval w (wilkieSection4GapPolynomial p) = 0} ∩
    {w | 0 < MvPolynomial.eval w
      (maxwellOrderedWitnessIncrementPolynomial p 1 0)}

theorem polynomialSignConstructible_wilkieSection4GapConstraint
    (p : ℕ) :
    PolynomialSignConstructible ((p + 1) + 2)
      (wilkieSection4GapConstraint p) := by
  exact .inter (.zero (wilkieSection4GapPolynomial p))
    (.pos (maxwellOrderedWitnessIncrementPolynomial p 1 0))

/-- Full incidence for two increasingly ordered fibre points with their
positive gap exposed as the visible scalar coordinate. -/
def wilkieSection4GapIncidence {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    Set (RealEuclidean ((p + 1) + 2)) :=
  (maxwellOrderedWitnessBaseLinearMap p 1 ⁻¹' C ∩
    ⋂ i : Fin 2,
      maxwellOrderedWitnessRelationLinearMap p 1 i ⁻¹' A) ∩
    wilkieSection4GapConstraint p

@[simp]
theorem realEuclideanAppend_append_mem_wilkieSection4GapIncidence_iff
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (x : RealEuclidean p) (ε : ℝ) (values : RealEuclidean 2) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4GapIncidence C A ↔
      x ∈ C ∧ values 0 < values 1 ∧
        (∀ i : Fin 2, values i ∈ maxwellScalarFiber A x) ∧
        ε = values 1 - values 0 := by
  simp [wilkieSection4GapIncidence, wilkieSection4GapConstraint,
    wilkieSection4GapPolynomial,
    maxwellOrderedWitnessBaseLinearMap_apply_append,
    maxwellOrderedWitnessRelationLinearMap_apply_append,
    maxwellOrderedWitnessIncrementPolynomial,
    maxwellOrderedWitnessOutputIndex, maxwellOrderedWitnessValueIndex,
    realEuclideanAppend_castAdd, realEuclideanAppend_natAdd,
    map_sub, MvPolynomial.eval_X, sub_pos,
    eq_comm, and_assoc, and_left_comm, and_comm]
  intro _ _ _ _
  constructor <;> intro h <;> linarith

/-- Wilkie's relation `H` of positive distances between two points in one
scalar fibre, restricted to the base `C`. -/
def wilkieSection4CollisionGapRelation {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    MaxwellRelation p 1 :=
  realEuclideanExistentialProjection
    (wilkieSection4GapIncidence C A)

@[simp]
theorem realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (x : RealEuclidean p) (ε : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ ε) ∈
        wilkieSection4CollisionGapRelation C A ↔
      x ∈ C ∧ ∃ y z : ℝ,
        y ∈ maxwellScalarFiber A x ∧
        z ∈ maxwellScalarFiber A x ∧ y < z ∧ ε = z - y := by
  change (∃ values : RealEuclidean 2,
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ ε)) values ∈
        wilkieSection4GapIncidence C A) ↔ _
  constructor
  · rintro ⟨values, hvalues⟩
    have h :=
      (realEuclideanAppend_append_mem_wilkieSection4GapIncidence_iff
        C A x ε values).mp hvalues
    exact ⟨h.1, values 0, values 1, h.2.2.1 0, h.2.2.1 1,
      h.2.1, h.2.2.2⟩
  · rintro ⟨hx, y, z, hy, hz, hyz, hε⟩
    let values : RealEuclidean 2 := ![y, z]
    refine ⟨values, (realEuclideanAppend_append_mem_wilkieSection4GapIncidence_iff
      C A x ε values).mpr ⟨hx, ?_, ?_, ?_⟩⟩
    · simpa [values]
    · intro i
      fin_cases i
      · simpa [values] using hy
      · simpa [values] using hz
    · simpa [values] using hε

/-- The positive gap relation belongs to the Charbonnel closure whenever its
base and original scalar relation do. -/
theorem wilkieSection4CollisionGapRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1)) :
    wilkieSection4CollisionGapRelation C A ∈
      charbonnelClosure S (p + 1) := by
  have hambient : 0 < (p + 1) + 2 := by omega
  have hbase : maxwellOrderedWitnessBaseLinearMap p 1 ⁻¹' C ∈
      charbonnelClosure S ((p + 1) + 2) :=
    hC.linear_preimage_mem hambient hp hCmem
      (maxwellOrderedWitnessBaseLinearMap p 1)
  have hrelations :
      (⋂ i : Fin 2,
        maxwellOrderedWitnessRelationLinearMap p 1 i ⁻¹' A) ∈
          charbonnelClosure S ((p + 1) + 2) := by
    apply maxwell_charbonnelClosure_iInter_fin_mem hC hambient
    intro i
    exact hC.linear_preimage_mem hambient (by omega) hAmem
      (maxwellOrderedWitnessRelationLinearMap p 1 i)
  have hconstraint : wilkieSection4GapConstraint p ∈
      charbonnelClosure S ((p + 1) + 2) :=
    hC.ws2_polynomialSign hambient
      (polynomialSignConstructible_wilkieSection4GapConstraint p)
  have hincidence : wilkieSection4GapIncidence C A ∈
      charbonnelClosure S ((p + 1) + 2) :=
    hC.ws1_inter hambient
      (hC.ws1_inter hambient hbase hrelations) hconstraint
  exact charbonnelClosure_projection (by omega) hincidence

/-- Wilkie's closed collision locus `H̃`, the zero section of `closure H`. -/
def wilkieSection4CollisionLocus {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  charbonnelZeroSection
    (closure (wilkieSection4CollisionGapRelation C A))

theorem wilkieSection4CollisionLocus_isClosed
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    IsClosed (wilkieSection4CollisionLocus C A) :=
  charbonnelZeroSection_isClosed isClosed_closure

theorem wilkieSection4CollisionLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1)) :
    wilkieSection4CollisionLocus C A ∈ charbonnelClosure S p := by
  apply charbonnelZeroSection_mem_charbonnelClosure hp
  exact charbonnelClosure_topologicalClosure
    (wilkieSection4CollisionGapRelation_mem_charbonnelClosure
      hC hp hCmem hAmem)

/-! ## Avoiding the collision locus gives uniform separation -/

/-- Off `H̃`, positive gaps in all nearby fibres have a uniform lower bound.
This is precisely `MaxwellScalarFiberNoCollision`. -/
theorem maxwellScalarFiberNoCollision_of_disjoint_collisionLocus
    {p : ℕ} {C B : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hBC : B ⊆ C)
    (hdisjoint : Disjoint B (wilkieSection4CollisionLocus C A)) :
    MaxwellScalarFiberNoCollision B A := by
  intro x hxB
  have hxC : x ∈ C := hBC hxB
  have hxnot : x ∉ wilkieSection4CollisionLocus C A := by
    exact Set.disjoint_left.mp hdisjoint hxB
  have hxnotClosure :
      realEuclideanAppend x (fun _ : Fin 1 ↦ (0 : ℝ)) ∉
        closure (wilkieSection4CollisionGapRelation C A) := by
    exact hxnot
  have hcomplNhd :
      (closure (wilkieSection4CollisionGapRelation C A))ᶜ ∈
        nhds (realEuclideanAppend x (fun _ : Fin 1 ↦ (0 : ℝ))) :=
    isClosed_closure.isOpen_compl.mem_nhds hxnotClosure
  let E := realEuclideanAppendScalarContinuousLinearEquiv p
  have hpre : E ⁻¹'
      (closure (wilkieSection4CollisionGapRelation C A))ᶜ ∈
        nhds (x, (0 : ℝ)) := by
    exact E.continuous.continuousAt hcomplNhd
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨δ, hδ, hballU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ρ, hρ, hballV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ, hρ, δ, hδ, ?_⟩
  intro x' hx'B hxx' y hy z hz hyz
  by_contra hgap
  have hgapLt : dist y z < ρ := lt_of_not_ge hgap
  have hgapPos : 0 < dist y z := dist_pos.mpr hyz
  have hx'U : x' ∈ U := hballU (Metric.mem_ball.mpr hxx')
  have hgapV : dist y z ∈ V := by
    apply hballV
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hgapPos.le]
    exact hgapLt
  have hpairPre : (x', dist y z) ∈ E ⁻¹'
      (closure (wilkieSection4CollisionGapRelation C A))ᶜ :=
    hUV ⟨hx'U, hgapV⟩
  have hpairCompl :
      realEuclideanAppend x' (fun _ : Fin 1 ↦ dist y z) ∈
        (closure (wilkieSection4CollisionGapRelation C A))ᶜ := by
    simpa [E, realEuclideanAppendScalar] using hpairPre
  have hpairGap :
      realEuclideanAppend x' (fun _ : Fin 1 ↦ dist y z) ∈
        wilkieSection4CollisionGapRelation C A := by
    rw [realEuclideanAppend_mem_wilkieSection4CollisionGapRelation_iff]
    refine ⟨hBC hx'B, ?_⟩
    rcases lt_or_gt_of_ne hyz with hyz' | hzy'
    · refine ⟨y, z, hy, hz, hyz', ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hyz'.le)]
      ring
    · refine ⟨z, y, hz, hy, hzy', ?_⟩
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hzy'.le)]
  exact hpairCompl (subset_closure hpairGap)

end AbelFormalization
