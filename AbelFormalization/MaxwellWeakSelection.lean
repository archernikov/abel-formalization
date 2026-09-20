import AbelFormalization.MaxwellClosureNullity
import AbelFormalization.MaxwellExtendedSlopeClusterMembership
import AbelFormalization.MaxwellVectorOutputReduction
import Mathlib.Data.Finset.Sort

/-!
# Maxwell--Figueiredo continuous weak selection

This file formalizes the assembly in Figueiredo's Lemma 2.3.1.  It keeps
the two earlier source lemmas which the proof invokes as explicit
propositions:

* `MaxwellLocalConstantScalarFiberCardinality` is the conclusion of Lemma
  2.2.1 needed in the empty-interior scalar branch;
* `MaxwellScalarDiscontinuityControl` is Lemma 2.2.2, stated for a
  one-dimensional Euclidean output.

Everything after those inputs is carried out here.  In particular, the
positive-increment formula really is presented as an existential projection
of a family member, its fibers are proved to be singleton fibers under the
local cardinality conclusion, scalar selections are assembled coordinate by
coordinate, and the coordinate discontinuity loci are removed on one
smaller open ball.  Closure-interior regularity, rather than complement
closure, is what makes that last ball nonempty.

The source uses open cubes.  Open Euclidean balls are used below: they are
polynomial-sign constructible in the maintained finite-coordinate model and
are all that the later arguments consume.
-/

noncomputable section

open Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Scalar fibers and the positive-increment formula -/

/-- The real-valued fiber of a relation with one Euclidean output
coordinate. -/
def maxwellScalarFiber {p : ℕ} (R : MaxwellRelation p 1)
    (x : RealEuclidean p) : Set ℝ :=
  {y | realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ R}

@[simp]
theorem mem_maxwellScalarFiber_iff {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) (y : ℝ) :
    y ∈ maxwellScalarFiber R x ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ R :=
  Iff.rfl

/-- `k + 1` increasingly ordered points in the scalar fiber, with the first
point prescribed to be `y`.  The adjacent strict inequalities are exactly
the source's positive increments `r₂, ..., rₖ > 0`, after replacing the
increments by their successive partial sums. -/
def MaxwellOrderedScalarFiberWitness {p : ℕ}
    (R : MaxwellRelation p 1) (k : ℕ)
    (x : RealEuclidean p) (y : ℝ) : Prop :=
  ∃ values : RealEuclidean (k + 1),
    values 0 = y ∧
    (∀ i : Fin k, values i.castSucc < values i.succ) ∧
    ∀ i : Fin (k + 1), values i ∈ maxwellScalarFiber R x

/-- Every finite scalar fiber of cardinality `k + 1` has a positive-increment
witness, obtained by its increasing enumeration. -/
theorem exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1) :
    ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y := by
  classical
  let s : Finset ℝ := hfinite.toFinset
  have hsCard : s.card = k + 1 := by
    change hfinite.toFinset.card = k + 1
    rw [← Set.ncard_eq_toFinset_card (maxwellScalarFiber R x) hfinite]
    exact hcard
  let values : RealEuclidean (k + 1) :=
    fun i ↦ s.orderEmbOfFin hsCard i
  refine ⟨values 0, values, rfl, ?_, ?_⟩
  · intro i
    exact (s.orderEmbOfFin hsCard).strictMono Fin.castSucc_lt_succ
  · intro i
    have hi : s.orderEmbOfFin hsCard i ∈ s :=
      s.orderEmbOfFin_mem hsCard i
    exact (Set.Finite.mem_toFinset hfinite).mp hi

/-- Under the same exact cardinality hypothesis, the first point in a
positive-increment enumeration is unique. -/
theorem maxwellOrderedScalarFiberWitness_unique
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    {y z : ℝ}
    (hy : MaxwellOrderedScalarFiberWitness R k x y)
    (hz : MaxwellOrderedScalarFiberWitness R k x z) :
    y = z := by
  obtain ⟨v, hv0, hvstep, hvfiber⟩ := hy
  obtain ⟨w, hw0, hwstep, hwfiber⟩ := hz
  have hvmono : StrictMono v :=
    Fin.strictMono_iff_lt_succ.mpr hvstep
  have hwmono : StrictMono w :=
    Fin.strictMono_iff_lt_succ.mpr hwstep
  have hvRange : Set.range v = maxwellScalarFiber R x := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨i, rfl⟩
      exact hvfiber i
    · rw [hcard, Set.ncard_range_of_injective hvmono.injective]
      simp
    · exact hfinite
  have hwRange : Set.range w = maxwellScalarFiber R x := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨i, rfl⟩
      exact hwfiber i
    · rw [hcard, Set.ncard_range_of_injective hwmono.injective]
      simp
    · exact hfinite
  have hw0InV : w 0 ∈ Set.range v := by
    rw [hvRange]
    exact hwfiber 0
  have hv0InW : v 0 ∈ Set.range w := by
    rw [hwRange]
    exact hvfiber 0
  obtain ⟨i, hi⟩ := hw0InV
  obtain ⟨j, hj⟩ := hv0InW
  have hvle : v 0 ≤ w 0 := by
    rw [← hi]
    exact hvmono.monotone (Fin.zero_le i)
  have hwle : w 0 ≤ v 0 := by
    rw [← hj]
    exact hwmono.monotone (Fin.zero_le j)
  rw [← hv0, ← hw0]
  exact le_antisymm hvle hwle

/-- The scalar value selected by the positive-increment formula.  Outside
the locus on which the formula has a witness it is totalized by zero. -/
noncomputable def maxwellOrderedScalarValue {p : ℕ}
    (R : MaxwellRelation p 1) (k : ℕ)
    (x : RealEuclidean p) : ℝ := by
  classical
  exact if h : ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y then
    Classical.choose h
  else 0

/-- One-dimensional Euclidean form of `maxwellOrderedScalarValue`. -/
noncomputable def maxwellOrderedScalarSelector {p : ℕ}
    (R : MaxwellRelation p 1) (k : ℕ) :
    RealEuclidean p → RealEuclidean 1 :=
  fun x _ ↦ maxwellOrderedScalarValue R k x

theorem maxwellOrderedScalarValue_spec {p k : ℕ}
    {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (h : ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y) :
    MaxwellOrderedScalarFiberWitness R k x
      (maxwellOrderedScalarValue R k x) := by
  rw [maxwellOrderedScalarValue, dif_pos h]
  exact Classical.choose_spec h

/-! ## A family-member incidence for the ordered witnesses -/

/-- Coordinate of the displayed scalar value in `(x,y,values)`. -/
def maxwellOrderedWitnessOutputIndex (p k : ℕ) :
    Fin ((p + 1) + (k + 1)) :=
  Fin.castAdd (k + 1) (Fin.natAdd p (0 : Fin 1))

/-- Coordinate of the `i`th ordered fiber value in `(x,y,values)`. -/
def maxwellOrderedWitnessValueIndex (p k : ℕ) (i : Fin (k + 1)) :
    Fin ((p + 1) + (k + 1)) :=
  Fin.natAdd (p + 1) i

/-- Polynomial imposing that the first ordered value is the displayed
output. -/
def maxwellOrderedWitnessFirstPolynomial (p k : ℕ) :
    MvPolynomial (Fin ((p + 1) + (k + 1))) ℝ :=
  MvPolynomial.X (maxwellOrderedWitnessValueIndex p k 0) -
    MvPolynomial.X (maxwellOrderedWitnessOutputIndex p k)

/-- Polynomial whose positivity is the `i`th positive increment. -/
def maxwellOrderedWitnessIncrementPolynomial (p k : ℕ) (i : Fin k) :
    MvPolynomial (Fin ((p + 1) + (k + 1))) ℝ :=
  MvPolynomial.X (maxwellOrderedWitnessValueIndex p k i.succ) -
    MvPolynomial.X (maxwellOrderedWitnessValueIndex p k i.castSucc)

/-- The semialgebraic equality/positive-increment part of the ordered
witness incidence. -/
def maxwellOrderedWitnessConstraint (p k : ℕ) :
    Set (RealEuclidean ((p + 1) + (k + 1))) :=
  {w | MvPolynomial.eval w
      (maxwellOrderedWitnessFirstPolynomial p k) = 0} ∩
    ⋂ i : Fin k,
      {w | 0 < MvPolynomial.eval w
        (maxwellOrderedWitnessIncrementPolynomial p k i)}

theorem polynomialSignConstructible_maxwellOrderedWitnessConstraint
    (p k : ℕ) :
    PolynomialSignConstructible ((p + 1) + (k + 1))
      (maxwellOrderedWitnessConstraint p k) := by
  exact .inter
    (.zero (maxwellOrderedWitnessFirstPolynomial p k))
    (polynomialSignConstructible_iInter_fin _ fun i ↦
      .pos (maxwellOrderedWitnessIncrementPolynomial p k i))

/-- Read the base point from `(x,y,values)`. -/
def maxwellOrderedWitnessBaseLinearMap (p k : ℕ) :
    RealEuclidean ((p + 1) + (k + 1)) →ₗ[ℝ] RealEuclidean p where
  toFun w := realEuclideanTakeLeft
    (realEuclideanTakeLeft (n := p + 1) (m := k + 1) w)
  map_add' := by
    intro v w
    rfl
  map_smul' := by
    intro c v
    rfl

/-- Read `(x,valuesᵢ)` from `(x,y,values)`. -/
def maxwellOrderedWitnessRelationLinearMap (p k : ℕ)
    (i : Fin (k + 1)) :
    RealEuclidean ((p + 1) + (k + 1)) →ₗ[ℝ]
      RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft
      (realEuclideanTakeLeft (n := p + 1) (m := k + 1) w))
    (fun _ : Fin 1 ↦
      realEuclideanTakeRight (n := p + 1) (m := k + 1) w i)
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem maxwellOrderedWitnessBaseLinearMap_apply_append
    {p k : ℕ} (x : RealEuclidean p) (y : RealEuclidean 1)
    (values : RealEuclidean (k + 1)) :
    maxwellOrderedWitnessBaseLinearMap p k
        (realEuclideanAppend (realEuclideanAppend x y) values) = x := by
  change realEuclideanTakeLeft
      (realEuclideanTakeLeft
        (realEuclideanAppend (realEuclideanAppend x y) values)) = x
  rw [realEuclideanTakeLeft_append, realEuclideanTakeLeft_append]

@[simp]
theorem maxwellOrderedWitnessRelationLinearMap_apply_append
    {p k : ℕ} (i : Fin (k + 1))
    (x : RealEuclidean p) (y : RealEuclidean 1)
    (values : RealEuclidean (k + 1)) :
    maxwellOrderedWitnessRelationLinearMap p k i
        (realEuclideanAppend (realEuclideanAppend x y) values) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ values i) := by
  change realEuclideanAppend
      (realEuclideanTakeLeft
        (realEuclideanTakeLeft
          (realEuclideanAppend (realEuclideanAppend x y) values)))
      (fun _ : Fin 1 ↦
        realEuclideanTakeRight
          (realEuclideanAppend (realEuclideanAppend x y) values) i) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]

/-- Incidence expressing membership of all `k + 1` increasingly ordered
fiber points.  Its final block is existentially projected away below. -/
def maxwellOrderedScalarSelectionIncidence {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (k : ℕ) :
    Set (RealEuclidean ((p + 1) + (k + 1))) :=
  (maxwellOrderedWitnessBaseLinearMap p k ⁻¹' U ∩
    ⋂ i : Fin (k + 1),
      maxwellOrderedWitnessRelationLinearMap p k i ⁻¹' R) ∩
    maxwellOrderedWitnessConstraint p k

@[simp]
theorem realEuclideanAppend_append_mem_maxwellOrderedScalarSelectionIncidence_iff
    {p k : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (x : RealEuclidean p) (y : ℝ)
    (values : RealEuclidean (k + 1)) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) values ∈
        maxwellOrderedScalarSelectionIncidence U R k ↔
      x ∈ U ∧ values 0 = y ∧
        (∀ i : Fin k, values i.castSucc < values i.succ) ∧
        ∀ i : Fin (k + 1),
          values i ∈ maxwellScalarFiber R x := by
  simp [maxwellOrderedScalarSelectionIncidence,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
    maxwellOrderedWitnessConstraint, Set.mem_setOf_eq,
    maxwellOrderedWitnessBaseLinearMap_apply_append,
    maxwellOrderedWitnessRelationLinearMap_apply_append,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    maxwellScalarFiber, maxwellOrderedWitnessFirstPolynomial,
    maxwellOrderedWitnessIncrementPolynomial, map_sub,
    MvPolynomial.eval_X, maxwellOrderedWitnessOutputIndex,
    maxwellOrderedWitnessValueIndex, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd, sub_eq_zero, sub_pos,
    and_assoc, and_left_comm, and_comm]

/-- The positive-increment selection graph is the visible projection of its
incidence. -/
def maxwellOrderedScalarSelectionGraph {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (k : ℕ) :
    Set (RealEuclidean (p + 1)) :=
  realEuclideanExistentialProjection
    (maxwellOrderedScalarSelectionIncidence U R k)

@[simp]
theorem realEuclideanAppend_mem_maxwellOrderedScalarSelectionGraph_iff
    {p k : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (x : RealEuclidean p) (y : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOrderedScalarSelectionGraph U R k ↔
      x ∈ U ∧ MaxwellOrderedScalarFiberWitness R k x y := by
  change (∃ values : RealEuclidean (k + 1),
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) values ∈
        maxwellOrderedScalarSelectionIncidence U R k) ↔ _
  simp only [
    realEuclideanAppend_append_mem_maxwellOrderedScalarSelectionIncidence_iff,
    MaxwellOrderedScalarFiberWitness]
  aesop

/-- Finite intersections of Charbonnel-closure members stay in the same
arity. -/
theorem maxwell_charbonnelClosure_iInter_fin_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {d k : ℕ} (hd : 0 < d)
    (A : Fin k → Set (RealEuclidean d))
    (hA : ∀ i, A i ∈ charbonnelClosure S d) :
    (⋂ i, A i) ∈ charbonnelClosure S d := by
  induction k with
  | zero =>
      simpa using hC.ws2_polynomialSign hd
        (polynomialSignConstructible_univ d)
  | succ k ih =>
      rw [show (⋂ i : Fin (k + 1), A i) =
          A 0 ∩ ⋂ j : Fin k, A j.succ by
        ext x
        simp only [Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro hx
          exact ⟨hx 0, fun j ↦ hx j.succ⟩
        · rintro ⟨hzero, hsucc⟩ i
          exact Fin.cases hzero (fun j ↦ hsucc j) i]
      exact hC.ws1_inter hd (hA 0)
        (ih (fun j ↦ A j.succ) (fun j ↦ hA j.succ))

/-- The positive-increment selection graph is a member of the Charbonnel
closure whenever its domain and relation are. -/
theorem maxwellOrderedScalarSelectionGraph_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p k : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellOrderedScalarSelectionGraph U R k ∈
      charbonnelClosure S (p + 1) := by
  have hambient : 0 < (p + 1) + (k + 1) := by omega
  have hbase : maxwellOrderedWitnessBaseLinearMap p k ⁻¹' U ∈
      charbonnelClosure S ((p + 1) + (k + 1)) :=
    hC.linear_preimage_mem hambient hp hU
      (maxwellOrderedWitnessBaseLinearMap p k)
  have hrelations :
      (⋂ i : Fin (k + 1),
        maxwellOrderedWitnessRelationLinearMap p k i ⁻¹' R) ∈
          charbonnelClosure S ((p + 1) + (k + 1)) := by
    apply maxwell_charbonnelClosure_iInter_fin_mem hC hambient
    intro i
    exact hC.linear_preimage_mem hambient (by omega) hR
      (maxwellOrderedWitnessRelationLinearMap p k i)
  have hconstraint : maxwellOrderedWitnessConstraint p k ∈
      charbonnelClosure S ((p + 1) + (k + 1)) :=
    hC.ws2_polynomialSign hambient
      (polynomialSignConstructible_maxwellOrderedWitnessConstraint p k)
  have hincidence : maxwellOrderedScalarSelectionIncidence U R k ∈
      charbonnelClosure S ((p + 1) + (k + 1)) :=
    hC.ws1_inter hambient
      (hC.ws1_inter hambient hbase hrelations) hconstraint
  exact charbonnelClosure_projection (by omega) hincidence

/-- Exact local fiber cardinality turns the projected ordered relation into
the graph of the canonical selected function. -/
theorem maxwellOrderedScalarSelectionGraph_eq_functionGraph
    {p k : ℕ} {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ U,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellOrderedScalarSelectionGraph U R k =
      maxwellFunctionGraph U (maxwellOrderedScalarSelector R k) := by
  ext z
  have hyCoordinates : realEuclideanTakeRight z =
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) := by
    funext i
    rw [show i = 0 from Fin.eq_zero i]
  rw [← realEuclideanAppend_takeLeft_takeRight (n := p) (m := 1) z,
    hyCoordinates,
    realEuclideanAppend_mem_maxwellOrderedScalarSelectionGraph_iff,
    realEuclideanAppend_mem_maxwellFunctionGraph_iff]
  constructor
  · rintro ⟨hx, hy⟩
    have hex : ∃ a : ℝ, MaxwellOrderedScalarFiberWitness R k
        (realEuclideanTakeLeft z) a :=
      exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ
        (hfiber (realEuclideanTakeLeft z) hx).1
        (hfiber (realEuclideanTakeLeft z) hx).2
    have hselected := maxwellOrderedScalarValue_spec (R := R) (k := k) hex
    have heq : realEuclideanTakeRight z 0 =
        maxwellOrderedScalarValue R k (realEuclideanTakeLeft z) :=
      maxwellOrderedScalarFiberWitness_unique
        (hfiber (realEuclideanTakeLeft z) hx).1
        (hfiber (realEuclideanTakeLeft z) hx).2 hy hselected
    refine ⟨hx, ?_⟩
    funext i
    rw [show i = 0 from Fin.eq_zero i]
    exact heq
  · rintro ⟨hx, hy⟩
    have hex : ∃ a : ℝ, MaxwellOrderedScalarFiberWitness R k
        (realEuclideanTakeLeft z) a :=
      exists_maxwellOrderedScalarFiberWitness_of_ncard_eq_succ
        (hfiber (realEuclideanTakeLeft z) hx).1
        (hfiber (realEuclideanTakeLeft z) hx).2
    refine ⟨hx, ?_⟩
    have hselected := maxwellOrderedScalarValue_spec (R := R) (k := k) hex
    have hy0 : realEuclideanTakeRight z 0 =
        maxwellOrderedScalarValue R k (realEuclideanTakeLeft z) := by
      simpa only [maxwellOrderedScalarSelector] using congrFun hy 0
    rw [hy0]
    exact hselected

/-- Every point of the ordered selection graph is a point of the original
relation. -/
theorem maxwellOrderedScalarSelectionGraph_subset
    {p k : ℕ} {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} :
    maxwellOrderedScalarSelectionGraph U R k ⊆ R := by
  intro z hz
  have hyCoordinates : realEuclideanTakeRight z =
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) := by
    funext i
    rw [show i = 0 from Fin.eq_zero i]
  rw [← realEuclideanAppend_takeLeft_takeRight (n := p) (m := 1) z,
    hyCoordinates] at hz ⊢
  have hgraph :=
    (realEuclideanAppend_mem_maxwellOrderedScalarSelectionGraph_iff
      U R (realEuclideanTakeLeft z)
        (realEuclideanTakeRight z 0)).mp hz
  obtain ⟨values, hzero, _hstep, hvalues⟩ := hgraph.2
  have hfirst := hvalues 0
  rw [hzero] at hfirst
  exact hfirst

/-! ## The two source interfaces -/

/-- The exact consequence of Figueiredo's Lemma 2.2.1 used by weak
selection.  If the scalar relation restricted over a nonempty open base has
empty interior, then on a smaller nonempty open family member every scalar
fiber has one fixed positive finite cardinality. -/
def MaxwellLocalConstantScalarFiberCardinality
    (C : EuclideanSetFamily) : Prop :=
  ∀ {p : ℕ}, 0 < p →
    ∀ {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1},
      IsOpen B → B.Nonempty → B ∈ C p → R ∈ C (p + 1) →
      MaxwellHasFullFibersOver B R →
      interior (maxwellRelationRestrict R B) = ∅ →
      ∃ (k : ℕ) (U : Set (RealEuclidean p)),
        IsOpen U ∧ U.Nonempty ∧ U ⊆ B ∧ U ∈ C p ∧
        ∀ x ∈ U,
          (maxwellScalarFiber R x).Finite ∧
          (maxwellScalarFiber R x).ncard = k + 1

/-- The relative discontinuity locus of a one-coordinate function. -/
def maxwellScalarDiscontinuityLocus {p : ℕ}
    (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1) :
    Set (RealEuclidean p) :=
  {x | x ∈ U ∧ ¬ ContinuousWithinAt f U x}

/-- The exact conclusion of Figueiredo's Lemma 2.2.2 used in Lemma 2.3.1:
the discontinuity locus of a family-member scalar graph is itself a family
member and has empty interior. -/
def MaxwellScalarDiscontinuityControl
    (C : EuclideanSetFamily) : Prop :=
  ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p))
      (f : RealEuclidean p → RealEuclidean 1),
      U ∈ C p → maxwellFunctionGraph U f ∈ C (p + 1) →
      maxwellScalarDiscontinuityLocus U f ∈ C p ∧
        interior (maxwellScalarDiscontinuityLocus U f) = ∅

/-! ## Selection data and the scalar split -/

/-- A family-member graph locally selecting a relation. -/
structure MaxwellWeakSelectionData
    (C : EuclideanSetFamily) {p q : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p q) where
  U : Set (RealEuclidean p)
  phi : RealEuclidean p → RealEuclidean q
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  U_subset : U ⊆ B
  U_mem : U ∈ C p
  graph_mem : maxwellFunctionGraph U phi ∈ C (p + q)
  graph_subset : maxwellFunctionGraph U phi ⊆ R

/-- Continuous version of `MaxwellWeakSelectionData`. -/
structure MaxwellContinuousWeakSelectionData
    (C : EuclideanSetFamily) {p q : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p q)
    extends MaxwellWeakSelectionData C B R where
  phi_continuous : ContinuousOn phi U

/-- Family-level form of Figueiredo's continuous weak-selection lemma. -/
def MaxwellContinuousWeakSelection (C : EuclideanSetFamily) : Prop :=
  ∀ {p q : ℕ}, 0 < p → 0 < q →
    ∀ {B : Set (RealEuclidean p)} {R : MaxwellRelation p q},
      IsOpen B → B.Nonempty → B ∈ C p →
      R ∈ C (p + q) → MaxwellHasFullFibersOver B R →
      Nonempty (MaxwellContinuousWeakSelectionData C B R)

/-- The graph of a constant one-coordinate map is the flat product of its
domain with the corresponding singleton. -/
theorem maxwellFunctionGraph_const_scalar_eq_product
    {p : ℕ} (U : Set (RealEuclidean p)) (b : RealEuclidean 1) :
    maxwellFunctionGraph U (fun _ ↦ b) =
      realEuclideanSetProduct U ({b} : Set (RealEuclidean 1)) := by
  ext z
  change (∃ x ∈ U, z = realEuclideanAppend x b) ↔
    realEuclideanTakeLeft z ∈ U ∧
      realEuclideanTakeRight z ∈ ({b} : Set (RealEuclidean 1))
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa only [realEuclideanTakeLeft_append] using hx,
      by simp only [realEuclideanTakeRight_append, Set.mem_singleton_iff]⟩
  · rintro ⟨hx, hb⟩
    have hright : realEuclideanTakeRight z = b := by
      simpa only [Set.mem_singleton_iff] using hb
    refine ⟨realEuclideanTakeLeft z, hx, ?_⟩
    rw [← hright]
    exact (realEuclideanAppend_takeLeft_takeRight z).symm

/-- The interior branch of the scalar proof: an interior point of the
restricted relation gives a smaller base ball on which one constant value is
in every fiber. -/
theorem exists_constant_scalarWeakSelection_of_restrict_interior
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hB : B ∈ charbonnelClosure S p)
    (hinterior :
      (interior (maxwellRelationRestrict R B)).Nonempty) :
    Nonempty (MaxwellWeakSelectionData
      (charbonnelClosure S) B R) := by
  obtain ⟨z, hz⟩ := hinterior
  let x₀ : RealEuclidean p := realEuclideanTakeLeft z
  let b : RealEuclidean 1 := realEuclideanTakeRight z
  have hzCanonical : realEuclideanAppend x₀ b = z :=
    realEuclideanAppend_takeLeft_takeRight z
  let constantLift : RealEuclidean p → RealEuclidean (p + 1) :=
    fun x ↦ realEuclideanAppend x b
  have hconstantLiftContinuous : Continuous constantLift := by
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [constantLift, realEuclideanAppend] using continuous_apply j
    · simpa [constantLift, realEuclideanAppend] using
        (continuous_const : Continuous (fun _ : RealEuclidean p ↦ b j))
  let V : Set (RealEuclidean p) :=
    constantLift ⁻¹' interior (maxwellRelationRestrict R B)
  have hVopen : IsOpen V :=
    isOpen_interior.preimage hconstantLiftContinuous
  have hx₀V : x₀ ∈ V := by
    change constantLift x₀ ∈ interior (maxwellRelationRestrict R B)
    rw [show constantLift x₀ = z from hzCanonical]
    exact hz
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hVopen x₀ hx₀V
  let U : Set (RealEuclidean p) := Metric.ball x₀ ε
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUnonempty : U.Nonempty := ⟨x₀, Metric.mem_ball_self hε⟩
  have hUsubsetB : U ⊆ B := by
    intro x hx
    have hs := interior_subset (hball hx)
    exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
      R B x b).mp hs |>.2
  have hUmem : U ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp (polynomialSignConstructible_ball x₀ hε)
  have hbmem : ({b} : Set (RealEuclidean 1)) ∈
      charbonnelClosure S 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_singleton b)
  have hgraphMem : maxwellFunctionGraph U (fun _ ↦ b) ∈
      charbonnelClosure S (p + 1) := by
    rw [maxwellFunctionGraph_const_scalar_eq_product]
    exact hC.ws3_prod hp (by omega) hUmem hbmem
  have hgraphSubset : maxwellFunctionGraph U (fun _ ↦ b) ⊆ R := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have hs := interior_subset (hball hx)
    exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
      R B x b).mp hs |>.1
  exact ⟨
    { U := U
      phi := fun _ ↦ b
      U_open := hUopen
      U_nonempty := hUnonempty
      U_subset := hUsubsetB
      U_mem := hUmem
      graph_mem := hgraphMem
      graph_subset := hgraphSubset }⟩

/-- The scalar claim in Figueiredo's proof.  Its interior branch is
elementary; its empty-interior branch invokes precisely the local-cardinality
interface and the positive-increment construction above. -/
theorem maxwellScalarWeakSelection_of_localConstantFiberCardinality
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hfull : MaxwellHasFullFibersOver B R) :
    Nonempty (MaxwellWeakSelectionData
      (charbonnelClosure S) B R) := by
  by_cases hinterior :
      (interior (maxwellRelationRestrict R B)).Nonempty
  · exact exists_constant_scalarWeakSelection_of_restrict_interior
      hC hp hBmem hinterior
  · have hinteriorEmpty :
        interior (maxwellRelationRestrict R B) = ∅ :=
      not_nonempty_iff_eq_empty.mp hinterior
    obtain ⟨k, U, hUopen, hUnonempty, hUsubset, hUmem, hfiber⟩ :=
      hcard hp hBopen hBnonempty hBmem hRmem hfull hinteriorEmpty
    have horderedMem : maxwellOrderedScalarSelectionGraph U R k ∈
        charbonnelClosure S (p + 1) :=
      maxwellOrderedScalarSelectionGraph_mem_charbonnelClosure
        hC hp hUmem hRmem
    have hgraphEq :=
      maxwellOrderedScalarSelectionGraph_eq_functionGraph hfiber
    exact ⟨
      { U := U
        phi := maxwellOrderedScalarSelector R k
        U_open := hUopen
        U_nonempty := hUnonempty
        U_subset := hUsubset
        U_mem := hUmem
        graph_mem := by rwa [← hgraphEq]
        graph_subset := by
          rw [← hgraphEq]
          exact maxwellOrderedScalarSelectionGraph_subset }⟩

/-! ## Coordinate induction for vector outputs -/

/-- Reassociate `(x,(y,z))` as `((x,y),z)` and project the last coordinate.
This is the prefix relation in the source's induction on output arity. -/
def maxwellOutputPrefixRelation {p q : ℕ}
    (R : MaxwellRelation p (q + 1)) : MaxwellRelation p q :=
  realEuclideanExistentialProjection
    (realEuclideanCoordinateReindex
      (finAddAssocCoordinateEquiv p q 1) '' R)

@[simp]
theorem realEuclideanAppend_mem_maxwellOutputPrefixRelation_iff
    {p q : ℕ} (R : MaxwellRelation p (q + 1))
    (x : RealEuclidean p) (y : RealEuclidean q) :
    realEuclideanAppend x y ∈ maxwellOutputPrefixRelation R ↔
      ∃ z : RealEuclidean 1,
        realEuclideanAppend x (realEuclideanAppend y z) ∈ R := by
  constructor
  · rintro ⟨z, w, hwR, hwEq⟩
    have hw : w = realEuclideanAppend x (realEuclideanAppend y z) := by
      apply (realEuclideanCoordinateReindex
        (finAddAssocCoordinateEquiv p q 1)).injective
      rw [realEuclideanCoordinateReindex_finAddAssoc_append]
      exact hwEq
    exact ⟨z, hw ▸ hwR⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, realEuclideanAppend x (realEuclideanAppend y z), hz, ?_⟩
    exact realEuclideanCoordinateReindex_finAddAssoc_append x y z

theorem maxwellOutputPrefixRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {R : MaxwellRelation p (q + 1)}
    (hR : R ∈ charbonnelClosure S (p + (q + 1))) :
    maxwellOutputPrefixRelation R ∈ charbonnelClosure S (p + q) := by
  have hreindexed :
      realEuclideanCoordinateReindex
          (finAddAssocCoordinateEquiv p q 1) '' R ∈
        charbonnelClosure S ((p + q) + 1) :=
    hC.toDescriptionReindexBase.coordinateReindex (by omega) hR
      (finAddAssocCoordinateEquiv p q 1)
  exact charbonnelClosure_projection (by omega) hreindexed

/-- Read `(x,prefix)` from coordinates `(x,last,prefix)`. -/
def maxwellResidualPrefixLinearMap (p q : ℕ) :
    RealEuclidean ((p + 1) + q) →ₗ[ℝ] RealEuclidean (p + q) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft
      (realEuclideanTakeLeft (n := p + 1) (m := q) w))
    (realEuclideanTakeRight (n := p + 1) (m := q) w)
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

/-- Read `(x,(prefix,last))` from coordinates `(x,last,prefix)`. -/
def maxwellResidualOriginalLinearMap (p q : ℕ) :
    RealEuclidean ((p + 1) + q) →ₗ[ℝ]
      RealEuclidean (p + (q + 1)) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft
      (realEuclideanTakeLeft (n := p + 1) (m := q) w))
    (realEuclideanAppend
      (realEuclideanTakeRight (n := p + 1) (m := q) w)
      (realEuclideanTakeRight (n := p) (m := 1)
        (realEuclideanTakeLeft (n := p + 1) (m := q) w)))
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
    · refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) j <;>
        simp [realEuclideanAppend, realEuclideanTakeLeft,
          realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
    · refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) j <;>
        simp [realEuclideanAppend, realEuclideanTakeLeft,
          realEuclideanTakeRight]

/-- Incidence defining the possible final coordinate after a prefix graph
has been selected. -/
def maxwellScalarResidualIncidence {p q : ℕ}
    (G : MaxwellRelation p q) (R : MaxwellRelation p (q + 1)) :
    Set (RealEuclidean ((p + 1) + q)) :=
  maxwellResidualPrefixLinearMap p q ⁻¹' G ∩
    maxwellResidualOriginalLinearMap p q ⁻¹' R

/-- Scalar residual relation after projecting away the already selected
prefix. -/
def maxwellScalarResidualRelation {p q : ℕ}
    (G : MaxwellRelation p q) (R : MaxwellRelation p (q + 1)) :
    MaxwellRelation p 1 :=
  realEuclideanExistentialProjection
    (maxwellScalarResidualIncidence G R)

@[simp]
theorem realEuclideanAppend_mem_maxwellScalarResidualRelation_iff
    {p q : ℕ} (G : MaxwellRelation p q)
    (R : MaxwellRelation p (q + 1))
    (x : RealEuclidean p) (last : RealEuclidean 1) :
    realEuclideanAppend x last ∈ maxwellScalarResidualRelation G R ↔
      ∃ head : RealEuclidean q,
        realEuclideanAppend x head ∈ G ∧
        realEuclideanAppend x (realEuclideanAppend head last) ∈ R := by
  change (∃ head : RealEuclidean q,
    realEuclideanAppend (realEuclideanAppend x last) head ∈
      maxwellScalarResidualIncidence G R) ↔ _
  simp [maxwellScalarResidualIncidence,
    maxwellResidualPrefixLinearMap, maxwellResidualOriginalLinearMap]

theorem maxwellScalarResidualRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {G : MaxwellRelation p q} {R : MaxwellRelation p (q + 1)}
    (hG : G ∈ charbonnelClosure S (p + q))
    (hR : R ∈ charbonnelClosure S (p + (q + 1))) :
    maxwellScalarResidualRelation G R ∈
      charbonnelClosure S (p + 1) := by
  have hambient : 0 < (p + 1) + q := by omega
  have hprefix : maxwellResidualPrefixLinearMap p q ⁻¹' G ∈
      charbonnelClosure S ((p + 1) + q) :=
    hC.linear_preimage_mem hambient (by omega) hG
      (maxwellResidualPrefixLinearMap p q)
  have horiginal : maxwellResidualOriginalLinearMap p q ⁻¹' R ∈
      charbonnelClosure S ((p + 1) + q) :=
    hC.linear_preimage_mem hambient (by omega) hR
      (maxwellResidualOriginalLinearMap p q)
  have hincidence : maxwellScalarResidualIncidence G R ∈
      charbonnelClosure S ((p + 1) + q) :=
    hC.ws1_inter hambient hprefix horiginal
  exact charbonnelClosure_projection (by omega) hincidence

/-- Read `(x,prefix)` from ordinary output coordinates
`(x,(prefix,last))`. -/
def maxwellJoinPrefixLinearMap (p q : ℕ) :
    RealEuclidean (p + (q + 1)) →ₗ[ℝ] RealEuclidean (p + q) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft (n := p) (m := q + 1) w)
    (realEuclideanTakeLeft (n := q) (m := 1)
      (realEuclideanTakeRight (n := p) (m := q + 1) w))
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

/-- Read `(x,last)` from ordinary output coordinates
`(x,(prefix,last))`. -/
def maxwellJoinLastLinearMap (p q : ℕ) :
    RealEuclidean (p + (q + 1)) →ₗ[ℝ] RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft (n := p) (m := q + 1) w)
    (realEuclideanTakeRight (n := q) (m := 1)
      (realEuclideanTakeRight (n := p) (m := q + 1) w))
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem maxwellJoinPrefixLinearMap_apply_append_append
    {p q : ℕ} (x : RealEuclidean p) (head : RealEuclidean q)
    (last : RealEuclidean 1) :
    maxwellJoinPrefixLinearMap p q
        (realEuclideanAppend x (realEuclideanAppend head last)) =
      realEuclideanAppend x head := by
  change realEuclideanAppend
      (realEuclideanTakeLeft
        (realEuclideanAppend x (realEuclideanAppend head last)))
      (realEuclideanTakeLeft
        (realEuclideanTakeRight
          (realEuclideanAppend x (realEuclideanAppend head last)))) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    realEuclideanTakeLeft_append]

@[simp]
theorem maxwellJoinLastLinearMap_apply_append_append
    {p q : ℕ} (x : RealEuclidean p) (head : RealEuclidean q)
    (last : RealEuclidean 1) :
    maxwellJoinLastLinearMap p q
        (realEuclideanAppend x (realEuclideanAppend head last)) =
      realEuclideanAppend x last := by
  change realEuclideanAppend
      (realEuclideanTakeLeft
        (realEuclideanAppend x (realEuclideanAppend head last)))
      (realEuclideanTakeRight
        (realEuclideanTakeRight
          (realEuclideanAppend x (realEuclideanAppend head last)))) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    realEuclideanTakeRight_append]

/-- Join a prefix graph and a final-coordinate graph over their common base. -/
def maxwellJoinFunctionGraphs {p q : ℕ}
    (G : MaxwellRelation p q) (H : MaxwellRelation p 1) :
    MaxwellRelation p (q + 1) :=
  maxwellJoinPrefixLinearMap p q ⁻¹' G ∩
    maxwellJoinLastLinearMap p q ⁻¹' H

theorem maxwellJoinFunctionGraphs_eq_functionGraph
    {p q : ℕ} (U V : Set (RealEuclidean p))
    (phi : RealEuclidean p → RealEuclidean q)
    (last : RealEuclidean p → RealEuclidean 1) :
    maxwellJoinFunctionGraphs
        (maxwellFunctionGraph U phi)
        (maxwellFunctionGraph V last) =
      maxwellFunctionGraph (U ∩ V)
        (fun x ↦ realEuclideanAppend (phi x) (last x)) := by
  ext z
  rw [← realEuclideanAppend_takeLeft_takeRight
    (n := p) (m := q + 1) z]
  rw [← realEuclideanAppend_takeLeft_takeRight
    (n := q) (m := 1)
    (realEuclideanTakeRight (n := p) (m := q + 1) z)]
  simp only [maxwellJoinFunctionGraphs, Set.mem_inter_iff,
    Set.mem_preimage,
    maxwellJoinPrefixLinearMap_apply_append_append,
    maxwellJoinLastLinearMap_apply_append_append,
    realEuclideanAppend_mem_maxwellFunctionGraph_iff]
  constructor
  · rintro ⟨⟨hxU, hhead⟩, hxV, hlast⟩
    exact ⟨⟨hxU, hxV⟩, by rw [hhead, hlast]⟩
  · rintro ⟨⟨hxU, hxV⟩, hout⟩
    have hhead :
        realEuclideanTakeLeft
            (realEuclideanTakeRight (n := p) (m := q + 1) z) =
          phi (realEuclideanTakeLeft z) := by
      simpa only [realEuclideanTakeLeft_append] using
        congrArg
          (fun w : RealEuclidean (q + 1) ↦
            realEuclideanTakeLeft (n := q) (m := 1) w) hout
    have hlast :
        realEuclideanTakeRight
            (realEuclideanTakeRight (n := p) (m := q + 1) z) =
          last (realEuclideanTakeLeft z) := by
      simpa only [realEuclideanTakeRight_append] using
        congrArg
          (fun w : RealEuclidean (q + 1) ↦
            realEuclideanTakeRight (n := q) (m := 1) w) hout
    exact ⟨⟨hxU, hhead⟩, hxV, hlast⟩

theorem maxwellJoinFunctionGraphs_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {G : MaxwellRelation p q} {H : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + q))
    (hH : H ∈ charbonnelClosure S (p + 1)) :
    maxwellJoinFunctionGraphs G H ∈
      charbonnelClosure S (p + (q + 1)) := by
  have hprefix := hC.linear_preimage_mem (by omega) (by omega) hG
    (maxwellJoinPrefixLinearMap p q)
  have hlast := hC.linear_preimage_mem (by omega) (by omega) hH
    (maxwellJoinLastLinearMap p q)
  exact hC.ws1_inter (by omega) hprefix hlast

/-- Scalar selection implies arbitrary finite-output weak selection by the
coordinate induction in Figueiredo's proof. -/
theorem maxwellWeakSelection_succOutput_of_localConstantFiberCardinality
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) :
    ∀ (r : ℕ) {B : Set (RealEuclidean p)}
      {R : MaxwellRelation p (r + 1)},
      IsOpen B → B.Nonempty → B ∈ charbonnelClosure S p →
      R ∈ charbonnelClosure S (p + (r + 1)) →
      MaxwellHasFullFibersOver B R →
      Nonempty (MaxwellWeakSelectionData
        (charbonnelClosure S) B R) := by
  intro r
  induction r with
  | zero =>
      intro B R hBopen hBnonempty hBmem hRmem hfull
      exact maxwellScalarWeakSelection_of_localConstantFiberCardinality
        hC hcard hp hBopen hBnonempty hBmem hRmem hfull
  | succ r ih =>
      intro B R hBopen hBnonempty hBmem hRmem hfull
      let P : MaxwellRelation p (r + 1) := maxwellOutputPrefixRelation R
      have hPmem : P ∈ charbonnelClosure S (p + (r + 1)) :=
        maxwellOutputPrefixRelation_mem_charbonnelClosure
          hC hp (by omega) hRmem
      have hPfull : MaxwellHasFullFibersOver B P := by
        intro x hx
        obtain ⟨y, hy⟩ := hfull x hx
        change realEuclideanAppend x y ∈ R at hy
        refine ⟨realEuclideanTakeLeft y, ?_⟩
        change realEuclideanAppend x (realEuclideanTakeLeft y) ∈ P
        rw [realEuclideanAppend_mem_maxwellOutputPrefixRelation_iff]
        refine ⟨realEuclideanTakeRight y, ?_⟩
        simpa only [realEuclideanAppend_take] using hy
      obtain ⟨prefixSelection⟩ :=
        ih hBopen hBnonempty hBmem hPmem hPfull
      let G : MaxwellRelation p (r + 1) :=
        maxwellFunctionGraph prefixSelection.U prefixSelection.phi
      let T : MaxwellRelation p 1 :=
        maxwellScalarResidualRelation G R
      have hTmem : T ∈ charbonnelClosure S (p + 1) :=
        maxwellScalarResidualRelation_mem_charbonnelClosure
          hC hp (by omega) prefixSelection.graph_mem hRmem
      have hTfull : MaxwellHasFullFibersOver prefixSelection.U T := by
        intro x hx
        have hprefixP : realEuclideanAppend x (prefixSelection.phi x) ∈ P :=
          prefixSelection.graph_subset
            ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
              prefixSelection.U prefixSelection.phi x
                (prefixSelection.phi x)).mpr ⟨hx, rfl⟩)
        obtain ⟨last, hlast⟩ :=
          (realEuclideanAppend_mem_maxwellOutputPrefixRelation_iff
            R x (prefixSelection.phi x)).mp hprefixP
        refine ⟨last, ?_⟩
        change realEuclideanAppend x last ∈ T
        rw [realEuclideanAppend_mem_maxwellScalarResidualRelation_iff]
        exact ⟨prefixSelection.phi x,
          (realEuclideanAppend_mem_maxwellFunctionGraph_iff
            prefixSelection.U prefixSelection.phi x
              (prefixSelection.phi x)).mpr ⟨hx, rfl⟩,
          hlast⟩
      obtain ⟨lastSelection⟩ :=
        maxwellScalarWeakSelection_of_localConstantFiberCardinality
          hC hcard hp prefixSelection.U_open
            prefixSelection.U_nonempty prefixSelection.U_mem hTmem hTfull
      let phi : RealEuclidean p → RealEuclidean ((r + 1) + 1) :=
        fun x ↦ realEuclideanAppend
          (prefixSelection.phi x) (lastSelection.phi x)
      have hjoinMem : maxwellJoinFunctionGraphs G
          (maxwellFunctionGraph lastSelection.U lastSelection.phi) ∈
          charbonnelClosure S (p + ((r + 1) + 1)) :=
        maxwellJoinFunctionGraphs_mem_charbonnelClosure hC hp (by omega)
          prefixSelection.graph_mem lastSelection.graph_mem
      have hgraphEq : maxwellFunctionGraph lastSelection.U phi =
          maxwellJoinFunctionGraphs G
            (maxwellFunctionGraph lastSelection.U lastSelection.phi) := by
        rw [maxwellJoinFunctionGraphs_eq_functionGraph]
        rw [inter_eq_right.mpr lastSelection.U_subset]
      refine ⟨
        { U := lastSelection.U
          phi := phi
          U_open := lastSelection.U_open
          U_nonempty := lastSelection.U_nonempty
          U_subset := lastSelection.U_subset.trans prefixSelection.U_subset
          U_mem := lastSelection.U_mem
          graph_mem := by rwa [hgraphEq]
          graph_subset := ?_ }⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hlastGraph : realEuclideanAppend x (lastSelection.phi x) ∈ T :=
        lastSelection.graph_subset
          ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
            lastSelection.U lastSelection.phi x
              (lastSelection.phi x)).mpr ⟨hx, rfl⟩)
      obtain ⟨head, hprefixGraph, horiginal⟩ :=
        (realEuclideanAppend_mem_maxwellScalarResidualRelation_iff
          G R x (lastSelection.phi x)).mp hlastGraph
      have hprefixEq : head = prefixSelection.phi x :=
        ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
          prefixSelection.U prefixSelection.phi x head).mp
            hprefixGraph).2
      simpa [phi, hprefixEq] using horiginal

/-- Arbitrary positive output arity version of the preceding induction. -/
theorem maxwellWeakSelection_of_localConstantFiberCardinality
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S))
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p q}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p)
    (hRmem : R ∈ charbonnelClosure S (p + q))
    (hfull : MaxwellHasFullFibersOver B R) :
    Nonempty (MaxwellWeakSelectionData
      (charbonnelClosure S) B R) := by
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact maxwellWeakSelection_succOutput_of_localConstantFiberCardinality
    hC hcard hp r hBopen hBnonempty hBmem hRmem hfull

/-! ## Removing the discontinuity loci -/

/-- An open nonempty Euclidean set contains an open ball disjoint from a
closed set with empty interior. -/
theorem exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
    {p : ℕ} {U A : Set (RealEuclidean p)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hAclosed : IsClosed A) (hAempty : interior A = ∅) :
    ∃ (x : RealEuclidean p) (ε : ℝ),
      0 < ε ∧ Metric.ball x ε ⊆ U \ A := by
  have hUnotSubset : ¬ U ⊆ A := by
    intro hsubset
    have hUint : U ⊆ interior A :=
      hUopen.subset_interior_iff.mpr hsubset
    obtain ⟨x, hx⟩ := hUnonempty
    simpa [hAempty] using hUint hx
  obtain ⟨x, hxU, hxA⟩ := Set.not_subset.mp hUnotSubset
  have hxDiff : x ∈ U \ A := ⟨hxU, hxA⟩
  have hdiffOpen : IsOpen (U \ A) := hUopen.sdiff hAclosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hdiffOpen x hxDiff
  exact ⟨x, ε, hε, hball⟩

/-- Restricting the domain of a function graph is intersection with the
corresponding visible cylinder. -/
theorem maxwellFunctionGraph_restrict_eq_inter_product
    {p q : ℕ} {U : Set (RealEuclidean p)}
    (V : Set (RealEuclidean p))
    (phi : RealEuclidean p → RealEuclidean q) :
    maxwellFunctionGraph (U ∩ V) phi =
      maxwellFunctionGraph U phi ∩
        realEuclideanSetProduct V (Set.univ : Set (RealEuclidean q)) := by
  ext z
  have hgraph (W : Set (RealEuclidean p)) :
      z ∈ maxwellFunctionGraph W phi ↔
        realEuclideanTakeLeft z ∈ W ∧
          realEuclideanTakeRight z =
            phi (realEuclideanTakeLeft z) := by
    calc
      z ∈ maxwellFunctionGraph W phi ↔
          realEuclideanAppend (realEuclideanTakeLeft z)
              (realEuclideanTakeRight z) ∈
            maxwellFunctionGraph W phi := by
              rw [realEuclideanAppend_takeLeft_takeRight]
      _ ↔ realEuclideanTakeLeft z ∈ W ∧
          realEuclideanTakeRight z =
            phi (realEuclideanTakeLeft z) :=
        realEuclideanAppend_mem_maxwellFunctionGraph_iff
          W phi (realEuclideanTakeLeft z) (realEuclideanTakeRight z)
  rw [hgraph (U ∩ V)]
  simp only [Set.mem_inter_iff]
  rw [hgraph U]
  simp only [realEuclideanSetProduct, Set.mem_inter_iff,
    Set.mem_setOf_eq, Set.mem_univ, and_true]
  aesop

/-- A family-member function graph stays a family member after restriction
to a polynomial-sign base set. -/
theorem maxwellFunctionGraph_restrict_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {U V : Set (RealEuclidean p)}
    {phi : RealEuclidean p → RealEuclidean q}
    (hgraph : maxwellFunctionGraph U phi ∈
      charbonnelClosure S (p + q))
    (hV : V ∈ charbonnelClosure S p) :
    maxwellFunctionGraph (U ∩ V) phi ∈
      charbonnelClosure S (p + q) := by
  rw [maxwellFunctionGraph_restrict_eq_inter_product]
  have huniv : (Set.univ : Set (RealEuclidean q)) ∈
      charbonnelClosure S q :=
    hC.ws2_polynomialSign hq (polynomialSignConstructible_univ q)
  have hcylinder : realEuclideanSetProduct V
      (Set.univ : Set (RealEuclidean q)) ∈
      charbonnelClosure S (p + q) :=
    hC.ws3_prod hp hq hV huniv
  exact hC.ws1_inter (by omega) hgraph hcylinder

/-- The weak selection assembled above becomes continuous on a smaller open
ball after removing the finitely many scalar discontinuity loci. -/
theorem maxwellContinuousWeakSelection_of_weakSelection_and_discontinuityControl
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hregularity :
      CharbonnelClosureInteriorRegularity (charbonnelClosure S))
    (hdiscontinuity :
      MaxwellScalarDiscontinuityControl (charbonnelClosure S))
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p q}
    (selection : MaxwellWeakSelectionData
      (charbonnelClosure S) B R) :
    Nonempty (MaxwellContinuousWeakSelectionData
      (charbonnelClosure S) B R) := by
  cases q with
  | zero => omega
  | succ r =>
      let scalar : Fin (r + 1) →
          RealEuclidean p → RealEuclidean 1 :=
        fun j ↦ maxwellScalarCoordinateFunction selection.phi j
      have hscalarGraph : ∀ j : Fin (r + 1),
          maxwellFunctionGraph selection.U (scalar j) ∈
            charbonnelClosure S (p + 1) := by
        intro j
        exact maxwellFunctionGraph_scalarCoordinate_mem_charbonnelClosure
          hC selection.U selection.phi selection.graph_mem j
      let D : Fin (r + 1) → Set (RealEuclidean p) :=
        fun j ↦ maxwellScalarDiscontinuityLocus selection.U (scalar j)
      have hDmem : ∀ j, D j ∈ charbonnelClosure S p := by
        intro j
        exact (hdiscontinuity hp selection.U (scalar j)
          selection.U_mem (hscalarGraph j)).1
      have hDempty : ∀ j, interior (D j) = ∅ := by
        intro j
        exact (hdiscontinuity hp selection.U (scalar j)
          selection.U_mem (hscalarGraph j)).2
      let bad : Set (RealEuclidean p) := maxwellCoordinateBadSet D
      have hbadMem : bad ∈ charbonnelClosure S p :=
        charbonnelClosure_maxwellCoordinateBadSet_mem hp hC hDmem
      have hclosureDEmpty : ∀ j, interior (closure (D j)) = ∅ := by
        intro j
        exact hregularity hp (hDmem j) (hDempty j)
      have hclosureUnionEmpty :
          interior (⋃ j, closure (D j)) = ∅ :=
        interior_iUnion_fin_eq_empty_of_closed
          (fun j ↦ closure (D j))
          (fun _ ↦ isClosed_closure) hclosureDEmpty
      have hbadSubset : bad ⊆ ⋃ j, closure (D j) := by
        intro x hx
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨j, subset_closure hxj⟩
      have hbadEmpty : interior bad = ∅ :=
        interior_eq_empty_of_subset hbadSubset hclosureUnionEmpty
      have hclosureBadEmpty : interior (closure bad) = ∅ :=
        hregularity hp hbadMem hbadEmpty
      obtain ⟨x₀, ε, hε, hball⟩ :=
        exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
          selection.U_open selection.U_nonempty isClosed_closure
            hclosureBadEmpty
      let V : Set (RealEuclidean p) := Metric.ball x₀ ε
      have hVopen : IsOpen V := Metric.isOpen_ball
      have hVnonempty : V.Nonempty := ⟨x₀, Metric.mem_ball_self hε⟩
      have hVsubsetU : V ⊆ selection.U :=
        fun _ hx ↦ (hball hx).1
      have hVmem : V ∈ charbonnelClosure S p :=
        hC.ws2_polynomialSign hp
          (polynomialSignConstructible_ball x₀ hε)
      have hphiContinuous : ContinuousOn selection.phi V := by
        intro x hx
        rw [continuousWithinAt_pi]
        intro j
        have hxNotBad : x ∉ bad := by
          intro hxbad
          exact (hball hx).2 (subset_closure hxbad)
        have hxNotDj : x ∉ D j := by
          intro hxDj
          exact hxNotBad (Set.mem_iUnion_of_mem j hxDj)
        have hscalarWithin : ContinuousWithinAt (scalar j) selection.U x := by
          by_contra hnot
          exact hxNotDj ⟨hVsubsetU hx, hnot⟩
        have hcoordinateWithin :
            ContinuousWithinAt (fun y ↦ selection.phi y j)
              selection.U x := by
          exact (continuous_apply 0).continuousAt.comp_continuousWithinAt
            hscalarWithin
        exact hcoordinateWithin.mono hVsubsetU
      have hgraphV : maxwellFunctionGraph V selection.phi ∈
          charbonnelClosure S (p + (r + 1)) := by
        have hrestricted :=
          maxwellFunctionGraph_restrict_mem_charbonnelClosure
            hC hp (by omega) selection.graph_mem hVmem
        simpa only [inter_eq_right.mpr hVsubsetU] using hrestricted
      refine ⟨
        { U := V
          phi := selection.phi
          U_open := hVopen
          U_nonempty := hVnonempty
          U_subset := hVsubsetU.trans selection.U_subset
          U_mem := hVmem
          graph_mem := hgraphV
          graph_subset := ?_
          phi_continuous := hphiContinuous }⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact selection.graph_subset ⟨x, hVsubsetU hx, rfl⟩

/-- Figueiredo's Lemma 2.3.1 from its two preceding source lemmas and the
already isolated closure-interior regularity theorem. -/
theorem maxwellContinuousWeakSelection_of_sourceInputs
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hregularity :
      CharbonnelClosureInteriorRegularity (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S))
    (hdiscontinuity :
      MaxwellScalarDiscontinuityControl (charbonnelClosure S)) :
    MaxwellContinuousWeakSelection (charbonnelClosure S) := by
  intro p q hp hq B R hBopen hBnonempty hBmem hRmem hfull
  obtain ⟨selection⟩ :=
    maxwellWeakSelection_of_localConstantFiberCardinality
      hC hcard hp hq hBopen hBnonempty hBmem hRmem hfull
  exact
    maxwellContinuousWeakSelection_of_weakSelection_and_discontinuityControl
      hC hregularity hdiscontinuity hp hq selection

/-- Adapter from the maintained Maxwell closure/nullity induction package.
After that package is available, the only remaining fields for continuous
weak selection are precisely Lemmas 2.2.1 and 2.2.2. -/
theorem MaxwellClosureNullityDimensionInduction.continuousWeakSelection
    {S : EuclideanSetFamily}
    (hMaxwell : MaxwellClosureNullityDimensionInduction
      (charbonnelClosure S))
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S))
    (hdiscontinuity :
      MaxwellScalarDiscontinuityControl (charbonnelClosure S)) :
    MaxwellContinuousWeakSelection (charbonnelClosure S) :=
  maxwellContinuousWeakSelection_of_sourceInputs
    hC.toPositiveArityWeakSetStructure
    (hMaxwell.closureInteriorRegularity hC) hcard hdiscontinuity

end AbelFormalization
