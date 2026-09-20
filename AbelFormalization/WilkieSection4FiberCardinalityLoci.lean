import AbelFormalization.MaxwellLocalFiberCardinality

/-!
# Wilkie Section 4 scalar-fibre cardinality loci

On page 418 of Wilkie's cell-decomposition argument, for a scalar relation
`A ⊆ C × ℝ` and `i ≥ 1`, the set `A_i` consists of the base points which
contain `i` strictly increasing points in the fibre of `A`.  This file records
that definition literally in the project's flat Euclidean coordinates.

The ordered incidence and its Charbonnel-closure membership were already
constructed for Maxwell weak selection.  We prove that the source-facing
definition is exactly that existing cardinality locus, and obtain:

* the semantic extended-cardinality characterization;
* nesting `A_j ⊆ A_i` for `i ≤ j`;
* the exact-cardinality identity `A_i \ A_(i+1)`; and
* membership of every `A_i` in the Charbonnel closure, without using
  complement closure.

A bare weak family is not assumed closed under existential projection, so
the final membership theorem is stated for its Charbonnel closure, precisely
as in Wilkie's application.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Wilkie's `A_i`: base points in `C` admitting `i` strictly increasing
scalar points in the fibre of `A`.  Defining the zero locus as well is useful:
the unique empty tuple makes `A_0 = C`. -/
def wilkieSection4FiberCardinalityLocus {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) (i : ℕ) :
    Set (RealEuclidean p) :=
  {x | x ∈ C ∧
    ∃ values : Fin i → ℝ, StrictMono values ∧
      ∀ j : Fin i,
        realEuclideanAppend x (fun _ : Fin 1 ↦ values j) ∈ A}

@[simp]
theorem mem_wilkieSection4FiberCardinalityLocus_iff
    {p i : ℕ} (C : Set (RealEuclidean p))
    (A : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ wilkieSection4FiberCardinalityLocus C A i ↔
      x ∈ C ∧
        ∃ values : Fin i → ℝ, StrictMono values ∧
          ∀ j : Fin i,
            realEuclideanAppend x (fun _ : Fin 1 ↦ values j) ∈ A :=
  Iff.rfl

@[simp]
theorem wilkieSection4FiberCardinalityLocus_zero
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    wilkieSection4FiberCardinalityLocus C A 0 = C := by
  ext x
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    refine ⟨hx, ![], ?_, ?_⟩
    · intro a
      exact Fin.elim0 a
    · intro j
      exact Fin.elim0 j

/-- The literal ordered-tuple formula agrees with the cardinality locus
already used in the Maxwell--Figueiredo weak-selection development. -/
theorem wilkieSection4FiberCardinalityLocus_eq_maxwell
    {p i : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    wilkieSection4FiberCardinalityLocus C A i =
      maxwellScalarFiberCardinalityAtLeast C A i := by
  cases i with
  | zero =>
      exact wilkieSection4FiberCardinalityLocus_zero C A
  | succ k =>
      ext x
      rw [mem_wilkieSection4FiberCardinalityLocus_iff,
        mem_maxwellScalarFiberCardinalityAtLeast_succ_iff]
      constructor
      · rintro ⟨hxC, values, hmono, hvalues⟩
        refine ⟨hxC, values 0, values, rfl,
          Fin.strictMono_iff_lt_succ.mp hmono, ?_⟩
        intro j
        exact hvalues j
      · rintro ⟨hxC, y, values, hzero, hstep, hvalues⟩
        refine ⟨hxC, values,
          Fin.strictMono_iff_lt_succ.mpr hstep, ?_⟩
        intro j
        exact hvalues j

/-- For a positive index, Wilkie's locus is visibly an existential
projection of the ordered scalar-selection graph. -/
theorem wilkieSection4FiberCardinalityLocus_succ_eq_projection
    {p k : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    wilkieSection4FiberCardinalityLocus C A (k + 1) =
      realEuclideanExistentialProjection
        (maxwellOrderedScalarSelectionGraph C A k) := by
  rw [wilkieSection4FiberCardinalityLocus_eq_maxwell,
    maxwellScalarFiberCardinalityAtLeast_succ_eq_projection]

/-- Semantic form: `x ∈ A_i` iff `x ∈ C` and the scalar fibre of `A`
has at least `i` elements. -/
theorem mem_wilkieSection4FiberCardinalityLocus_iff_encard
    {p i : ℕ} (C : Set (RealEuclidean p))
    (A : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ wilkieSection4FiberCardinalityLocus C A i ↔
      x ∈ C ∧ (i : ℕ∞) ≤ (maxwellScalarFiber A x).encard := by
  rw [wilkieSection4FiberCardinalityLocus_eq_maxwell,
    mem_maxwellScalarFiberCardinalityAtLeast_iff_encard]

/-- Wilkie's loci are decreasing in their cardinality index. -/
theorem wilkieSection4FiberCardinalityLocus_antitone
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    Antitone (wilkieSection4FiberCardinalityLocus C A) := by
  intro i j hij x hx
  rw [mem_wilkieSection4FiberCardinalityLocus_iff_encard] at hx ⊢
  exact ⟨hx.1, (ENat.natCast_le_natCast.mpr hij).trans hx.2⟩

/-- In particular, requiring one more ordered fibre point gives a subset. -/
theorem wilkieSection4FiberCardinalityLocus_succ_subset
    {p i : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    wilkieSection4FiberCardinalityLocus C A (i + 1) ⊆
      wilkieSection4FiberCardinalityLocus C A i :=
  wilkieSection4FiberCardinalityLocus_antitone C A (Nat.le_succ i)

/-- Membership in `A_i` but not `A_(i+1)` is exactly finite fibre
cardinality `i`. -/
theorem mem_wilkieSection4FiberCardinalityLocus_and_not_succ_iff
    {p i : ℕ} (C : Set (RealEuclidean p))
    (A : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ wilkieSection4FiberCardinalityLocus C A i ∧
        x ∉ wilkieSection4FiberCardinalityLocus C A (i + 1) ↔
      x ∈ C ∧ (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = i := by
  rw [mem_wilkieSection4FiberCardinalityLocus_iff_encard]
  constructor
  · rintro ⟨⟨hxC, hlower⟩, hnotNext⟩
    have hnotSucc :
        ¬ (i + 1 : ℕ∞) ≤ (maxwellScalarFiber A x).encard := by
      intro hsucc
      apply hnotNext
      exact
        (mem_wilkieSection4FiberCardinalityLocus_iff_encard C A x).mpr
          ⟨hxC, hsucc⟩
    have hupper : (maxwellScalarFiber A x).encard ≤ (i : ℕ∞) := by
      by_contra hnotUpper
      have hlt : (i : ℕ∞) < (maxwellScalarFiber A x).encard :=
        lt_of_not_ge hnotUpper
      apply hnotSucc
      rw [ENat.natCast_add_one_le_iff]
      exact hlt
    have hcard : (maxwellScalarFiber A x).encard = (i : ℕ∞) :=
      le_antisymm hupper hlower
    have hfinite : (maxwellScalarFiber A x).Finite :=
      Set.finite_of_encard_eq_coe hcard
    refine ⟨hxC, hfinite, ?_⟩
    apply ENat.natCast_inj.mp
    rw [hfinite.cast_ncard_eq]
    exact hcard
  · rintro ⟨hxC, hfinite, hcard⟩
    have hencard :
        (maxwellScalarFiber A x).encard = (i : ℕ∞) := by
      rw [← hfinite.cast_ncard_eq, hcard]
    constructor
    · exact ⟨hxC, hencard.ge⟩
    · intro hnext
      have hsucc :=
        (mem_wilkieSection4FiberCardinalityLocus_iff_encard C A x).mp
          hnext |>.2
      rw [hencard] at hsucc
      have : i + 1 ≤ i := ENat.natCast_le_natCast.mp hsucc
      omega

/-- Set form of the exact-cardinality stratum used after choosing a maximal
nonempty locus in Wilkie's Section 4 argument. -/
theorem wilkieSection4FiberCardinalityLocus_diff_succ
    {p i : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1) :
    wilkieSection4FiberCardinalityLocus C A i \
        wilkieSection4FiberCardinalityLocus C A (i + 1) =
      {x | x ∈ C ∧ (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = i} := by
  ext x
  exact mem_wilkieSection4FiberCardinalityLocus_and_not_succ_iff C A x

/-- Every Wilkie Section 4 cardinality locus belongs to the Charbonnel
closure when the base `C` and relation `A` do.  The proof uses the existing
ordered incidence, finite intersections, polynomial strict-order
constraints, and existential projection; no complement is used. -/
theorem wilkieSection4FiberCardinalityLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hweak : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p i : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hC : C ∈ charbonnelClosure S p)
    (hA : A ∈ charbonnelClosure S (p + 1)) :
    wilkieSection4FiberCardinalityLocus C A i ∈
      charbonnelClosure S p := by
  rw [wilkieSection4FiberCardinalityLocus_eq_maxwell]
  exact maxwellScalarFiberCardinalityAtLeast_mem_charbonnelClosure
    hweak hp hC hA

/-- The closures `closure A_i` used immediately after the cardinality loci
on Wilkie's page 418 also remain in the Charbonnel closure. -/
theorem closure_wilkieSection4FiberCardinalityLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hweak : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p i : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hC : C ∈ charbonnelClosure S p)
    (hA : A ∈ charbonnelClosure S (p + 1)) :
    closure (wilkieSection4FiberCardinalityLocus C A i) ∈
      charbonnelClosure S p :=
  charbonnelClosure_topologicalClosure
    (wilkieSection4FiberCardinalityLocus_mem_charbonnelClosure
      hweak hp hC hA)

end AbelFormalization
