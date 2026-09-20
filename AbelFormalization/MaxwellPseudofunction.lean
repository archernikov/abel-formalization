import AbelFormalization.MaxwellAlmostEverywhereSmoothness
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Maxwell pseudofunctions and directional difference quotients

This file records the relation-level syntax used in the Maxwell smoothness
argument.  A relation from `RealEuclidean p` to `RealEuclidean q` is stored in
the project's flat coordinates `RealEuclidean (p + q)`.  It is a
pseudofunction on `U` when its domain is exactly `U` and the set of base
points carrying two distinct values is Lebesgue null.

For a scalar relation, the directional difference quotient retains the step
coordinate: its coordinates are `(x, epsilon, y)`, and its defining equation
is `epsilon * y = z₂ - z₁`.  The zero-step relation is taken only after
closing this quotient relation.  These are definitions and elementary exact
identities; family membership, closedness, and derivative containment for the
resulting zero traces are exposed as separate predicates and certificates.
The later totalization argument that produces pseudofunctions is not asserted
here.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- A relation from `RealEuclidean p` to `RealEuclidean q`, represented in
the project's flat `(p + q)`-coordinate convention. -/
abbrev MaxwellRelation (p q : ℕ) :=
  Set (RealEuclidean (p + q))

/-- The proposition that `y` is related to `x`. -/
def maxwellRelates {p q : ℕ} (R : MaxwellRelation p q)
    (x : RealEuclidean p) (y : RealEuclidean q) : Prop :=
  realEuclideanAppend x y ∈ R

@[simp]
theorem maxwellRelates_iff {p q : ℕ} (R : MaxwellRelation p q)
    (x : RealEuclidean p) (y : RealEuclidean q) :
    maxwellRelates R x y ↔ realEuclideanAppend x y ∈ R :=
  Iff.rfl

/-- The full vertical fiber of a relation over one base point. -/
def maxwellRelationFiber {p q : ℕ} (R : MaxwellRelation p q)
    (x : RealEuclidean p) : Set (RealEuclidean q) :=
  {y | maxwellRelates R x y}

@[simp]
theorem mem_maxwellRelationFiber_iff {p q : ℕ}
    (R : MaxwellRelation p q) (x : RealEuclidean p)
    (y : RealEuclidean q) :
    y ∈ maxwellRelationFiber R x ↔ realEuclideanAppend x y ∈ R :=
  Iff.rfl

/-- The set of base points whose vertical fiber is nonempty. -/
def maxwellRelationDomain {p q : ℕ}
    (R : MaxwellRelation p q) : Set (RealEuclidean p) :=
  {x | (maxwellRelationFiber R x).Nonempty}

@[simp]
theorem mem_maxwellRelationDomain_iff {p q : ℕ}
    (R : MaxwellRelation p q) (x : RealEuclidean p) :
    x ∈ maxwellRelationDomain R ↔
      ∃ y : RealEuclidean q, realEuclideanAppend x y ∈ R :=
  Iff.rfl

/-- The relation has a full (that is, nonempty) fiber over every point of
`U`.  This is the full-fiber premise in the source selection theorem. -/
def MaxwellHasFullFibersOver {p q : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p q) : Prop :=
  ∀ x ∈ U, (maxwellRelationFiber R x).Nonempty

theorem maxwellHasFullFibersOver_iff_subset_domain {p q : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p q) :
    MaxwellHasFullFibersOver U R ↔ U ⊆ maxwellRelationDomain R :=
  Iff.rfl

/-- The relation domain is exactly the project's existential projection onto
the initial coordinate block. -/
theorem maxwellRelationDomain_eq_existentialProjection {p q : ℕ}
    (R : MaxwellRelation p q) :
    maxwellRelationDomain R = realEuclideanExistentialProjection R :=
  rfl

/-- Restrict a relation to a set of base points while retaining all values
over those points. -/
def maxwellRelationRestrict {p q : ℕ} (R : MaxwellRelation p q)
    (V : Set (RealEuclidean p)) : MaxwellRelation p q :=
  {z | z ∈ R ∧ realEuclideanTakeLeft z ∈ V}

@[simp]
theorem realEuclideanAppend_mem_maxwellRelationRestrict_iff
    {p q : ℕ} (R : MaxwellRelation p q)
    (V : Set (RealEuclidean p)) (x : RealEuclidean p)
    (y : RealEuclidean q) :
    realEuclideanAppend x y ∈ maxwellRelationRestrict R V ↔
      realEuclideanAppend x y ∈ R ∧ x ∈ V := by
  simp [maxwellRelationRestrict]

/-- Restricting an already restricted relation intersects the two base
domains. -/
theorem maxwellRelationRestrict_restrict {p q : ℕ}
    (R : MaxwellRelation p q) (V W : Set (RealEuclidean p)) :
    maxwellRelationRestrict (maxwellRelationRestrict R V) W =
      maxwellRelationRestrict R (V ∩ W) := by
  ext z
  simp [maxwellRelationRestrict, and_assoc, and_left_comm]

/-- Base points at which a relation has at least two distinct values. -/
def maxwellMultivaluedLocus {p q : ℕ}
    (R : MaxwellRelation p q) : Set (RealEuclidean p) :=
  {x | ∃ y₁ y₂ : RealEuclidean q,
    maxwellRelates R x y₁ ∧ maxwellRelates R x y₂ ∧ y₁ ≠ y₂}

@[simp]
theorem mem_maxwellMultivaluedLocus_iff {p q : ℕ}
    (R : MaxwellRelation p q) (x : RealEuclidean p) :
    x ∈ maxwellMultivaluedLocus R ↔
      ∃ y₁ y₂ : RealEuclidean q,
        realEuclideanAppend x y₁ ∈ R ∧
        realEuclideanAppend x y₂ ∈ R ∧ y₁ ≠ y₂ :=
  Iff.rfl

theorem maxwellMultivaluedLocus_subset_domain {p q : ℕ}
    (R : MaxwellRelation p q) :
    maxwellMultivaluedLocus R ⊆ maxwellRelationDomain R := by
  rintro x ⟨y₁, y₂, hy₁, _hy₂, _hne⟩
  exact ⟨y₁, hy₁⟩

/-- The measure-theoretic single-valuedness clause for a relation: its
multivalued locus is Lebesgue null.  The source notion of a pseudofunction on
a specified domain also requires the two domain conditions bundled below. -/
def IsMaxwellPseudofunction {p q : ℕ}
    (R : MaxwellRelation p q) : Prop :=
  (volume : Measure (RealEuclidean p)) (maxwellMultivaluedLocus R) = 0

/-- Containment of the relation over `U`, written both as a domain inclusion
and directly in flat coordinates. -/
theorem maxwellRelationDomain_subset_iff {p q : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p q) :
    maxwellRelationDomain R ⊆ U ↔
      ∀ x : RealEuclidean p, ∀ y : RealEuclidean q,
        realEuclideanAppend x y ∈ R → x ∈ U := by
  constructor
  · intro h x y hxy
    exact h ⟨y, hxy⟩
  · intro h x hx
    obtain ⟨y, hy⟩ := hx
    exact h x y hy

/-- Maxwell's source notion of a pseudofunction on `U`: the relation lies
over `U`, has a nonempty fiber at every point of `U`, and has a Lebesgue-null
multivalued locus. -/
structure IsMaxwellPseudofunctionOn {p q : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p q) : Prop where
  domain_subset : maxwellRelationDomain R ⊆ U
  full_fibers : MaxwellHasFullFibersOver U R
  multivalued_null : IsMaxwellPseudofunction R

/-- The two domain clauses in `IsMaxwellPseudofunctionOn` say exactly that
the relation domain is `U`. -/
theorem isMaxwellPseudofunctionOn_iff_domain_eq {p q : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p q) :
    IsMaxwellPseudofunctionOn U R ↔
      maxwellRelationDomain R = U ∧ IsMaxwellPseudofunction R := by
  constructor
  · intro h
    exact ⟨Set.Subset.antisymm h.domain_subset
      ((maxwellHasFullFibersOver_iff_subset_domain U R).mp h.full_fibers),
      h.multivalued_null⟩
  · rintro ⟨hdomain, hnull⟩
    refine ⟨?_, ?_, hnull⟩
    · intro x hx
      rw [hdomain] at hx
      exact hx
    · rw [maxwellHasFullFibersOver_iff_subset_domain, hdomain]

/-! ## Ordinary graphs -/

@[simp]
theorem realEuclideanAppend_mem_maxwellFunctionGraph_iff
    {p q : ℕ} (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q)
    (x : RealEuclidean p) (y : RealEuclidean q) :
    realEuclideanAppend x y ∈ maxwellFunctionGraph U Phi ↔
      x ∈ U ∧ y = Phi x := by
  constructor
  · rintro ⟨x', hx', hxy⟩
    have hxx' : x = x' := by
      simpa only [realEuclideanTakeLeft_append] using
        congrArg (fun w : RealEuclidean (p + q) ↦
          realEuclideanTakeLeft w) hxy
    have hyy' : y = Phi x' := by
      simpa only [realEuclideanTakeRight_append] using
        congrArg (fun w : RealEuclidean (p + q) ↦
          realEuclideanTakeRight w) hxy
    subst x'
    exact ⟨hx', hyy'⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩

namespace MaxwellRelation

/-- A relation represents the function `Phi` on `V` when every fiber over
`V` consists exactly of the prescribed value.  In particular, this packages
both existence and uniqueness on the restricted domain. -/
def RepresentsOn {p q : ℕ} (R : MaxwellRelation p q)
    (V : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) : Prop :=
  ∀ x ∈ V, ∀ y : RealEuclidean q,
    realEuclideanAppend x y ∈ R ↔ y = Phi x

/-- Restricting the base set preserves exact representation. -/
theorem RepresentsOn.mono {p q : ℕ} {R : MaxwellRelation p q}
    {V W : Set (RealEuclidean p)}
    {Phi : RealEuclidean p → RealEuclidean q}
    (h : RepresentsOn R V Phi) (hWV : W ⊆ V) :
    RepresentsOn R W Phi := by
  intro x hx y
  exact h x (hWV hx) y

/-- Exact representation supplies a nonempty fiber at every represented
base point. -/
theorem RepresentsOn.hasFullFibersOver
    {p q : ℕ} {R : MaxwellRelation p q}
    {V : Set (RealEuclidean p)}
    {Phi : RealEuclidean p → RealEuclidean q}
    (h : RepresentsOn R V Phi) :
    MaxwellHasFullFibersOver V R := by
  intro x hx
  exact ⟨Phi x, (h x hx (Phi x)).mpr rfl⟩

/-- An ordinary graph represents its defining function on its domain. -/
theorem representsOn_functionGraph {p q : ℕ}
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    RepresentsOn (maxwellFunctionGraph U Phi) U Phi := by
  intro x hx y
  simpa only [realEuclideanAppend_mem_maxwellFunctionGraph_iff,
    hx, true_and]

end MaxwellRelation

@[simp]
theorem maxwellRelationDomain_functionGraph {p q : ℕ}
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    maxwellRelationDomain (maxwellFunctionGraph U Phi) = U := by
  rw [maxwellRelationDomain_eq_existentialProjection,
    realEuclideanExistentialProjection_maxwellFunctionGraph]

@[simp]
theorem maxwellMultivaluedLocus_functionGraph {p q : ℕ}
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    maxwellMultivaluedLocus (maxwellFunctionGraph U Phi) = ∅ := by
  ext x
  simp only [mem_maxwellMultivaluedLocus_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨y₁, y₂, hy₁, hy₂, hne⟩
  have hy₁' :=
    (realEuclideanAppend_mem_maxwellFunctionGraph_iff U Phi x y₁).mp hy₁
  have hy₂' :=
    (realEuclideanAppend_mem_maxwellFunctionGraph_iff U Phi x y₂).mp hy₂
  exact hne (hy₁'.2.trans hy₂'.2.symm)

/-- Every ordinary function graph satisfies the null-multivaluedness clause. -/
theorem isMaxwellPseudofunction_functionGraph {p q : ℕ}
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    IsMaxwellPseudofunction (maxwellFunctionGraph U Phi) := by
  rw [IsMaxwellPseudofunction,
    maxwellMultivaluedLocus_functionGraph, measure_empty]

/-- Every ordinary function graph is a pseudofunction on its stated domain. -/
theorem isMaxwellPseudofunctionOn_functionGraph {p q : ℕ}
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    IsMaxwellPseudofunctionOn U (maxwellFunctionGraph U Phi) := by
  refine ⟨?_, ?_, isMaxwellPseudofunction_functionGraph U Phi⟩
  · rw [maxwellRelationDomain_functionGraph]
  · rw [maxwellHasFullFibersOver_iff_subset_domain,
      maxwellRelationDomain_functionGraph]

/-! ## Scalar directional difference quotients -/

/-- The source-shaped scalar difference-quotient relation in direction `i`.
Its flat coordinates are `((x, epsilon), y)`.  Keeping `epsilon` is essential:
the directional derivative relation is obtained from the zero-step trace of
the closure, rather than by existentially projecting the step away. -/
def maxwellDifferenceQuotientRelation {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation (p + 1) 1 :=
  {w |
    let xepsilon : RealEuclidean (p + 1) := realEuclideanTakeLeft w
    let x : RealEuclidean p := realEuclideanTakeLeft xepsilon
    let epsilon : ℝ := realEuclideanTakeRight xepsilon 0
    let y : ℝ := realEuclideanTakeRight w 0
    x ∈ U ∧
      x + epsilon • (Pi.single i 1 : RealEuclidean p) ∈ U ∧
      epsilon ≠ 0 ∧
      ∃ z₁ z₂ : ℝ,
        realEuclideanAppend x (fun _ : Fin 1 ↦ z₁) ∈ R ∧
        realEuclideanAppend
            (x + epsilon • (Pi.single i 1 : RealEuclidean p))
            (fun _ : Fin 1 ↦ z₂) ∈ R ∧
        epsilon * y = z₂ - z₁}

@[simp]
theorem realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
    {p : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (i : Fin p)
    (x : RealEuclidean p) (epsilon y : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
        (fun _ : Fin 1 ↦ y) ∈
      maxwellDifferenceQuotientRelation U R i ↔
    x ∈ U ∧
      x + epsilon • (Pi.single i 1 : RealEuclidean p) ∈ U ∧
      epsilon ≠ 0 ∧
      ∃ z₁ z₂ : ℝ,
        realEuclideanAppend x (fun _ : Fin 1 ↦ z₁) ∈ R ∧
        realEuclideanAppend
            (x + epsilon • (Pi.single i 1 : RealEuclidean p))
            (fun _ : Fin 1 ↦ z₂) ∈ R ∧
        epsilon * y = z₂ - z₁ := by
  simp [maxwellDifferenceQuotientRelation]

/-- For an ordinary scalar graph, the relation definition reduces exactly to
the usual directional difference-quotient equation. -/
theorem realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_functionGraph_iff
    {p : ℕ} (U : Set (RealEuclidean p))
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (x : RealEuclidean p) (epsilon y : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
        (fun _ : Fin 1 ↦ y) ∈
      maxwellDifferenceQuotientRelation U
        (maxwellFunctionGraph U (fun u _ ↦ f u)) i ↔
    x ∈ U ∧
      x + epsilon • (Pi.single i 1 : RealEuclidean p) ∈ U ∧
      epsilon ≠ 0 ∧
      epsilon * y =
        f (x + epsilon • (Pi.single i 1 : RealEuclidean p)) - f x := by
  rw [realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff]
  constructor
  · rintro ⟨hx, hxepsilon, hepsilon, z₁, z₂, hz₁, hz₂, heq⟩
    have hz₁' :=
      (realEuclideanAppend_mem_maxwellFunctionGraph_iff
        U (fun u _ ↦ f u) x (fun _ : Fin 1 ↦ z₁)).mp hz₁
    have hz₂' :=
      (realEuclideanAppend_mem_maxwellFunctionGraph_iff
        U (fun u _ ↦ f u)
          (x + epsilon • (Pi.single i 1 : RealEuclidean p))
          (fun _ : Fin 1 ↦ z₂)).mp hz₂
    have hz₁eq : z₁ = f x := congrFun hz₁'.2 0
    have hz₂eq :
        z₂ = f (x + epsilon • (Pi.single i 1 : RealEuclidean p)) :=
      congrFun hz₂'.2 0
    rw [hz₁eq, hz₂eq] at heq
    exact ⟨hx, hxepsilon, hepsilon, heq⟩
  · rintro ⟨hx, hxepsilon, hepsilon, heq⟩
    refine ⟨hx, hxepsilon, hepsilon, f x,
      f (x + epsilon • (Pi.single i 1 : RealEuclidean p)), ?_, ?_, heq⟩
    · exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
        U (fun u _ ↦ f u) x (fun _ : Fin 1 ↦ f x)).mpr ⟨hx, rfl⟩
    · exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
        U (fun u _ ↦ f u)
          (x + epsilon • (Pi.single i 1 : RealEuclidean p))
          (fun _ : Fin 1 ↦
            f (x + epsilon • (Pi.single i 1 : RealEuclidean p)))).mpr
          ⟨hxepsilon, rfl⟩

/-- Insert a zero step into a scalar graph coordinate. -/
def maxwellInsertZeroStep {p : ℕ}
    (v : RealEuclidean (p + 1)) : RealEuclidean ((p + 1) + 1) :=
  realEuclideanAppend
    (realEuclideanAppend (realEuclideanTakeLeft v)
      (0 : RealEuclidean 1))
    (realEuclideanTakeRight v)

@[simp]
theorem maxwellInsertZeroStep_append {p : ℕ}
    (x : RealEuclidean p) (y : RealEuclidean 1) :
    maxwellInsertZeroStep (realEuclideanAppend x y) =
      realEuclideanAppend (realEuclideanAppend x (0 : RealEuclidean 1)) y := by
  simp [maxwellInsertZeroStep]

/-- The zero-step trace of the closure of the directional quotient relation.
This is the relation denoted `G_i` in the source argument. -/
def maxwellDifferenceQuotientZeroTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  maxwellInsertZeroStep ⁻¹'
    closure (maxwellDifferenceQuotientRelation U R i)

@[simp]
theorem realEuclideanAppend_mem_maxwellDifferenceQuotientZeroTrace_iff
    {p : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (i : Fin p)
    (x : RealEuclidean p) (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈
        maxwellDifferenceQuotientZeroTrace U R i ↔
      realEuclideanAppend
          (realEuclideanAppend x (0 : RealEuclidean 1)) y ∈
        closure (maxwellDifferenceQuotientRelation U R i) := by
  simp [maxwellDifferenceQuotientZeroTrace]

@[simp]
theorem realEuclideanAppend_scalar_mem_maxwellDifferenceQuotientZeroTrace_iff
    {p : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (i : Fin p)
    (x : RealEuclidean p) (y : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellDifferenceQuotientZeroTrace U R i ↔
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
          (fun _ : Fin 1 ↦ y) ∈
        closure (maxwellDifferenceQuotientRelation U R i) := by
  change
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellDifferenceQuotientZeroTrace U R i ↔
      realEuclideanAppend
          (realEuclideanAppend x (0 : RealEuclidean 1))
          (fun _ : Fin 1 ↦ y) ∈
        closure (maxwellDifferenceQuotientRelation U R i)
  exact realEuclideanAppend_mem_maxwellDifferenceQuotientZeroTrace_iff
    U R i x (fun _ : Fin 1 ↦ y)

/-- The domain of `G_i` is exactly the set of base points having a value in
the zero-step slice of the closed quotient relation. -/
theorem maxwellRelationDomain_differenceQuotientZeroTrace
    {p : ℕ} (U : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (i : Fin p) :
    maxwellRelationDomain (maxwellDifferenceQuotientZeroTrace U R i) =
      {x | ∃ y : RealEuclidean 1,
        realEuclideanAppend
            (realEuclideanAppend x (0 : RealEuclidean 1)) y ∈
          closure (maxwellDifferenceQuotientRelation U R i)} := by
  ext x
  simp only [mem_maxwellRelationDomain_iff, Set.mem_setOf_eq]
  exact exists_congr (fun y ↦
    realEuclideanAppend_mem_maxwellDifferenceQuotientZeroTrace_iff
      U R i x y)

/-- Membership and closedness output for the quotient relation and its
zero-step trace.  These are geometric/family claims in the source lemma, so
they are kept as an explicit certificate rather than asserted here. -/
structure MaxwellDifferenceQuotientTraceCertificate
    (C : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  quotient_mem :
    maxwellDifferenceQuotientRelation U R i ∈ C ((p + 1) + 1)
  trace_mem : maxwellDifferenceQuotientZeroTrace U R i ∈ C (p + 1)
  trace_closed : IsClosed (maxwellDifferenceQuotientZeroTrace U R i)

/-- The analytic containment conclusion used with the zero-step trace: at a
point where a represented scalar function is differentiable, its directional
derivative occurs in the trace.  Proving this from representation and the
quotient construction is kept separate from the syntax module. -/
def MaxwellDifferenceQuotientTraceContainsDirectionalDerivative
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (f : RealEuclidean p → ℝ) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ f x →
    realEuclideanAppend x
        (fun _ : Fin 1 ↦
          fderiv ℝ f x (Pi.single i 1 : RealEuclidean p)) ∈
      maxwellDifferenceQuotientZeroTrace U R i

end AbelFormalization
