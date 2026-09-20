import AbelFormalization.MaxwellPseudofunction
import AbelFormalization.MaxwellContDiffInductionGlue

/-!
# Extended slope clusters in Maxwell's smoothness argument

Maxwell keeps the ambient weak family in ordinary real coordinates.  A slope
tending to `+∞` or `-∞` is encoded by the reciprocal tending to zero from the
corresponding side.  This file records that encoding, the first-order bad
locus, and the derivative pseudograph obtained by filling an infinite-only
fiber with the value `1`.

The definitions are the set-theoretic part of Figueiredo 2.3.8--2.3.13.  The
geometric assertions that the loci belong to the family and have empty
interior are deliberately separate.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Infinite cluster values in real coordinates -/

/-- The reciprocal relation with positive reciprocal coordinate.  Approaching
zero in its closure encodes a value tending to `+∞`. -/
def maxwellPositiveReciprocalRelation {p : ℕ}
    (G : MaxwellRelation p 1) : MaxwellRelation p 1 :=
  {w |
    let x : RealEuclidean p := realEuclideanTakeLeft w
    let r : ℝ := realEuclideanTakeRight w 0
    ∃ y : ℝ,
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G ∧
      y * r = 1 ∧ 0 < r}

/-- The reciprocal relation with negative reciprocal coordinate. -/
def maxwellNegativeReciprocalRelation {p : ℕ}
    (G : MaxwellRelation p 1) : MaxwellRelation p 1 :=
  {w |
    let x : RealEuclidean p := realEuclideanTakeLeft w
    let r : ℝ := realEuclideanTakeRight w 0
    ∃ y : ℝ,
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G ∧
      y * r = 1 ∧ r < 0}

@[simp]
theorem realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff
    {p : ℕ} (G : MaxwellRelation p 1)
    (x : RealEuclidean p) (r : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ r) ∈
        maxwellPositiveReciprocalRelation G ↔
      ∃ y : ℝ,
        realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G ∧
        y * r = 1 ∧ 0 < r := by
  simp [maxwellPositiveReciprocalRelation]

@[simp]
theorem realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff
    {p : ℕ} (G : MaxwellRelation p 1)
    (x : RealEuclidean p) (r : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ r) ∈
        maxwellNegativeReciprocalRelation G ↔
      ∃ y : ℝ,
        realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G ∧
        y * r = 1 ∧ r < 0 := by
  simp [maxwellNegativeReciprocalRelation]

/-- Base points at which `G` has the source's `+∞` cluster value. -/
def maxwellPositiveInfinityBase {p : ℕ}
    (G : MaxwellRelation p 1) : Set (RealEuclidean p) :=
  {x | realEuclideanAppend x (0 : RealEuclidean 1) ∈
    closure (maxwellPositiveReciprocalRelation G)}

/-- Base points at which `G` has the source's `-∞` cluster value. -/
def maxwellNegativeInfinityBase {p : ℕ}
    (G : MaxwellRelation p 1) : Set (RealEuclidean p) :=
  {x | realEuclideanAppend x (0 : RealEuclidean 1) ∈
    closure (maxwellNegativeReciprocalRelation G)}

@[simp]
theorem mem_maxwellPositiveInfinityBase_iff {p : ℕ}
    (G : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ maxwellPositiveInfinityBase G ↔
      realEuclideanAppend x (0 : RealEuclidean 1) ∈
        closure (maxwellPositiveReciprocalRelation G) :=
  Iff.rfl

@[simp]
theorem mem_maxwellNegativeInfinityBase_iff {p : ℕ}
    (G : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ maxwellNegativeInfinityBase G ↔
      realEuclideanAppend x (0 : RealEuclidean 1) ∈
        closure (maxwellNegativeReciprocalRelation G) :=
  Iff.rfl

/-! ## The first-order exceptional locus -/

/-- The raw bad locus for coordinate `i`: the original relation is
multivalued, the finite slope trace has an infinite value, or that finite
trace itself is multivalued. -/
def maxwellCoordinateRawBadLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  let G := maxwellDifferenceQuotientZeroTrace U R i
  maxwellMultivaluedLocus R ∪
    maxwellPositiveInfinityBase G ∪
    maxwellNegativeInfinityBase G ∪
    maxwellMultivaluedLocus G

/-- Maxwell closes each coordinate bad locus so that its complement is open. -/
def maxwellCoordinateExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  closure (maxwellCoordinateRawBadLocus U R i)

/-- The common first-order exceptional locus. -/
def maxwellFirstOrderExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  ⋃ i : Fin p, maxwellCoordinateExceptionalLocus U R i

theorem isClosed_maxwellCoordinateExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    IsClosed (maxwellCoordinateExceptionalLocus U R i) := by
  exact isClosed_closure

theorem isClosed_maxwellFirstOrderExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    IsClosed (maxwellFirstOrderExceptionalLocus U R) := by
  apply isClosed_iUnion_of_finite
  intro i
  exact isClosed_maxwellCoordinateExceptionalLocus U R i

theorem maxwellCoordinateRawBadLocus_subset_exceptional {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellCoordinateRawBadLocus U R i ⊆
      maxwellCoordinateExceptionalLocus U R i :=
  subset_closure

theorem maxwellCoordinateExceptionalLocus_subset_firstOrder {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellCoordinateExceptionalLocus U R i ⊆
      maxwellFirstOrderExceptionalLocus U R :=
  subset_iUnion (fun j : Fin p ↦
    maxwellCoordinateExceptionalLocus U R j) i

/-- Empty interior of every closed coordinate exception passes to their
finite common union. -/
theorem interior_maxwellFirstOrderExceptionalLocus_eq_empty {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (hempty : ∀ i,
      interior (maxwellCoordinateExceptionalLocus U R i) = ∅) :
    interior (maxwellFirstOrderExceptionalLocus U R) = ∅ := by
  exact interior_iUnion_fin_eq_empty_of_closed
    (fun i ↦ maxwellCoordinateExceptionalLocus U R i)
    (fun i ↦ isClosed_maxwellCoordinateExceptionalLocus U R i)
    hempty

/-! ## Totalized derivative pseudographs -/

/-- Add the dummy value `1` over a base point carrying an infinite cluster
value. -/
def maxwellInfinityFillerRelation {p : ℕ}
    (U : Set (RealEuclidean p)) (G : MaxwellRelation p 1) :
    MaxwellRelation p 1 :=
  {w |
    let x : RealEuclidean p := realEuclideanTakeLeft w
    let y : RealEuclidean 1 := realEuclideanTakeRight w
    x ∈ U ∧
      (x ∈ maxwellPositiveInfinityBase G ∨
        x ∈ maxwellNegativeInfinityBase G) ∧
      y = (1 : RealEuclidean 1)}

@[simp]
theorem realEuclideanAppend_mem_maxwellInfinityFillerRelation_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (G : MaxwellRelation p 1)
    (x : RealEuclidean p) (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈ maxwellInfinityFillerRelation U G ↔
      x ∈ U ∧
      (x ∈ maxwellPositiveInfinityBase G ∨
        x ∈ maxwellNegativeInfinityBase G) ∧
      y = (1 : RealEuclidean 1) := by
  simp [maxwellInfinityFillerRelation]

/-- Maxwell's total derivative surrogate `H_i`: the finite slope trace,
augmented by the infinity filler and restricted back over `U`. -/
def maxwellDerivativePseudograph {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  let G := maxwellDifferenceQuotientZeroTrace U R i
  maxwellRelationRestrict (G ∪ maxwellInfinityFillerRelation U G) U

@[simp]
theorem realEuclideanAppend_mem_maxwellDerivativePseudograph_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (x : RealEuclidean p) (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈ maxwellDerivativePseudograph U R i ↔
      x ∈ U ∧
        (realEuclideanAppend x y ∈
            maxwellDifferenceQuotientZeroTrace U R i ∨
          ((x ∈ maxwellPositiveInfinityBase
                (maxwellDifferenceQuotientZeroTrace U R i) ∨
            x ∈ maxwellNegativeInfinityBase
                (maxwellDifferenceQuotientZeroTrace U R i)) ∧
            y = (1 : RealEuclidean 1))) := by
  simp only [maxwellDerivativePseudograph,
    realEuclideanAppend_mem_maxwellRelationRestrict_iff, mem_union,
    realEuclideanAppend_mem_maxwellInfinityFillerRelation_iff]
  aesop

/-- Off the coordinate exceptional set the filler is impossible, so the
derivative pseudograph and the finite slope trace agree exactly. -/
theorem maxwellDerivativePseudograph_iff_zeroTrace_of_not_exceptional
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) {x : RealEuclidean p}
    (hx : x ∈ U \ maxwellCoordinateExceptionalLocus U R i)
    (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈ maxwellDerivativePseudograph U R i ↔
      realEuclideanAppend x y ∈
        maxwellDifferenceQuotientZeroTrace U R i := by
  rw [realEuclideanAppend_mem_maxwellDerivativePseudograph_iff]
  constructor
  · rintro ⟨_hxU, htrace | hinfinity⟩
    · exact htrace
    · exfalso
      apply hx.2
      apply subset_closure
      unfold maxwellCoordinateRawBadLocus
      rcases hinfinity.1 with hpos | hneg
      · aesop
      · aesop
  · intro htrace
    exact ⟨hx.1, Or.inl htrace⟩

/-- Exact representation by the finite trace transfers to the totalized
derivative graph on any set avoiding the coordinate exception. -/
theorem MaxwellRelation.RepresentsOn.derivativePseudograph
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {i : Fin p}
    {d : RealEuclidean p → RealEuclidean 1}
    (hV : V ⊆ U \ maxwellCoordinateExceptionalLocus U R i)
    (hrep : MaxwellRelation.RepresentsOn
      (maxwellDifferenceQuotientZeroTrace U R i) V d) :
    MaxwellRelation.RepresentsOn
      (maxwellDerivativePseudograph U R i) V d := by
  intro x hx y
  rw [maxwellDerivativePseudograph_iff_zeroTrace_of_not_exceptional
    U R i (hV hx) y]
  exact hrep x hx y

/-- Every multivalued fiber of the totalized derivative graph lies in the
closed coordinate exceptional locus. -/
theorem maxwellMultivaluedLocus_derivativePseudograph_subset_exceptional
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellMultivaluedLocus (maxwellDerivativePseudograph U R i) ⊆
      maxwellCoordinateExceptionalLocus U R i := by
  rintro x ⟨y₁, y₂, hy₁, hy₂, hne⟩
  change realEuclideanAppend x y₁ ∈ maxwellDerivativePseudograph U R i at hy₁
  change realEuclideanAppend x y₂ ∈ maxwellDerivativePseudograph U R i at hy₂
  rw [realEuclideanAppend_mem_maxwellDerivativePseudograph_iff] at hy₁ hy₂
  rcases hy₁.2 with hy₁G | hy₁F <;>
    rcases hy₂.2 with hy₂G | hy₂F
  · apply subset_closure
    unfold maxwellCoordinateRawBadLocus
    aesop
  · apply subset_closure
    unfold maxwellCoordinateRawBadLocus
    rcases hy₂F.1 with hpos | hneg
    · aesop
    · aesop
  · apply subset_closure
    unfold maxwellCoordinateRawBadLocus
    rcases hy₁F.1 with hpos | hneg
    · aesop
    · aesop
  · exact False.elim (hne (hy₁F.2.trans hy₂F.2.symm))

/-- The compactified-slope coverage assertion needed to make `H_i` total.
Its proof is analytic and is therefore kept visible as a separate predicate. -/
def MaxwellSlopeClusterCoverage {p : ℕ}
    (U : Set (RealEuclidean p)) (G : MaxwellRelation p 1) : Prop :=
  ∀ x ∈ U,
    (maxwellRelationFiber G x).Nonempty ∨
      x ∈ maxwellPositiveInfinityBase G ∨
      x ∈ maxwellNegativeInfinityBase G

/-- Coverage of finite or infinite slope clusters gives a full fiber for the
totalized derivative pseudograph. -/
theorem maxwellDerivativePseudograph_hasFullFibersOver
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p)
    (hcover : MaxwellSlopeClusterCoverage U
      (maxwellDifferenceQuotientZeroTrace U R i)) :
    MaxwellHasFullFibersOver U (maxwellDerivativePseudograph U R i) := by
  intro x hx
  rcases hcover x hx with ⟨y, hy⟩ | hinfinity
  · exact ⟨y,
      (realEuclideanAppend_mem_maxwellDerivativePseudograph_iff
        U R i x y).2 ⟨hx, Or.inl hy⟩⟩
  · exact ⟨(1 : RealEuclidean 1),
      (realEuclideanAppend_mem_maxwellDerivativePseudograph_iff
        U R i x (1 : RealEuclidean 1)).2
          ⟨hx, Or.inr ⟨hinfinity, rfl⟩⟩⟩

/-- If the closed coordinate exceptional set is null, the totalized
derivative graph is a Maxwell pseudofunction on `U`. -/
theorem isMaxwellPseudofunctionOn_derivativePseudograph
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p)
    (hcover : MaxwellSlopeClusterCoverage U
      (maxwellDifferenceQuotientZeroTrace U R i))
    (hnull : (volume : Measure (RealEuclidean p))
      (maxwellCoordinateExceptionalLocus U R i) = 0) :
    IsMaxwellPseudofunctionOn U (maxwellDerivativePseudograph U R i) := by
  refine ⟨?_, maxwellDerivativePseudograph_hasFullFibersOver i hcover, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hx
    exact ((realEuclideanAppend_mem_maxwellDerivativePseudograph_iff
      U R i x y).1 hy).1
  · unfold IsMaxwellPseudofunction
    exact measure_mono_null
      (maxwellMultivaluedLocus_derivativePseudograph_subset_exceptional
        U R i) hnull

end AbelFormalization
