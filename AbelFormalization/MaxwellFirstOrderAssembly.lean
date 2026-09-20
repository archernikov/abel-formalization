import AbelFormalization.MaxwellPseudofunctionChoice
import AbelFormalization.MaxwellDifferenceQuotientTraceTopology
import AbelFormalization.MaxwellExtendedSlopeClusterMembership
import AbelFormalization.MaxwellPseudofunctionInduction
import AbelFormalization.MaxwellVectorOutputReduction
import AbelFormalization.MaxwellClosureNullity

/-!
# Assembly of Maxwell's scalar first-order package

This file separates the two remaining analytic assertions in Maxwell's first-order
argument from all choice, relation, closure, and family-membership bookkeeping.
The representative is the canonical classical choice from each nonempty
fiber.  The source fills infinite slope fibers with a dummy value; here the
same value is placed over the larger common null exceptional set.  This
preserves the finite slope trace exactly on the good open set and removes a
logically unnecessary global slope-coverage premise.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Monotonicity and the canonical representative's derivative trace -/

theorem maxwellDifferenceQuotientRelation_mono {p : ℕ}
    {U : Set (RealEuclidean p)} {R T : MaxwellRelation p 1}
    (hRT : R ⊆ T) (i : Fin p) :
    maxwellDifferenceQuotientRelation U R i ⊆
      maxwellDifferenceQuotientRelation U T i := by
  intro w hw
  simp only [maxwellDifferenceQuotientRelation, Set.mem_setOf_eq] at hw ⊢
  rcases hw with
    ⟨hx, hxshift, hepsilon, z₁, z₂, hz₁, hz₂, heq⟩
  exact ⟨hx, hxshift, hepsilon, z₁, z₂,
    hRT hz₁, hRT hz₂, heq⟩

theorem maxwellDifferenceQuotientZeroTrace_mono {p : ℕ}
    {U : Set (RealEuclidean p)} {R T : MaxwellRelation p 1}
    (hRT : R ⊆ T) (i : Fin p) :
    maxwellDifferenceQuotientZeroTrace U R i ⊆
      maxwellDifferenceQuotientZeroTrace U T i := by
  intro v hv
  change maxwellInsertZeroStep v ∈
    closure (maxwellDifferenceQuotientRelation U R i) at hv
  change maxwellInsertZeroStep v ∈
    closure (maxwellDifferenceQuotientRelation U T i)
  exact closure_mono (maxwellDifferenceQuotientRelation_mono hRT i) hv

theorem IsMaxwellPseudofunctionOn.chosenScalarGraph_subset {p : ℕ}
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) :
    maxwellFunctionGraph U
        (fun x : RealEuclidean p ↦
          fun _ : Fin 1 ↦ maxwellChosenScalarValue R x) ⊆ R := by
  rintro _ ⟨x, hx, rfl⟩
  change realEuclideanAppend x
    (fun _ : Fin 1 ↦ maxwellChosenScalarValue R x) ∈ R
  rw [← maxwellChosenValue_eq_scalar R x]
  exact hR.full_fibers.maxwellChosenValue_mem hx

/-- At every differentiability point, the derivative of the canonical chosen
representative occurs in the original relation's zero-step quotient trace.
Extra values in a multivalued fiber can only enlarge that trace. -/
theorem IsMaxwellPseudofunctionOn.chosenScalar_directionalDerivative_mem_trace
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (i : Fin p) {x : RealEuclidean p} (hx : x ∈ U)
    (hdiff : DifferentiableAt ℝ (maxwellChosenScalarValue R) x) :
    realEuclideanAppend x
        (fun _ : Fin 1 ↦
          fderiv ℝ (maxwellChosenScalarValue R) x
            (Pi.single i 1 : RealEuclidean p)) ∈
      maxwellDifferenceQuotientZeroTrace U R i := by
  have hgraph :=
    maxwellDifferenceQuotientZeroTrace_functionGraph_fderiv_mem
      hU hx (maxwellChosenScalarValue R) i hdiff
  exact maxwellDifferenceQuotientZeroTrace_mono
    hR.chosenScalarGraph_subset i hgraph

/-! ## Exceptional-set totalization of the derivative trace -/

/-- The part of the coordinate bad locus not already controlled by the
input pseudofunction hypothesis.  Nullity of `maxwellMultivaluedLocus R` is
one of the fields of `IsMaxwellPseudofunctionOn U R`; only the three slope
degeneracies below remain genuinely analytic. -/
def maxwellCoordinateSlopeBadLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  let G := maxwellDifferenceQuotientZeroTrace U R i
  maxwellPositiveInfinityBase G ∪
    maxwellNegativeInfinityBase G ∪
    maxwellMultivaluedLocus G

theorem maxwellCoordinateRawBadLocus_eq_multivalued_union_slopeBad
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellCoordinateRawBadLocus U R i =
      maxwellMultivaluedLocus R ∪
        maxwellCoordinateSlopeBadLocus U R i := by
  ext x
  simp [maxwellCoordinateRawBadLocus,
    maxwellCoordinateSlopeBadLocus, or_assoc]

/-- The constant value `1` over an arbitrary exceptional base set. -/
def maxwellExceptionalFillerRelation {p : ℕ}
    (A : Set (RealEuclidean p)) : MaxwellRelation p 1 :=
  {w | realEuclideanTakeLeft w ∈ A ∧
    realEuclideanTakeRight w = (1 : RealEuclidean 1)}

@[simp]
theorem realEuclideanAppend_mem_maxwellExceptionalFillerRelation_iff
    {p : ℕ} (A : Set (RealEuclidean p))
    (x : RealEuclidean p) (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈ maxwellExceptionalFillerRelation A ↔
      x ∈ A ∧ y = (1 : RealEuclidean 1) := by
  simp [maxwellExceptionalFillerRelation]

/-- A product-and-affine-cut presentation of the exceptional filler. -/
def maxwellExceptionalFillerCarrier {p : ℕ}
    (A : Set (RealEuclidean p)) : Set (RealEuclidean (p + 1)) :=
  realEuclideanSetProduct A Set.univ ∩
    maxwellLastCoordinateOneHyperplane p

theorem maxwellExceptionalFillerCarrier_eq {p : ℕ}
    (A : Set (RealEuclidean p)) :
    maxwellExceptionalFillerCarrier A =
      maxwellExceptionalFillerRelation A := by
  ext w
  simp only [maxwellExceptionalFillerCarrier, realEuclideanSetProduct,
    Set.mem_inter_iff, Set.mem_univ, and_true,
    maxwellLastCoordinateOneHyperplane, Set.mem_setOf_eq,
    maxwellExceptionalFillerRelation]
  rw [← realEuclideanTakeRight_one_eq_iff_last_eq_one w]

theorem maxwellExceptionalFillerRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {A : Set (RealEuclidean p)}
    (hA : A ∈ charbonnelClosure S p) :
    maxwellExceptionalFillerRelation A ∈
      charbonnelClosure S (p + 1) := by
  have huniv : (Set.univ : Set (RealEuclidean 1)) ∈
      charbonnelClosure S 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ 1)
  have hproduct : realEuclideanSetProduct A Set.univ ∈
      charbonnelClosure S (p + 1) :=
    hC.ws3_prod hp (by omega) hA huniv
  have hcarrier : maxwellExceptionalFillerCarrier A ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_integerAffineInter hproduct
      (isIntegerAffineSet_maxwellLastCoordinateOneHyperplane p)
  rw [maxwellExceptionalFillerCarrier_eq A] at hcarrier
  exact hcarrier

/-- Restrict the finite slope trace to `U` and add the dummy value `1` over
the common closed exceptional set.  Differentiability supplies a finite
trace value off that set, and the filler supplies a value on it. -/
def maxwellExceptionalDerivativePseudograph {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (A : Set (RealEuclidean p)) (i : Fin p) : MaxwellRelation p 1 :=
  maxwellRelationRestrict
    (maxwellDifferenceQuotientZeroTrace U R i ∪
      maxwellExceptionalFillerRelation A) U

@[simp]
theorem realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (A : Set (RealEuclidean p)) (i : Fin p)
    (x : RealEuclidean p) (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈
        maxwellExceptionalDerivativePseudograph U R A i ↔
      x ∈ U ∧
        (realEuclideanAppend x y ∈
            maxwellDifferenceQuotientZeroTrace U R i ∨
          (x ∈ A ∧ y = (1 : RealEuclidean 1))) := by
  simp only [maxwellExceptionalDerivativePseudograph,
    realEuclideanAppend_mem_maxwellRelationRestrict_iff, Set.mem_union,
    realEuclideanAppend_mem_maxwellExceptionalFillerRelation_iff]
  aesop

theorem maxwellExceptionalDerivativePseudograph_iff_zeroTrace_of_not_exceptional
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (A : Set (RealEuclidean p)) (i : Fin p)
    {x : RealEuclidean p} (hx : x ∈ U \ A)
    (y : RealEuclidean 1) :
    realEuclideanAppend x y ∈
        maxwellExceptionalDerivativePseudograph U R A i ↔
      realEuclideanAppend x y ∈
        maxwellDifferenceQuotientZeroTrace U R i := by
  rw [realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff]
  constructor
  · rintro ⟨_hxU, htrace | ⟨hxA, _hy⟩⟩
    · exact htrace
    · exact False.elim (hx.2 hxA)
  · intro htrace
    exact ⟨hx.1, Or.inl htrace⟩

theorem maxwellExceptionalDerivativePseudograph_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {U A : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hA : A ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellExceptionalDerivativePseudograph U R A i ∈
      charbonnelClosure S (p + 1) := by
  have htrace : maxwellDifferenceQuotientZeroTrace U R i ∈
      charbonnelClosure S (p + 1) :=
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure
      hC i hU hR
  have hfiller : maxwellExceptionalFillerRelation A ∈
      charbonnelClosure S (p + 1) :=
    maxwellExceptionalFillerRelation_mem_charbonnelClosure hC hp hA
  exact maxwellRelationRestrict_mem_charbonnelClosure hC hp hU
    (charbonnelClosure_union htrace hfiller)

/-- Any multivalued fiber of the exceptional-set totalization lies in the
exceptional set, provided the finite trace is single-valued off that set. -/
theorem maxwellMultivaluedLocus_exceptionalDerivativePseudograph_subset
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (A : Set (RealEuclidean p)) (i : Fin p)
    (htrace : maxwellMultivaluedLocus
        (maxwellDifferenceQuotientZeroTrace U R i) ⊆ A) :
    maxwellMultivaluedLocus
        (maxwellExceptionalDerivativePseudograph U R A i) ⊆ A := by
  rintro x ⟨y₁, y₂, hy₁, hy₂, hne⟩
  by_contra hxA
  change realEuclideanAppend x y₁ ∈
    maxwellExceptionalDerivativePseudograph U R A i at hy₁
  change realEuclideanAppend x y₂ ∈
    maxwellExceptionalDerivativePseudograph U R A i at hy₂
  have hy₁' :=
    (realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
      U R A i x y₁).mp hy₁
  have hy₂' :=
    (realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
      U R A i x y₂).mp hy₂
  have hy₁trace : realEuclideanAppend x y₁ ∈
      maxwellDifferenceQuotientZeroTrace U R i := by
    rcases hy₁'.2 with h | h
    · exact h
    · exact False.elim (hxA h.1)
  have hy₂trace : realEuclideanAppend x y₂ ∈
      maxwellDifferenceQuotientZeroTrace U R i := by
    rcases hy₂'.2 with h | h
    · exact h
    · exact False.elim (hxA h.1)
  exact hxA (htrace ⟨y₁, y₂, hy₁trace, hy₂trace, hne⟩)

/-! ## The remaining source-level analytic core -/

/-- The exact analytic content still needed after the relation algebra and
the exceptional-set totalization have been discharged.

* every genuinely slope-theoretic coordinate bad locus is null;
* the canonical representative is differentiable away from the common
  closed exceptional locus.

The omitted part of the raw bad locus is the original relation's
multivalued locus, whose nullity is already supplied by the pseudofunction
hypothesis.  No global slope-coverage premise is required.  These are
concrete assertions about the fixed constructions above; neither is the
first-order package or an arbitrary-order smoothness conclusion. -/
structure MaxwellScalarFirstOrderAnalyticCore
    (C : EuclideanSetFamily) : Prop where
  /-- The nullity consequence of the geometric argument in Figueiredo
  Lemma 2.3.11, after removing the input multivalued locus whose nullity is
  already part of the pseudofunction hypothesis. -/
  slopeBadLocus_null : ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∀ i : Fin p,
        (volume : Measure (RealEuclidean p))
          (maxwellCoordinateSlopeBadLocus U R i) = 0
  /-- The differentiability consequence of Figueiredo Lemma 2.3.10.  The
  source proves the stronger statement that all partial derivatives exist
  and are continuous on this open complement. -/
  chosen_differentiable : ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∀ x ∈ U \ maxwellFirstOrderExceptionalLocus U R,
        DifferentiableAt ℝ (maxwellChosenScalarValue R) x

theorem pi_basisFun_eq_single {p : ℕ} (i : Fin p) :
    (Pi.basisFun ℝ (Fin p)) i =
      (Pi.single i 1 : RealEuclidean p) := by
  funext j
  simp only [Pi.basisFun_apply, Pi.single_apply]

/-- The two analytic assertions above, Wilkie 2.1, and the proved weak-family
algebra imply the exact scalar first-order package consumed by the
arbitrary-order induction. -/
theorem maxwellScalarFirstOrderPackage_of_analyticCore
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (hcore : MaxwellScalarFirstOrderAnalyticCore (charbonnelClosure S)) :
    MaxwellScalarFirstOrderPackage (charbonnelClosure S) := by
  intro p hp U R hUopen hUmem hRmem hRpseudo
  let A0 : Set (RealEuclidean p) :=
    maxwellFirstOrderExceptionalLocus U R
  let f : RealEuclidean p → ℝ := maxwellChosenScalarValue R
  let H : Fin p → MaxwellRelation p 1 :=
    fun i ↦ maxwellExceptionalDerivativePseudograph U R A0 i
  have hrawNull : ∀ i : Fin p,
      (volume : Measure (RealEuclidean p))
        (maxwellCoordinateRawBadLocus U R i) = 0 := by
    intro i
    rw [maxwellCoordinateRawBadLocus_eq_multivalued_union_slopeBad]
    exact measure_union_null hRpseudo.multivalued_null
      (hcore.slopeBadLocus_null hp U R hUopen hUmem hRmem hRpseudo i)
  have hcoordinateMem : ∀ i : Fin p,
      maxwellCoordinateExceptionalLocus U R i ∈
        charbonnelClosure S p := by
    intro i
    exact maxwellCoordinateExceptionalLocus_mem_charbonnelClosure
      hC i hUmem hRmem
  have hcoordinateEmpty : ∀ i : Fin p,
      interior (maxwellCoordinateExceptionalLocus U R i) = ∅ := by
    intro i
    have hrawMem : maxwellCoordinateRawBadLocus U R i ∈
        charbonnelClosure S p :=
      maxwellCoordinateRawBadLocus_mem_charbonnelClosure
        hC i hUmem hRmem
    have hclosureEmpty :
        interior (closure (maxwellCoordinateRawBadLocus U R i)) = ∅ :=
      (h21 hp hrawMem).2.1.mp (hrawNull i)
    exact hclosureEmpty
  have hcoordinateNull : ∀ i : Fin p,
      (volume : Measure (RealEuclidean p))
        (maxwellCoordinateExceptionalLocus U R i) = 0 := by
    intro i
    have hrawMem : maxwellCoordinateRawBadLocus U R i ∈
        charbonnelClosure S p :=
      maxwellCoordinateRawBadLocus_mem_charbonnelClosure
        hC i hUmem hRmem
    have hclosureEmpty :
        interior (closure (maxwellCoordinateRawBadLocus U R i)) = ∅ :=
      (h21 hp hrawMem).2.1.mp (hrawNull i)
    exact (h21 hp hrawMem).2.2.mp hclosureEmpty
  have hA0closed : IsClosed A0 := by
    exact isClosed_maxwellFirstOrderExceptionalLocus U R
  have hA0mem : A0 ∈ charbonnelClosure S p := by
    exact maxwellFirstOrderExceptionalLocus_mem_charbonnelClosure
      hC hp hUmem hRmem
  have hA0empty : interior A0 = ∅ := by
    exact interior_maxwellFirstOrderExceptionalLocus_eq_empty
      U R hcoordinateEmpty
  have hA0null : (volume : Measure (RealEuclidean p)) A0 = 0 := by
    dsimp only [A0]
    unfold maxwellFirstOrderExceptionalLocus
    exact measure_iUnion_null hcoordinateNull
  have hmultiSubset : maxwellMultivaluedLocus R ⊆ A0 := by
    let i0 : Fin p := ⟨0, hp⟩
    intro x hx
    apply maxwellCoordinateExceptionalLocus_subset_firstOrder U R i0
    apply subset_closure
    unfold maxwellCoordinateRawBadLocus
    aesop
  have hRrep : MaxwellRelation.RepresentsOn R (U \ A0)
      (fun x : RealEuclidean p ↦ fun _ : Fin 1 ↦ f x) := by
    exact hRpseudo.representsOn_maxwellChosenScalarValue_of_subset
      hmultiSubset
  have hfdiff : ∀ x ∈ U \ A0, DifferentiableAt ℝ f x := by
    intro x hx
    exact hcore.chosen_differentiable hp U R hUopen hUmem hRmem
      hRpseudo x hx
  refine ⟨A0, f, H, hA0closed, hA0mem, hA0empty, hRrep, hfdiff, ?_⟩
  intro i
  have hHmem : H i ∈ charbonnelClosure S (p + 1) := by
    exact maxwellExceptionalDerivativePseudograph_mem_charbonnelClosure
      hC hp i hUmem hA0mem hRmem
  have htraceMulti : maxwellMultivaluedLocus
      (maxwellDifferenceQuotientZeroTrace U R i) ⊆ A0 := by
    intro x hx
    apply maxwellCoordinateExceptionalLocus_subset_firstOrder U R i
    apply subset_closure
    unfold maxwellCoordinateRawBadLocus
    aesop
  have hHpseudo : IsMaxwellPseudofunctionOn U (H i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      exact
        ((realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
          U R A0 i x y).mp hy).1
    · intro x hx
      by_cases hxA : x ∈ A0
      · exact ⟨(1 : RealEuclidean 1),
          (realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
            U R A0 i x (1 : RealEuclidean 1)).mpr
              ⟨hx, Or.inr ⟨hxA, rfl⟩⟩⟩
      · let d : RealEuclidean 1 := fun _ : Fin 1 ↦
          fderiv ℝ f x (Pi.single i 1 : RealEuclidean p)
        have hdTrace : realEuclideanAppend x d ∈
            maxwellDifferenceQuotientZeroTrace U R i := by
          exact hRpseudo.chosenScalar_directionalDerivative_mem_trace
            hUopen i hx (hfdiff x ⟨hx, hxA⟩)
        exact ⟨d,
          (realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
            U R A0 i x d).mpr ⟨hx, Or.inl hdTrace⟩⟩
    · unfold IsMaxwellPseudofunction
      exact measure_mono_null
        (maxwellMultivaluedLocus_exceptionalDerivativePseudograph_subset
          U R A0 i htraceMulti) hA0null
  refine ⟨hHmem, hHpseudo, ?_⟩
  intro x hx y
  let d : RealEuclidean 1 := fun _ : Fin 1 ↦
    fderiv ℝ f x ((Pi.basisFun ℝ (Fin p)) i)
  have hdTrace : realEuclideanAppend x d ∈
      maxwellDifferenceQuotientZeroTrace U R i := by
    have hchosen :=
      hRpseudo.chosenScalar_directionalDerivative_mem_trace
        hUopen i hx.1 (hfdiff x hx)
    simpa only [f, d, pi_basisFun_eq_single] using hchosen
  have hdH : realEuclideanAppend x d ∈ H i := by
    exact
      (maxwellExceptionalDerivativePseudograph_iff_zeroTrace_of_not_exceptional
        U R A0 i hx d).mpr hdTrace
  constructor
  · intro hy
    by_contra hne
    have hmulti : x ∈ maxwellMultivaluedLocus (H i) :=
      ⟨y, d, hy, hdH, hne⟩
    exact hx.2
      (maxwellMultivaluedLocus_exceptionalDerivativePseudograph_subset
        U R A0 i htraceMulti hmulti)
  · intro hy
    change y = d at hy
    simpa only [hy] using hdH

/-- The same assembly, before the finite-output reduction, gives every
finite scalar differentiability order by the existing induction. -/
theorem maxwellScalarPseudofunctionOrderSmoothness_of_analyticCore
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (hcore : MaxwellScalarFirstOrderAnalyticCore (charbonnelClosure S)) :
    ∀ N : ℕ,
      MaxwellScalarPseudofunctionOrderSmoothness
        (charbonnelClosure S) N :=
  maxwellScalarPseudofunctionOrderSmoothness_of_firstOrderPackage hC
    (maxwellScalarFirstOrderPackage_of_analyticCore
      hC.toPositiveArityWeakSetStructure h21 hcore)

/-- End-to-end Maxwell 2.4 reduction: the concrete scalar analytic core gives
all finite differentiability orders and then all finite output coordinates. -/
theorem maxwellAlmostEverywhereSmoothness_of_analyticCore
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (hcore : MaxwellScalarFirstOrderAnalyticCore (charbonnelClosure S)) :
    MaxwellAlmostEverywhereSmoothness (charbonnelClosure S) :=
  maxwellAlmostEverywhereSmoothness_of_scalarPseudofunctionOrderSmoothness
    hC.toPositiveArityWeakSetStructure
    (maxwellScalarPseudofunctionOrderSmoothness_of_analyticCore
      hC h21 hcore)

end AbelFormalization
