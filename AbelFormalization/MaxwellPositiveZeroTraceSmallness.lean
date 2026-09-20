import AbelFormalization.MaxwellExtendedSlopeClusterMembership
import AbelFormalization.MaxwellClosureNullity
import AbelFormalization.CharbonnelApproximationTraceSmallness
import AbelFormalization.CharbonnelClosureNullityWitnesses
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Positive zero traces and finite slope bad loci

This file isolates the measure-theoretic step in Figueiredo--Maxwell
Lemmas 2.3.2 and 2.3.3.  A relation with a distinguished final parameter is
split into its positive and negative parameter parts.  Wilkie--Charbonnel
Theorem 2.2 makes the two one-sided zero traces small; their union is the
two-sided zero section as soon as the original relation has no point with
zero final parameter.

For a closed scalar zero trace, the only further source-level input is the
intermediate-value assertion used in Lemma 2.3.3: two finite values in one
fiber force the whole interval between them to occur in that fiber.  Fubini
then makes the multivalued base null.  In particular, no smallness conclusion
about the multivalued locus is included in that premise.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Reflection of the final coordinate -/

/-- Negate the final coordinate and leave every preceding coordinate fixed. -/
def maxwellLastCoordinateReflection (d : ℕ) :
    RealEuclidean (d + 1) ≃ₗ[ℝ] RealEuclidean (d + 1) where
  toFun v i := if i = Fin.last d then -v i else v i
  invFun v i := if i = Fin.last d then -v i else v i
  left_inv v := by
    funext i
    by_cases hi : i = Fin.last d <;> simp [hi]
  right_inv v := by
    funext i
    by_cases hi : i = Fin.last d <;> simp [hi]
  map_add' v w := by
    funext i
    by_cases hi : i = Fin.last d
    · subst i
      simp
      ring
    · simp [hi]
  map_smul' c v := by
    funext i
    by_cases hi : i = Fin.last d <;> simp [hi]

@[simp]
theorem maxwellLastCoordinateReflection_apply_last {d : ℕ}
    (v : RealEuclidean (d + 1)) :
    maxwellLastCoordinateReflection d v (Fin.last d) = -v (Fin.last d) := by
  simp [maxwellLastCoordinateReflection]

@[simp]
theorem maxwellLastCoordinateReflection_symm (d : ℕ) :
    (maxwellLastCoordinateReflection d).symm =
      maxwellLastCoordinateReflection d :=
  rfl

@[simp]
theorem maxwellLastCoordinateReflection_append_zero {d : ℕ}
    (x : RealEuclidean d) :
    maxwellLastCoordinateReflection d
        (charbonnelAppendLastCoordinate x 0) =
      charbonnelAppendLastCoordinate x 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
    simp [maxwellLastCoordinateReflection]

/-- The negative-parameter part of a relation. -/
def maxwellNegativeLastPart {d : ℕ}
    (A : Set (RealEuclidean (d + 1))) : Set (RealEuclidean (d + 1)) :=
  A ∩ {v | v (Fin.last d) < 0}

/-- The negative zero trace, expressed as a positive trace after reflecting
the distinguished parameter. -/
def maxwellNegativeZeroTrace {d : ℕ}
    (A : Set (RealEuclidean (d + 1))) : Set (RealEuclidean d) :=
  charbonnelPositiveZeroTrace (maxwellLastCoordinateReflection d '' A)

/-- The union of the two one-sided zero traces. -/
def maxwellTwoSidedZeroTrace {d : ℕ}
    (A : Set (RealEuclidean (d + 1))) : Set (RealEuclidean d) :=
  charbonnelPositiveZeroTrace A ∪ maxwellNegativeZeroTrace A

theorem charbonnelPositiveLastPart_reflection {d : ℕ}
    (A : Set (RealEuclidean (d + 1))) :
    charbonnelPositiveLastPart (maxwellLastCoordinateReflection d '' A) =
      maxwellLastCoordinateReflection d '' maxwellNegativeLastPart A := by
  ext z
  constructor
  · rintro ⟨⟨w, hwA, rfl⟩, hwpos⟩
    refine ⟨w, ⟨hwA, ?_⟩, rfl⟩
    simpa using hwpos
  · rintro ⟨w, ⟨hwA, hwneg⟩, rfl⟩
    exact ⟨⟨w, hwA, rfl⟩, by simpa using hwneg⟩

theorem maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart
    {d : ℕ} (A : Set (RealEuclidean (d + 1))) :
    maxwellNegativeZeroTrace A =
      charbonnelZeroSection (closure (maxwellNegativeLastPart A)) := by
  let E := maxwellLastCoordinateReflection d
  rw [maxwellNegativeZeroTrace, charbonnelPositiveZeroTrace,
    charbonnelPositiveLastPart_reflection]
  have hclosure : closure (E '' maxwellNegativeLastPart A) =
      E '' closure (maxwellNegativeLastPart A) :=
    (E.toContinuousLinearEquiv.image_closure
      (maxwellNegativeLastPart A)).symm
  rw [hclosure]
  ext x
  change charbonnelAppendLastCoordinate x 0 ∈
      E '' closure (maxwellNegativeLastPart A) ↔
    charbonnelAppendLastCoordinate x 0 ∈
      closure (maxwellNegativeLastPart A)
  constructor
  · rintro ⟨z, hz, hzEq⟩
    have hz' : z = charbonnelAppendLastCoordinate x 0 := by
      apply E.injective
      calc
        E z = charbonnelAppendLastCoordinate x 0 := hzEq
        _ = E (charbonnelAppendLastCoordinate x 0) :=
          (maxwellLastCoordinateReflection_append_zero x).symm
    rwa [hz'] at hz
  · intro hx
    exact ⟨charbonnelAppendLastCoordinate x 0, hx,
      maxwellLastCoordinateReflection_append_zero x⟩

theorem maxwellTwoSidedZeroTrace_eq_zeroSection_closure
    {d : ℕ} {A : Set (RealEuclidean (d + 1))}
    (hzero : ∀ z ∈ A, z (Fin.last d) ≠ 0) :
    maxwellTwoSidedZeroTrace A = charbonnelZeroSection (closure A) := by
  have hsplit : A =
      charbonnelPositiveLastPart A ∪ maxwellNegativeLastPart A := by
    ext z
    constructor
    · intro hz
      rcases lt_or_gt_of_ne (hzero z hz) with hzneg | hzpos
      · exact Or.inr ⟨hz, hzneg⟩
      · exact Or.inl ⟨hz, hzpos⟩
    · rintro (hz | hz) <;> exact hz.1
  have hclosure : closure A =
      closure (charbonnelPositiveLastPart A) ∪
        closure (maxwellNegativeLastPart A) := by
    calc
      closure A = closure
          (charbonnelPositiveLastPart A ∪ maxwellNegativeLastPart A) :=
        congrArg closure hsplit
      _ = closure (charbonnelPositiveLastPart A) ∪
          closure (maxwellNegativeLastPart A) := closure_union
  have hpositiveEq : charbonnelPositiveZeroTrace A =
      charbonnelZeroSection (closure (charbonnelPositiveLastPart A)) := by
    calc
      charbonnelPositiveZeroTrace A =
          charbonnelPositiveZeroTrace (charbonnelPositiveLastPart A) :=
        (charbonnelPositiveZeroTrace_positiveLastPart A).symm
      _ = charbonnelZeroSection
          (closure (charbonnelPositiveLastPart A)) :=
        charbonnelPositiveZeroTrace_eq_zeroSection_closure inter_subset_right
  calc
    maxwellTwoSidedZeroTrace A =
        charbonnelZeroSection (closure (charbonnelPositiveLastPart A)) ∪
          charbonnelZeroSection (closure (maxwellNegativeLastPart A)) := by
      rw [maxwellTwoSidedZeroTrace,
        hpositiveEq,
        maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart]
    _ = charbonnelZeroSection (closure A) := by
      rw [hclosure]
      ext x
      rfl

/-! ## The two one-sided applications of Theorem 2.2 -/

/-- The strongest smallness package supplied by the positive/negative split.
The final three fields also record the closure conclusions furnished by
Theorem 2.1. -/
structure MaxwellTwoSidedZeroTraceSmallness
    (S : EuclideanSetFamily) {d : ℕ}
    (A : Set (RealEuclidean (d + 1))) : Prop where
  positiveTrace_mem : charbonnelPositiveZeroTrace A ∈ charbonnelClosure S d
  negativeTrace_mem : maxwellNegativeZeroTrace A ∈ charbonnelClosure S d
  positiveTrace_interior_eq_empty :
    interior (charbonnelPositiveZeroTrace A) = ∅
  negativeTrace_interior_eq_empty :
    interior (maxwellNegativeZeroTrace A) = ∅
  positiveTrace_volume_eq_zero :
    (volume : Measure (RealEuclidean d)) (charbonnelPositiveZeroTrace A) = 0
  negativeTrace_volume_eq_zero :
    (volume : Measure (RealEuclidean d)) (maxwellNegativeZeroTrace A) = 0
  zeroTrace_mem :
    charbonnelZeroSection (closure A) ∈ charbonnelClosure S d
  zeroTrace_interior_eq_empty :
    interior (charbonnelZeroSection (closure A)) = ∅
  zeroTrace_volume_eq_zero :
    (volume : Measure (RealEuclidean d))
      (charbonnelZeroSection (closure A)) = 0
  zeroTrace_closure_interior_eq_empty :
    interior (closure (charbonnelZeroSection (closure A))) = ∅
  zeroTrace_closure_volume_eq_zero :
    (volume : Measure (RealEuclidean d))
      (closure (charbonnelZeroSection (closure A))) = 0

theorem maxwellTwoSidedZeroTraceSmallness_of_theorems21_22
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {d : ℕ} (hd : 0 < d) {A : Set (RealEuclidean (d + 1))}
    (hA : A ∈ charbonnelClosure S (d + 1))
    (hAempty : interior A = ∅)
    (hzero : ∀ z ∈ A, z (Fin.last d) ≠ 0) :
    MaxwellTwoSidedZeroTraceSmallness S A := by
  let E := maxwellLastCoordinateReflection d
  have hreflectMem : E '' A ∈ charbonnelClosure S (d + 1) :=
    hC.ws4_linearEquiv (by omega) hA E
  have hreflectEmpty : interior (E '' A) = ∅ := by
    calc
      interior (E '' A) = E '' interior A :=
        (E.toContinuousLinearEquiv.toHomeomorph.image_interior A).symm
      _ = E '' ∅ := congrArg (fun T : Set (RealEuclidean (d + 1)) ↦ E '' T)
        hAempty
      _ = ∅ := image_empty E
  have hpositivePartMem : charbonnelPositiveLastPart A ∈
      charbonnelClosure S (d + 1) :=
    hmem.positiveLastPart_mem hd hA
  have hpositivePartEmpty :
      interior (charbonnelPositiveLastPart A) = ∅ :=
    interior_eq_empty_of_subset inter_subset_left hAempty
  have hpositive := h22 hd hpositivePartMem inter_subset_right
  have hpositiveMem : charbonnelPositiveZeroTrace A ∈
      charbonnelClosure S d := by
    rw [← charbonnelPositiveZeroTrace_positiveLastPart]
    exact hpositive.1
  have hpositiveEmpty : interior (charbonnelPositiveZeroTrace A) = ∅ := by
    rw [← charbonnelPositiveZeroTrace_positiveLastPart]
    exact hpositive.2 hpositivePartEmpty
  have hnegativePartMem : charbonnelPositiveLastPart (E '' A) ∈
      charbonnelClosure S (d + 1) :=
    hmem.positiveLastPart_mem hd hreflectMem
  have hnegativePartEmpty :
      interior (charbonnelPositiveLastPart (E '' A)) = ∅ :=
    interior_eq_empty_of_subset inter_subset_left hreflectEmpty
  have hnegative := h22 hd hnegativePartMem inter_subset_right
  have hnegativeMem : maxwellNegativeZeroTrace A ∈
      charbonnelClosure S d := by
    rw [maxwellNegativeZeroTrace,
      ← charbonnelPositiveZeroTrace_positiveLastPart]
    exact hnegative.1
  have hnegativeEmpty : interior (maxwellNegativeZeroTrace A) = ∅ := by
    rw [maxwellNegativeZeroTrace,
      ← charbonnelPositiveZeroTrace_positiveLastPart]
    exact hnegative.2 hnegativePartEmpty
  have hpositiveNull :
      (volume : Measure (RealEuclidean d))
        (charbonnelPositiveZeroTrace A) = 0 :=
    (h21 hd hpositiveMem).1.mp hpositiveEmpty
  have hnegativeNull :
      (volume : Measure (RealEuclidean d))
        (maxwellNegativeZeroTrace A) = 0 :=
    (h21 hd hnegativeMem).1.mp hnegativeEmpty
  have htwoMem : maxwellTwoSidedZeroTrace A ∈ charbonnelClosure S d := by
    exact charbonnelClosure_union hpositiveMem hnegativeMem
  have htwoNull :
      (volume : Measure (RealEuclidean d)) (maxwellTwoSidedZeroTrace A) = 0 :=
    measure_union_null hpositiveNull hnegativeNull
  have htraceEq := maxwellTwoSidedZeroTrace_eq_zeroSection_closure hzero
  have hzeroMem : charbonnelZeroSection (closure A) ∈
      charbonnelClosure S d := by
    rwa [← htraceEq]
  have hzeroNull :
      (volume : Measure (RealEuclidean d))
        (charbonnelZeroSection (closure A)) = 0 := by
    rwa [← htraceEq]
  have hzeroEmpty : interior (charbonnelZeroSection (closure A)) = ∅ :=
    (h21 hd hzeroMem).1.mpr hzeroNull
  have hzeroClosureEmpty :
      interior (closure (charbonnelZeroSection (closure A))) = ∅ :=
    (h21 hd hzeroMem).2.1.mp hzeroNull
  have hzeroClosureNull :
      (volume : Measure (RealEuclidean d))
        (closure (charbonnelZeroSection (closure A))) = 0 :=
    (h21 hd hzeroMem).2.2.mp hzeroClosureEmpty
  exact
    { positiveTrace_mem := hpositiveMem
      negativeTrace_mem := hnegativeMem
      positiveTrace_interior_eq_empty := hpositiveEmpty
      negativeTrace_interior_eq_empty := hnegativeEmpty
      positiveTrace_volume_eq_zero := hpositiveNull
      negativeTrace_volume_eq_zero := hnegativeNull
      zeroTrace_mem := hzeroMem
      zeroTrace_interior_eq_empty := hzeroEmpty
      zeroTrace_volume_eq_zero := hzeroNull
      zeroTrace_closure_interior_eq_empty := hzeroClosureEmpty
      zeroTrace_closure_volume_eq_zero := hzeroClosureNull }

/-! ## Moving Maxwell's step coordinate to the end -/

/-- Maxwell stores quotient coordinates as `(x,epsilon,y)`.  This linear
equivalence moves them to `(x,y,epsilon)`, the convention required by the
positive-final-coordinate trace theorem. -/
def maxwellMoveStepToLastLinearEquiv (p : ℕ) :
    RealEuclidean ((p + 1) + 1) ≃ₗ[ℝ]
      RealEuclidean ((p + 1) + 1) :=
  (realEuclideanCoordinateReindex
    (charbonnelMoveLastBeforeWitnessesEquiv p 1)).symm

/-- The difference quotient after moving the step coordinate to the end. -/
def maxwellStepLastDifferenceQuotientRelation {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean ((p + 1) + 1)) :=
  maxwellMoveStepToLastLinearEquiv p ''
    maxwellDifferenceQuotientRelation U R i

@[simp]
theorem maxwellMoveStepToLastLinearEquiv_apply_append
    {p : ℕ} (x : RealEuclidean p) (epsilon y : RealEuclidean 1) :
    maxwellMoveStepToLastLinearEquiv p
        (realEuclideanAppend (realEuclideanAppend x epsilon) y) =
      realEuclideanAppend (realEuclideanAppend x y) epsilon := by
  let F := realEuclideanCoordinateReindex
    (charbonnelMoveLastBeforeWitnessesEquiv p 1)
  have hforward :
      F (realEuclideanAppend (realEuclideanAppend x y) epsilon) =
        realEuclideanAppend (realEuclideanAppend x epsilon) y :=
    realEuclideanCoordinateReindex_moveLastBeforeWitnesses x y epsilon
  change F.symm
      (realEuclideanAppend (realEuclideanAppend x epsilon) y) = _
  rw [← hforward, F.symm_apply_apply]

@[simp]
theorem maxwellMoveStepToLastLinearEquiv_symm_apply_append
    {p : ℕ} (x : RealEuclidean p) (y epsilon : RealEuclidean 1) :
    (maxwellMoveStepToLastLinearEquiv p).symm
        (realEuclideanAppend (realEuclideanAppend x y) epsilon) =
      realEuclideanAppend (realEuclideanAppend x epsilon) y := by
  exact realEuclideanCoordinateReindex_moveLastBeforeWitnesses x y epsilon

@[simp]
theorem mem_maxwellStepLastDifferenceQuotientRelation_append_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (x : RealEuclidean p) (y epsilon : RealEuclidean 1) :
    realEuclideanAppend (realEuclideanAppend x y) epsilon ∈
        maxwellStepLastDifferenceQuotientRelation U R i ↔
      realEuclideanAppend (realEuclideanAppend x epsilon) y ∈
        maxwellDifferenceQuotientRelation U R i := by
  let E := maxwellMoveStepToLastLinearEquiv p
  constructor
  · rintro ⟨w, hw, hwEq⟩
    have hwCanonical :
        w = realEuclideanAppend (realEuclideanAppend x epsilon) y := by
      apply E.injective
      exact hwEq.trans
        (maxwellMoveStepToLastLinearEquiv_apply_append x epsilon y).symm
    rwa [hwCanonical] at hw
  · intro hw
    exact ⟨realEuclideanAppend (realEuclideanAppend x epsilon) y, hw,
      maxwellMoveStepToLastLinearEquiv_apply_append x epsilon y⟩

theorem maxwellStepLastDifferenceQuotientRelation_last_ne_zero
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) {z : RealEuclidean ((p + 1) + 1)}
    (hz : z ∈ maxwellStepLastDifferenceQuotientRelation U R i) :
    z (Fin.last (p + 1)) ≠ 0 := by
  let xy : RealEuclidean (p + 1) := realEuclideanTakeLeft z
  let x : RealEuclidean p := realEuclideanTakeLeft xy
  let y : RealEuclidean 1 := realEuclideanTakeRight xy
  let epsilon : RealEuclidean 1 := realEuclideanTakeRight z
  have hxy : realEuclideanAppend x y = xy := by
    exact realEuclideanAppend_takeLeft_takeRight xy
  have hzdecomp :
      realEuclideanAppend (realEuclideanAppend x y) epsilon = z := by
    rw [hxy]
    exact realEuclideanAppend_takeLeft_takeRight z
  have hquotient :
      realEuclideanAppend (realEuclideanAppend x epsilon) y ∈
        maxwellDifferenceQuotientRelation U R i := by
    apply (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x y epsilon).mp
    rwa [hzdecomp]
  have hquotientScalar :
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon 0))
          (fun _ : Fin 1 ↦ y 0) ∈
        maxwellDifferenceQuotientRelation U R i := by
    simpa only [← realEuclidean_one_eq_const epsilon,
      ← realEuclidean_one_eq_const y] using hquotient
  have hepsilon : epsilon 0 ≠ 0 :=
    ((realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      U R i x (epsilon 0) (y 0)).mp hquotientScalar).2.2.1
  have hzlast : z (Fin.last (p + 1)) = epsilon 0 := by
    rw [← hzdecomp, realEuclideanAppend_last_one]
  rwa [hzlast]

@[simp]
theorem maxwellMoveStepToLastLinearEquiv_symm_appendLast_zero
    {p : ℕ} (v : RealEuclidean (p + 1)) :
    (maxwellMoveStepToLastLinearEquiv p).symm
        (charbonnelAppendLastCoordinate v 0) =
      maxwellInsertZeroStep v := by
  let x : RealEuclidean p := realEuclideanTakeLeft v
  let y : RealEuclidean 1 := realEuclideanTakeRight v
  have hv : realEuclideanAppend x y = v :=
    realEuclideanAppend_takeLeft_takeRight v
  change realEuclideanCoordinateReindex
      (charbonnelMoveLastBeforeWitnessesEquiv p 1)
        (charbonnelAppendLastCoordinate v 0) = maxwellInsertZeroStep v
  calc
    realEuclideanCoordinateReindex
        (charbonnelMoveLastBeforeWitnessesEquiv p 1)
          (charbonnelAppendLastCoordinate v 0) =
        realEuclideanCoordinateReindex
          (charbonnelMoveLastBeforeWitnessesEquiv p 1)
            (realEuclideanAppend (realEuclideanAppend x y)
              (0 : RealEuclidean 1)) := by rw [hv]; rfl
    _ = realEuclideanAppend
        (realEuclideanAppend x (0 : RealEuclidean 1)) y :=
      realEuclideanCoordinateReindex_moveLastBeforeWitnesses x y
        (0 : RealEuclidean 1)
    _ = maxwellInsertZeroStep v := by
      rw [← hv]
      simp [maxwellInsertZeroStep]

theorem charbonnelZeroSection_closure_stepLastDifferenceQuotientRelation
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    charbonnelZeroSection
        (closure (maxwellStepLastDifferenceQuotientRelation U R i)) =
      maxwellDifferenceQuotientZeroTrace U R i := by
  let E := maxwellMoveStepToLastLinearEquiv p
  let Q := maxwellDifferenceQuotientRelation U R i
  have hclosure :
      closure (maxwellStepLastDifferenceQuotientRelation U R i) =
        E '' closure Q := by
    exact (E.toContinuousLinearEquiv.image_closure Q).symm
  ext v
  change charbonnelAppendLastCoordinate v 0 ∈
      closure (maxwellStepLastDifferenceQuotientRelation U R i) ↔
    maxwellInsertZeroStep v ∈ closure Q
  rw [hclosure]
  constructor
  · rintro ⟨w, hw, hwEq⟩
    have hw' : w = E.symm (charbonnelAppendLastCoordinate v 0) := by
      simpa using congrArg E.symm hwEq
    rw [hw', maxwellMoveStepToLastLinearEquiv_symm_appendLast_zero] at hw
    exact hw
  · intro hv
    refine ⟨E.symm (charbonnelAppendLastCoordinate v 0), ?_,
      E.apply_symm_apply _⟩
    rwa [maxwellMoveStepToLastLinearEquiv_symm_appendLast_zero]

/-- Direct specialization of the positive/negative trace theorem to
Maxwell's directional quotient.  Its extra hypothesis is exactly the empty
interior premise to which source Lemma 2.3.2 is applied. -/
theorem maxwellDifferenceQuotientPositiveZeroTraceSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hquotientEmpty :
      interior (maxwellDifferenceQuotientRelation U R i) = ∅) :
    MaxwellTwoSidedZeroTraceSmallness S
      (maxwellStepLastDifferenceQuotientRelation U R i) := by
  let E := maxwellMoveStepToLastLinearEquiv p
  have hquotient := maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    hC i hU hR
  have hstepLastMem : maxwellStepLastDifferenceQuotientRelation U R i ∈
      charbonnelClosure S ((p + 1) + 1) :=
    hC.ws4_linearEquiv (by omega) hquotient E
  have hstepLastEmpty :
      interior (maxwellStepLastDifferenceQuotientRelation U R i) = ∅ := by
    change interior
      (E '' maxwellDifferenceQuotientRelation U R i) = ∅
    calc
      interior (E '' maxwellDifferenceQuotientRelation U R i) =
          E '' interior (maxwellDifferenceQuotientRelation U R i) :=
        (E.toContinuousLinearEquiv.toHomeomorph.image_interior
          (maxwellDifferenceQuotientRelation U R i)).symm
      _ = E '' ∅ := congrArg
        (fun T : Set (RealEuclidean ((p + 1) + 1)) ↦ E '' T)
          hquotientEmpty
      _ = ∅ := image_empty E
  exact maxwellTwoSidedZeroTraceSmallness_of_theorems21_22
    hC hmem h21 h22 (by omega) hstepLastMem hstepLastEmpty
      (fun z hz ↦
        maxwellStepLastDifferenceQuotientRelation_last_ne_zero U R i hz)

theorem maxwellDifferenceQuotientZeroTrace_volume_eq_zero
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hquotientEmpty :
      interior (maxwellDifferenceQuotientRelation U R i) = ∅) :
    (volume : Measure (RealEuclidean (p + 1)))
        (maxwellDifferenceQuotientZeroTrace U R i) = 0 := by
  have hsmall := maxwellDifferenceQuotientPositiveZeroTraceSmallness
    hC hmem h21 h22 i hU hR hquotientEmpty
  rw [← charbonnelZeroSection_closure_stepLastDifferenceQuotientRelation
    U R i]
  exact hsmall.zeroTrace_volume_eq_zero

theorem maxwellDifferenceQuotientZeroTrace_interior_eq_empty
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hquotientEmpty :
      interior (maxwellDifferenceQuotientRelation U R i) = ∅) :
    interior (maxwellDifferenceQuotientZeroTrace U R i) = ∅ := by
  have hsmall := maxwellDifferenceQuotientPositiveZeroTraceSmallness
    hC hmem h21 h22 i hU hR hquotientEmpty
  rw [← charbonnelZeroSection_closure_stepLastDifferenceQuotientRelation
    U R i]
  exact hsmall.zeroTrace_interior_eq_empty

/-- The finite zero-step clusters approached through positive steps. -/
def maxwellPositiveStepZeroTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  charbonnelPositiveZeroTrace
    (maxwellStepLastDifferenceQuotientRelation U R i)

/-- The finite zero-step clusters approached through negative steps, after
reflecting the step so that Theorem 2.2 again sees a positive parameter. -/
def maxwellNegativeStepZeroTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  maxwellNegativeZeroTrace
    (maxwellStepLastDifferenceQuotientRelation U R i)

theorem maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellPositiveStepZeroTrace U R i ∪
        maxwellNegativeStepZeroTrace U R i =
      maxwellDifferenceQuotientZeroTrace U R i := by
  change maxwellTwoSidedZeroTrace
      (maxwellStepLastDifferenceQuotientRelation U R i) =
    maxwellDifferenceQuotientZeroTrace U R i
  exact (maxwellTwoSidedZeroTrace_eq_zeroSection_closure
    (fun z hz ↦
      maxwellStepLastDifferenceQuotientRelation_last_ne_zero U R i hz)).trans
    (charbonnelZeroSection_closure_stepLastDifferenceQuotientRelation U R i)

theorem isClosed_maxwellPositiveStepZeroTrace
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : IsClosed (maxwellPositiveStepZeroTrace U R i) := by
  let A := maxwellStepLastDifferenceQuotientRelation U R i
  have hEq : charbonnelPositiveZeroTrace A =
      charbonnelZeroSection (closure (charbonnelPositiveLastPart A)) := by
    calc
      charbonnelPositiveZeroTrace A =
          charbonnelPositiveZeroTrace (charbonnelPositiveLastPart A) :=
        (charbonnelPositiveZeroTrace_positiveLastPart A).symm
      _ = charbonnelZeroSection
          (closure (charbonnelPositiveLastPart A)) :=
        charbonnelPositiveZeroTrace_eq_zeroSection_closure inter_subset_right
  change IsClosed (charbonnelPositiveZeroTrace A)
  rw [hEq]
  exact charbonnelZeroSection_isClosed isClosed_closure

theorem isClosed_maxwellNegativeStepZeroTrace
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : IsClosed (maxwellNegativeStepZeroTrace U R i) := by
  rw [maxwellNegativeStepZeroTrace,
    maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart]
  exact charbonnelZeroSection_isClosed isClosed_closure

/-! ## The finite-slope bad locus -/

/-- The genuine analytic premise from the intermediate-value part of source
Lemma 2.3.3.  It asserts interval filling inside each scalar fiber and says
nothing about measure, interior, or family membership. -/
def MaxwellFiniteSlopeIntervalFibers {p : ℕ}
    (G : MaxwellRelation p 1) : Prop :=
  ∀ (x : RealEuclidean p) (a b : ℝ), a < b →
    realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈ G →
    realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈ G →
      Set.Icc a b ⊆
        {y : ℝ | realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G}

/-- Rearrange a flat scalar relation as a subset of `base × ℝ`. -/
def maxwellScalarRelationProductEquiv (p : ℕ) :
    RealEuclidean (p + 1) ≃ᵐ (RealEuclidean p × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (p + 1) ↦ ℝ) (Fin.last p)).trans
      MeasurableEquiv.prodComm

def maxwellScalarRelationProductCoordinates {p : ℕ}
    (G : MaxwellRelation p 1) : Set (RealEuclidean p × ℝ) :=
  maxwellScalarRelationProductEquiv p '' G

@[simp]
theorem maxwellScalarRelationProductEquiv_apply_append
    {p : ℕ} (x : RealEuclidean p) (y : ℝ) :
    maxwellScalarRelationProductEquiv p
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) = (x, y) := by
  apply Prod.ext
  · funext j
    change realEuclideanAppend x (fun _ : Fin 1 ↦ y)
      ((Fin.last p).succAbove j) = x j
    rw [Fin.succAbove_last_apply]
    exact charbonnelAppendLastCoordinate_castSucc x y j
  · change realEuclideanAppend x (fun _ : Fin 1 ↦ y) (Fin.last p) = y
    exact realEuclideanAppend_last_one x (fun _ : Fin 1 ↦ y)

@[simp]
theorem mem_maxwellScalarRelationProductCoordinates_iff
    {p : ℕ} (G : MaxwellRelation p 1) (x : RealEuclidean p) (y : ℝ) :
    (x, y) ∈ maxwellScalarRelationProductCoordinates G ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G := by
  let E := maxwellScalarRelationProductEquiv p
  constructor
  · rintro ⟨z, hz, hzEq⟩
    have hzCanonical : z =
        realEuclideanAppend x (fun _ : Fin 1 ↦ y) := by
      apply E.injective
      exact hzEq.trans
        (maxwellScalarRelationProductEquiv_apply_append x y).symm
    rwa [hzCanonical] at hz
  · intro hz
    exact ⟨realEuclideanAppend x (fun _ : Fin 1 ↦ y), hz,
      maxwellScalarRelationProductEquiv_apply_append x y⟩

theorem maxwellScalarRelationProductEquiv_measurePreserving (p : ℕ) :
    MeasurePreserving (maxwellScalarRelationProductEquiv p) := by
  have hswap : MeasurePreserving
      (Prod.swap : (ℝ × RealEuclidean p) → (RealEuclidean p × ℝ)) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  exact hswap.comp
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (p + 1) ↦ ℝ) (Fin.last p))

theorem maxwellScalarRelationProductCoordinates_volume_eq_zero
    {p : ℕ} {G : MaxwellRelation p 1}
    (hG : (volume : Measure (RealEuclidean (p + 1))) G = 0) :
    (volume : Measure (RealEuclidean p × ℝ))
        (maxwellScalarRelationProductCoordinates G) = 0 := by
  let E := maxwellScalarRelationProductEquiv p
  rw [maxwellScalarRelationProductCoordinates,
    E.image_eq_preimage_symm]
  exact ((maxwellScalarRelationProductEquiv_measurePreserving p).symm E)
    |>.quasiMeasurePreserving.preimage_null hG

theorem maxwellMultivaluedLocus_volume_eq_zero_of_intervalFibers
    {p : ℕ} {G : MaxwellRelation p 1}
    (hGclosed : IsClosed G)
    (hGnull : (volume : Measure (RealEuclidean (p + 1))) G = 0)
    (hinterval : MaxwellFiniteSlopeIntervalFibers G) :
    (volume : Measure (RealEuclidean p)) (maxwellMultivaluedLocus G) = 0 := by
  let T := maxwellScalarRelationProductCoordinates G
  have hTmeasurable : MeasurableSet T := by
    exact (maxwellScalarRelationProductEquiv p).measurableEmbedding
      |>.measurableSet_image' hGclosed.measurableSet
  have hTnull : (volume : Measure (RealEuclidean p × ℝ)) T = 0 :=
    maxwellScalarRelationProductCoordinates_volume_eq_zero hGnull
  apply volume_base_eq_zero_of_prod_eq_zero_of_sections_ne_zero
    hTmeasurable (B := maxwellMultivaluedLocus G) _ hTnull
  intro x hx
  rcases hx with ⟨y₁, y₂, hy₁, hy₂, hne⟩
  change realEuclideanAppend x y₁ ∈ G at hy₁
  change realEuclideanAppend x y₂ ∈ G at hy₂
  have hy₁scalar :
      realEuclideanAppend x (fun _ : Fin 1 ↦ y₁ 0) ∈ G := by
    simpa only [← realEuclidean_one_eq_const y₁] using hy₁
  have hy₂scalar :
      realEuclideanAppend x (fun _ : Fin 1 ↦ y₂ 0) ∈ G := by
    simpa only [← realEuclidean_one_eq_const y₂] using hy₂
  have hvaluesNe : y₁ 0 ≠ y₂ 0 := by
    intro h
    apply hne
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    exact h
  have hfiber : Prod.mk x ⁻¹' T =
      {y : ℝ | realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G} := by
    ext y
    exact mem_maxwellScalarRelationProductCoordinates_iff G x y
  rcases lt_or_gt_of_ne hvaluesNe with hlt | hgt
  · have hIcc : (volume : Measure ℝ) (Set.Icc (y₁ 0) (y₂ 0)) ≠ 0 := by
      rw [Real.volume_Icc, ENNReal.ofReal_ne_zero_iff]
      exact sub_pos.mpr hlt
    intro hsection
    apply hIcc
    apply measure_mono_null (hinterval x (y₁ 0) (y₂ 0) hlt
      hy₁scalar hy₂scalar)
    rwa [← hfiber]
  · have hIcc : (volume : Measure ℝ) (Set.Icc (y₂ 0) (y₁ 0)) ≠ 0 := by
      rw [Real.volume_Icc, ENNReal.ofReal_ne_zero_iff]
      exact sub_pos.mpr hgt
    intro hsection
    apply hIcc
    apply measure_mono_null (hinterval x (y₂ 0) (y₁ 0) hgt
      hy₂scalar hy₁scalar)
    rwa [← hfiber]

/-- Family membership and every measure/interior consequence for the finite
slope multivalued locus and its closure. -/
structure MaxwellFiniteSlopeBadLocusSmallness
    (S : EuclideanSetFamily) {p : ℕ} (G : MaxwellRelation p 1) : Prop where
  badLocus_mem : maxwellMultivaluedLocus G ∈ charbonnelClosure S p
  badLocus_volume_eq_zero :
    (volume : Measure (RealEuclidean p)) (maxwellMultivaluedLocus G) = 0
  badLocus_interior_eq_empty : interior (maxwellMultivaluedLocus G) = ∅
  badLocus_closure_mem :
    closure (maxwellMultivaluedLocus G) ∈ charbonnelClosure S p
  badLocus_closure_interior_eq_empty :
    interior (closure (maxwellMultivaluedLocus G)) = ∅
  badLocus_closure_volume_eq_zero :
    (volume : Measure (RealEuclidean p))
      (closure (maxwellMultivaluedLocus G)) = 0

theorem maxwellFiniteSlopeBadLocusSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    (hGmem : G ∈ charbonnelClosure S (p + 1))
    (hGclosed : IsClosed G)
    (hGnull : (volume : Measure (RealEuclidean (p + 1))) G = 0)
    (hinterval : MaxwellFiniteSlopeIntervalFibers G) :
    MaxwellFiniteSlopeBadLocusSmallness S G := by
  have hbadMem := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC hp hGmem
  have hbadNull := maxwellMultivaluedLocus_volume_eq_zero_of_intervalFibers
    hGclosed hGnull hinterval
  have hbadEmpty := (h21 hp hbadMem).1.mpr hbadNull
  have hbadClosureMem := charbonnelClosure_topologicalClosure hbadMem
  have hbadClosureEmpty := (h21 hp hbadMem).2.1.mp hbadNull
  have hbadClosureNull := (h21 hp hbadMem).2.2.mp hbadClosureEmpty
  exact
    { badLocus_mem := hbadMem
      badLocus_volume_eq_zero := hbadNull
      badLocus_interior_eq_empty := hbadEmpty
      badLocus_closure_mem := hbadClosureMem
      badLocus_closure_interior_eq_empty := hbadClosureEmpty
      badLocus_closure_volume_eq_zero := hbadClosureNull }

/-- The two applications of Lemma 2.3.3 that are justified by continuity on
the connected positive-step domain: one for `g⁺`, and one for the reflected
`g⁻`.  Cross-side disagreement is deliberately absent from this structure;
the source treats it later, in the `U₃` part of Lemma 2.3.11. -/
structure MaxwellOneSidedFiniteSlopeBadLociSmallness
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  zeroTraceSmallness : MaxwellTwoSidedZeroTraceSmallness S
    (maxwellStepLastDifferenceQuotientRelation U R i)
  positiveBadLocus : MaxwellFiniteSlopeBadLocusSmallness S
    (maxwellPositiveStepZeroTrace U R i)
  negativeBadLocus : MaxwellFiniteSlopeBadLocusSmallness S
    (maxwellNegativeStepZeroTrace U R i)
  twoSidedTrace_eq :
    maxwellPositiveStepZeroTrace U R i ∪
        maxwellNegativeStepZeroTrace U R i =
      maxwellDifferenceQuotientZeroTrace U R i

/-- Lemma 2.3.2 followed by the finite-value part of Lemma 2.3.3, separately
on the two connected step components.  The two interval hypotheses are the
intermediate-value conclusions that continuity supplies in the source. -/
theorem maxwellOneSidedFiniteSlopeBadLociSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hquotientEmpty :
      interior (maxwellDifferenceQuotientRelation U R i) = ∅)
    (hpositiveInterval : MaxwellFiniteSlopeIntervalFibers
      (maxwellPositiveStepZeroTrace U R i))
    (hnegativeInterval : MaxwellFiniteSlopeIntervalFibers
      (maxwellNegativeStepZeroTrace U R i)) :
    MaxwellOneSidedFiniteSlopeBadLociSmallness S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  have htrace := maxwellDifferenceQuotientPositiveZeroTraceSmallness
    hC hmem h21 h22 i hU hR hquotientEmpty
  have hpositive := maxwellFiniteSlopeBadLocusSmallness hC h21 hp
    htrace.positiveTrace_mem
    (isClosed_maxwellPositiveStepZeroTrace U R i)
    htrace.positiveTrace_volume_eq_zero hpositiveInterval
  have hnegative := maxwellFiniteSlopeBadLocusSmallness hC h21 hp
    htrace.negativeTrace_mem
    (isClosed_maxwellNegativeStepZeroTrace U R i)
    htrace.negativeTrace_volume_eq_zero hnegativeInterval
  exact
    { zeroTraceSmallness := htrace
      positiveBadLocus := hpositive
      negativeBadLocus := hnegative
      twoSidedTrace_eq :=
        maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i }

/-- Lemmas 2.3.2 and 2.3.3 combined for Maxwell's finite zero-step slope
relation under an interval-filling hypothesis for the full trace.  The source
normally obtains only the two one-sided hypotheses above and treats
cross-side disagreement separately in Lemma 2.3.11. -/
theorem maxwellDifferenceQuotientFiniteSlopeBadLocusSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hquotientEmpty :
      interior (maxwellDifferenceQuotientRelation U R i) = ∅)
    (hinterval : MaxwellFiniteSlopeIntervalFibers
      (maxwellDifferenceQuotientZeroTrace U R i)) :
    MaxwellFiniteSlopeBadLocusSmallness S
      (maxwellDifferenceQuotientZeroTrace U R i) := by
  have hp : 0 < p := maxwellFinArity_pos i
  have htraceMem := maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure
    hC i hU hR
  have htraceNull := maxwellDifferenceQuotientZeroTrace_volume_eq_zero
    hC hmem h21 h22 i hU hR hquotientEmpty
  exact maxwellFiniteSlopeBadLocusSmallness hC h21 hp htraceMem
    (isClosed_maxwellDifferenceQuotientZeroTrace U R i)
    htraceNull hinterval

end AbelFormalization
