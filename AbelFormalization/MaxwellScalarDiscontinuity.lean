import AbelFormalization.MaxwellWeakSelection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The scalar discontinuity locus in Maxwell--Figueiredo Lemma 2.2.2

This file separates the algebraic, topological, and geometric parts of
Figueiredo's Lemma 2.2.2.

For a scalar graph `G`, a failure of continuity at a point has exactly the
three alternatives used in the printed proof:

* the closed graph has two distinct finite values over the point;
* positive values escape to infinity, detected by reciprocal values tending
  to zero;
* negative values escape to infinity, detected in the same way.

The union of these three loci is constructed below using only operations
already available in the Charbonnel closure.  We prove that every point of
this closure-defined locus is a genuine discontinuity and that the locus is
a family member.  The converse inclusion is isolated as the elementary
bounded/unbounded sequence dichotomy occurring on pages 57--59 of
Figueiredo's exposition.

For the empty-interior half, the final contradiction in the source is
factored through a `MaxwellScalarUniformEscapeWitness`.  Such a witness is
impossible by a finite Archimedean iteration, proved here.  What remains of
the source's geometric argument is precisely the production of this witness
from an interior ball in the closure-defined bad locus.  This is the step
that invokes uniform fiber cardinality, nullity/interior equivalence, and the
maximum/minimum fiber construction; it is stated separately and does not
assume the desired empty-interior conclusion.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## The closure-defined bad locus -/

/-- The three closure alternatives for discontinuity of a scalar graph.

The intersection with `U` is important: closure fibers over boundary points
of `U` do not concern relative continuity on `U`. -/
def maxwellScalarClosureBadLocus {p : ℕ}
    (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1) :
    Set (RealEuclidean p) :=
  U ∩
    (maxwellMultivaluedLocus
        (closure (maxwellFunctionGraph U f)) ∪
      (maxwellPositiveInfinityBase (maxwellFunctionGraph U f) ∪
        maxwellNegativeInfinityBase (maxwellFunctionGraph U f)))

/-- The closure-defined bad locus is a Charbonnel-closure member.  This is
the entire family-membership calculation in Lemma 2.2.2(a): closure,
two-value incidence, reciprocal incidence, finite union, and intersection. -/
theorem maxwellScalarClosureBadLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hU : U ∈ charbonnelClosure S p)
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1)) :
    maxwellScalarClosureBadLocus U f ∈ charbonnelClosure S p := by
  have hclosedGraph : closure (maxwellFunctionGraph U f) ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hgraph
  have hfinite := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC hp hclosedGraph
  have hpositive := maxwellPositiveInfinityBase_mem_charbonnelClosure
    hC hp hgraph
  have hnegative := maxwellNegativeInfinityBase_mem_charbonnelClosure
    hC hp hgraph
  have hbad :
      maxwellMultivaluedLocus
          (closure (maxwellFunctionGraph U f)) ∪
        (maxwellPositiveInfinityBase (maxwellFunctionGraph U f) ∪
          maxwellNegativeInfinityBase (maxwellFunctionGraph U f)) ∈
          charbonnelClosure S p :=
    charbonnelClosure_union hfinite
      (charbonnelClosure_union hpositive hnegative)
  exact hC.ws1_inter hp hU hbad

/-! ## Continuous points have a single finite closure value -/

/-- At a point of the domain where `f` is relatively continuous, the fiber
of the closed graph contains only the actual value of `f`. -/
theorem maxwellClosureFunctionGraph_fiber_eq_of_continuousWithinAt
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p} {y : RealEuclidean 1}
    (hxU : x ∈ U) (hf : ContinuousWithinAt f U x)
    (hy : realEuclideanAppend x y ∈
      closure (maxwellFunctionGraph U f)) :
    y = f x := by
  obtain ⟨w, hwGraph, hwLimit⟩ :=
    mem_closure_iff_seq_limit.mp hy
  let xseq : ℕ → RealEuclidean p :=
    fun n ↦ realEuclideanTakeLeft (w n)
  let yseq : ℕ → RealEuclidean 1 :=
    fun n ↦ realEuclideanTakeRight (w n)
  have hwSplit : ∀ n,
      w n = realEuclideanAppend (xseq n) (yseq n) := by
    intro n
    exact (realEuclideanAppend_takeLeft_takeRight (w n)).symm
  have hxseqU : ∀ n, xseq n ∈ U := by
    intro n
    have hn := hwGraph n
    rw [hwSplit n,
      realEuclideanAppend_mem_maxwellFunctionGraph_iff] at hn
    exact hn.1
  have hyseq : ∀ n, yseq n = f (xseq n) := by
    intro n
    have hn := hwGraph n
    rw [hwSplit n,
      realEuclideanAppend_mem_maxwellFunctionGraph_iff] at hn
    exact hn.2
  have hxseqLimit : Tendsto xseq atTop (𝓝 x) := by
    have h :=
      ((realEuclideanTakeLeftContinuousLinearMap p 1).continuous.tendsto _).comp
        hwLimit
    simpa [xseq, Function.comp_def] using h
  let rightMap : RealEuclidean (p + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have hyseqLimit : Tendsto yseq atTop (𝓝 y) := by
    have h := (rightMap.continuous.tendsto _).comp hwLimit
    simpa [rightMap, yseq, Function.comp_def] using h
  have hxseqWithin : Tendsto xseq atTop (𝓝[U] x) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hxseqLimit, Eventually.of_forall hxseqU⟩
  have hfseqLimit : Tendsto (fun n ↦ f (xseq n)) atTop (𝓝 (f x)) :=
    hf.tendsto.comp hxseqWithin
  have hyseqAsFunction : yseq = fun n ↦ f (xseq n) := by
    funext n
    exact hyseq n
  rw [hyseqAsFunction] at hyseqLimit
  exact tendsto_nhds_unique hyseqLimit hfseqLimit

/-- A reciprocal relation satisfying `y*r=1` cannot accumulate at reciprocal
value zero over a relative continuity point of the original graph. -/
theorem maxwell_not_mem_zeroReciprocalClosure_of_continuousWithinAt
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {H : MaxwellRelation p 1} {x : RealEuclidean p}
    (hf : ContinuousWithinAt f U x)
    (hH : ∀ (a : RealEuclidean p) (r : ℝ),
      realEuclideanAppend a (fun _ : Fin 1 ↦ r) ∈ H →
        ∃ y : ℝ,
          realEuclideanAppend a (fun _ : Fin 1 ↦ y) ∈
              maxwellFunctionGraph U f ∧
            y * r = 1) :
    realEuclideanAppend x (0 : RealEuclidean 1) ∉ closure H := by
  intro hxClosure
  obtain ⟨w, hwH, hwLimit⟩ :=
    mem_closure_iff_seq_limit.mp hxClosure
  let xseq : ℕ → RealEuclidean p :=
    fun n ↦ realEuclideanTakeLeft (w n)
  let rseq : ℕ → ℝ :=
    fun n ↦ realEuclideanTakeRight (w n) 0
  have hwSplit : ∀ n,
      w n = realEuclideanAppend (xseq n)
        (fun _ : Fin 1 ↦ rseq n) := by
    intro n
    calc
      w n = realEuclideanAppend
          (realEuclideanTakeLeft (w n))
          (realEuclideanTakeRight (w n)) :=
        (realEuclideanAppend_takeLeft_takeRight (w n)).symm
      _ = realEuclideanAppend (xseq n)
          (fun _ : Fin 1 ↦ rseq n) := by
        congr 1
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        rfl
  have hrelation : ∀ n,
      ∃ y : ℝ,
        realEuclideanAppend (xseq n) (fun _ : Fin 1 ↦ y) ∈
            maxwellFunctionGraph U f ∧
          y * rseq n = 1 := by
    intro n
    apply hH
    rw [← hwSplit n]
    exact hwH n
  choose y hyGraph hyProduct using hrelation
  have hxseqU : ∀ n, xseq n ∈ U := by
    intro n
    exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f (xseq n) (fun _ : Fin 1 ↦ y n)).mp (hyGraph n) |>.1
  have hyValue : ∀ n, y n = f (xseq n) 0 := by
    intro n
    have hvalue := (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f (xseq n) (fun _ : Fin 1 ↦ y n)).mp (hyGraph n) |>.2
    exact congrFun hvalue 0
  have hxseqLimit : Tendsto xseq atTop (𝓝 x) := by
    have h :=
      ((realEuclideanTakeLeftContinuousLinearMap p 1).continuous.tendsto _).comp
        hwLimit
    simpa [xseq, Function.comp_def] using h
  let rightMap : RealEuclidean (p + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have hrvecLimit :
      Tendsto (fun n ↦ realEuclideanTakeRight (w n)) atTop
        (𝓝 (0 : RealEuclidean 1)) := by
    have h := (rightMap.continuous.tendsto _).comp hwLimit
    simpa [rightMap, Function.comp_def] using h
  have hrseqLimit : Tendsto rseq atTop (𝓝 0) := by
    have h := ((continuous_apply (0 : Fin 1)).tendsto _).comp hrvecLimit
    simpa [rseq, Function.comp_def] using h
  have hxseqWithin : Tendsto xseq atTop (𝓝[U] x) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hxseqLimit, Eventually.of_forall hxseqU⟩
  have hfseqLimit : Tendsto (fun n ↦ f (xseq n)) atTop (𝓝 (f x)) :=
    hf.tendsto.comp hxseqWithin
  have hscalarLimit :
      Tendsto (fun n ↦ f (xseq n) 0) atTop (𝓝 (f x 0)) :=
    ((continuous_apply (0 : Fin 1)).tendsto _).comp hfseqLimit
  have hyLimit : Tendsto y atTop (𝓝 (f x 0)) := by
    have hfun : y = fun n ↦ f (xseq n) 0 := by
      funext n
      exact hyValue n
    rw [hfun]
    exact hscalarLimit
  have hproductLimit : Tendsto (fun n ↦ y n * rseq n) atTop (𝓝 0) := by
    simpa using hyLimit.mul hrseqLimit
  have honeLimit : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
    have hfun : (fun n ↦ y n * rseq n) = fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      exact hyProduct n
    rwa [hfun] at hproductLimit
  have honeZero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds honeLimit
  norm_num at honeZero

/-- Every closure-defined bad point is a genuine relative discontinuity. -/
theorem maxwellScalarClosureBadLocus_subset_discontinuityLocus
    {p : ℕ} (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1) :
    maxwellScalarClosureBadLocus U f ⊆
      maxwellScalarDiscontinuityLocus U f := by
  rintro x ⟨hxU, hxBad⟩
  refine ⟨hxU, ?_⟩
  intro hf
  rcases hxBad with hfinite | hpositive | hnegative
  · obtain ⟨y₁, y₂, hy₁, hy₂, hyne⟩ := hfinite
    have hy₁eq :=
      maxwellClosureFunctionGraph_fiber_eq_of_continuousWithinAt
        hxU hf hy₁
    have hy₂eq :=
      maxwellClosureFunctionGraph_fiber_eq_of_continuousWithinAt
        hxU hf hy₂
    exact hyne (hy₁eq.trans hy₂eq.symm)
  · exact maxwell_not_mem_zeroReciprocalClosure_of_continuousWithinAt
      hf (fun a r har ↦ by
        obtain ⟨y, hy, hyr, _hrpos⟩ :=
          (realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff
            (maxwellFunctionGraph U f) a r).mp har
        exact ⟨y, hy, hyr⟩) hpositive
  · exact maxwell_not_mem_zeroReciprocalClosure_of_continuousWithinAt
      hf (fun a r har ↦ by
        obtain ⟨y, hy, hyr, _hrneg⟩ :=
          (realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff
            (maxwellFunctionGraph U f) a r).mp har
        exact ⟨y, hy, hyr⟩) hnegative

/-! ## The elementary bounded/unbounded sequence dichotomy -/

/-- The only topological direction not used by the family-membership
calculation: a discontinuous scalar function either has two finite closed
graph values or an infinite cluster value of one sign.

This is the exact bounded/unbounded sequence split in the first half of
Figueiredo Lemma 2.2.2.  It contains no set-family assertion. -/
def MaxwellScalarClosureSequenceDichotomy : Prop :=
  ∀ {p : ℕ} (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1)
    (x : RealEuclidean p),
      x ∈ U → ¬ ContinuousWithinAt f U x →
        x ∈ maxwellMultivaluedLocus
              (closure (maxwellFunctionGraph U f)) ∨
          x ∈ maxwellPositiveInfinityBase
              (maxwellFunctionGraph U f) ∨
          x ∈ maxwellNegativeInfinityBase
              (maxwellFunctionGraph U f)

/-! ### Discharging the sequence dichotomy in mathlib -/

/-- Coordinatewise convergence is preserved by the flat append map. -/
theorem tendsto_realEuclideanAppend
    {X : Type*} {l : Filter X} {p q : ℕ}
    {a : X → RealEuclidean p} {b : X → RealEuclidean q}
    {x : RealEuclidean p} {y : RealEuclidean q}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 y)) :
    Tendsto (fun t ↦ realEuclideanAppend (a t) (b t)) l
      (𝓝 (realEuclideanAppend x y)) := by
  rw [tendsto_pi_nhds]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [realEuclideanAppend, Function.comp_def] using
      ((continuous_apply j).tendsto _).comp ha
  · simpa [realEuclideanAppend, Function.comp_def] using
      ((continuous_apply j).tendsto _).comp hb

/-- A discontinuity of a one-coordinate Euclidean-valued function supplies
a sequence in the relative domain converging to the base point while its
unique scalar coordinate stays a fixed positive distance away. -/
theorem exists_maxwellScalarDiscontinuitySequence
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p}
    (hdiscontinuous : ¬ ContinuousWithinAt f U x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : ℕ → RealEuclidean p,
        (∀ n, a n ∈ U) ∧ Tendsto a atTop (𝓝 x) ∧
        ∀ n, ε ≤ dist (f (a n) 0) (f x 0) := by
  have hscalar :
      ¬ ContinuousWithinAt (fun z ↦ f z 0) U x := by
    intro h
    apply hdiscontinuous
    rw [continuousWithinAt_pi]
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact h
  rw [Metric.continuousWithinAt_iff] at hscalar
  push_neg at hscalar
  obtain ⟨ε, hε, hbad⟩ := hscalar
  have hexists : ∀ n : ℕ, ∃ a : RealEuclidean p,
      a ∈ U ∧
      dist a x < (1 : ℝ) / ((n : ℝ) + 1) ∧
      ε ≤ dist (f a 0) (f x 0) := by
    intro n
    have hdenom : 0 < (n : ℝ) + 1 := by positivity
    exact hbad ((1 : ℝ) / ((n : ℝ) + 1))
      (one_div_pos.mpr hdenom)
  choose a haU haClose haFar using hexists
  refine ⟨ε, hε, a, haU, ?_, haFar⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun n ↦ (haClose n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- From a real sequence unbounded above, choose values tending upward while
their indices also tend to infinity. -/
theorem exists_index_ge_natCast_lt_of_not_bddAbove_range
    (u : ℕ → ℝ) (hu : ¬ BddAbove (Set.range u)) (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧ (n : ℝ) < u k := by
  let A : ℝ := ∑ i ∈ Finset.range n, |u i|
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (u i)
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ :=
    (not_bddAbove_iff.mp hu) ((n : ℝ) + A + 1)
  refine ⟨k, ?_, by linarith⟩
  by_contra hkn
  have hklt : k < n := Nat.lt_of_not_ge hkn
  have hkMem : k ∈ Finset.range n := Finset.mem_range.mpr hklt
  have habs : |u k| ≤ A := by
    exact Finset.single_le_sum
      (fun i _ ↦ abs_nonneg (u i)) hkMem
  have hleabs : u k ≤ |u k| := le_abs_self (u k)
  linarith

/-- The lower-unbounded counterpart of
`exists_index_ge_natCast_lt_of_not_bddAbove_range`. -/
theorem exists_index_ge_lt_neg_natCast_of_not_bddBelow_range
    (u : ℕ → ℝ) (hu : ¬ BddBelow (Set.range u)) (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧ u k < -(n : ℝ) := by
  let A : ℝ := ∑ i ∈ Finset.range n, |u i|
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (u i)
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ :=
    (not_bddBelow_iff.mp hu) (-((n : ℝ) + A + 1))
  refine ⟨k, ?_, by linarith⟩
  by_contra hkn
  have hklt : k < n := Nat.lt_of_not_ge hkn
  have hkMem : k ∈ Finset.range n := Finset.mem_range.mpr hklt
  have habs : |u k| ≤ A := by
    exact Finset.single_le_sum
      (fun i _ ↦ abs_nonneg (u i)) hkMem
  have hnegabs : -|u k| ≤ u k := neg_abs_le (u k)
  linarith

/-- The bounded/unbounded split is purely metric and order theoretic; no
definability hypothesis is needed. -/
theorem maxwellScalarClosureSequenceDichotomy_mathlib :
    MaxwellScalarClosureSequenceDichotomy := by
  intro p U f x hxU hdiscontinuous
  obtain ⟨ε, hε, a, haU, haLimit, haFar⟩ :=
    exists_maxwellScalarDiscontinuitySequence hdiscontinuous
  let value : ℕ → ℝ := fun n ↦ f (a n) 0
  by_cases hbounded : Bornology.IsBounded (Set.range value)
  · obtain ⟨y, _hyClosure, φ, hφmono, hvalueLimit⟩ :=
      tendsto_subseq_of_bounded hbounded
        (fun n ↦ Set.mem_range_self n)
    have hφTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hbaseLimit : Tendsto (fun n ↦ a (φ n)) atTop (𝓝 x) :=
      haLimit.comp hφTop
    have hvectorLimit :
        Tendsto (fun n ↦ f (a (φ n))) atTop
          (𝓝 (fun _ : Fin 1 ↦ y)) := by
      rw [tendsto_pi_nhds]
      intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simpa [value, Function.comp_def] using hvalueLimit
    have hcluster :
        realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
          closure (maxwellFunctionGraph U f) := by
      apply mem_closure_iff_seq_limit.mpr
      refine ⟨fun n ↦ realEuclideanAppend (a (φ n)) (f (a (φ n))), ?_, ?_⟩
      · intro n
        exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
          U f (a (φ n)) (f (a (φ n)))).mpr
            ⟨haU (φ n), rfl⟩
      · exact tendsto_realEuclideanAppend hbaseLimit hvectorLimit
    have hactual : realEuclideanAppend x (f x) ∈
        closure (maxwellFunctionGraph U f) :=
      subset_closure
        ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
          U f x (f x)).mpr ⟨hxU, rfl⟩)
    have hdistLimit :
        Tendsto (fun n ↦ dist (value (φ n)) (f x 0)) atTop
          (𝓝 (dist y (f x 0))) :=
      hvalueLimit.dist tendsto_const_nhds
    have hεdist : ε ≤ dist y (f x 0) :=
      ge_of_tendsto' hdistLimit (fun n ↦ by
        simpa [value] using haFar (φ n))
    have hyneScalar : y ≠ f x 0 :=
      (dist_pos.mp (hε.trans_le hεdist))
    have hyneVector : (fun _ : Fin 1 ↦ y) ≠ f x := by
      intro h
      apply hyneScalar
      exact congrFun h 0
    exact Or.inl ⟨(fun _ : Fin 1 ↦ y), f x,
      hcluster, hactual, hyneVector⟩
  · by_cases hbelow : BddBelow (Set.range value)
    · have habove : ¬ BddAbove (Set.range value) := by
        intro habove
        exact hbounded
          (isBounded_iff_bddBelow_bddAbove.mpr ⟨hbelow, habove⟩)
      have hextract : ∀ n : ℕ, ∃ k : ℕ,
          n ≤ k ∧ (n : ℝ) < value k :=
        fun n ↦ exists_index_ge_natCast_lt_of_not_bddAbove_range
          value habove n
      choose φ hφge hφlarge using hextract
      have hφTop : Tendsto φ atTop atTop := by
        rw [tendsto_atTop]
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hφge n)
      have hbaseLimit : Tendsto (fun n ↦ a (φ n)) atTop (𝓝 x) :=
        haLimit.comp hφTop
      have hvalueTop : Tendsto (fun n ↦ value (φ n)) atTop atTop :=
        tendsto_atTop_mono (fun n ↦ (hφlarge n).le)
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have hinvLimit :
          Tendsto (fun n ↦ (value (φ n))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hvalueTop
      have hinvVectorLimit :
          Tendsto (fun n ↦ fun _ : Fin 1 ↦ (value (φ n))⁻¹)
            atTop (𝓝 (0 : RealEuclidean 1)) := by
        rw [tendsto_pi_nhds]
        intro i
        simpa using hinvLimit
      apply Or.inr
      apply Or.inl
      apply mem_closure_iff_seq_limit.mpr
      refine ⟨fun n ↦ realEuclideanAppend (a (φ n))
        (fun _ : Fin 1 ↦ (value (φ n))⁻¹), ?_, ?_⟩
      · intro n
        apply (realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff
          (maxwellFunctionGraph U f) (a (φ n))
            ((value (φ n))⁻¹)).mpr
        have hpos : 0 < value (φ n) :=
          lt_of_le_of_lt (Nat.cast_nonneg n) (hφlarge n)
        have hconst : (fun _ : Fin 1 ↦ value (φ n)) = f (a (φ n)) := by
          funext i
          have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
          subst i
          rfl
        exact ⟨value (φ n),
          (realEuclideanAppend_mem_maxwellFunctionGraph_iff
            U f (a (φ n)) (fun _ : Fin 1 ↦ value (φ n))).mpr
              ⟨haU (φ n), hconst⟩,
          mul_inv_cancel₀ (ne_of_gt hpos), inv_pos.mpr hpos⟩
      · exact tendsto_realEuclideanAppend hbaseLimit hinvVectorLimit
    · have hextract : ∀ n : ℕ, ∃ k : ℕ,
          n ≤ k ∧ value k < -(n : ℝ) :=
        fun n ↦ exists_index_ge_lt_neg_natCast_of_not_bddBelow_range
          value hbelow n
      choose φ hφge hφsmall using hextract
      have hφTop : Tendsto φ atTop atTop := by
        rw [tendsto_atTop]
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hφge n)
      have hbaseLimit : Tendsto (fun n ↦ a (φ n)) atTop (𝓝 x) :=
        haLimit.comp hφTop
      have hnegNat :
          Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have hvalueBot : Tendsto (fun n ↦ value (φ n)) atTop atBot :=
        tendsto_atBot_mono (fun n ↦ (hφsmall n).le) hnegNat
      have hinvLimit :
          Tendsto (fun n ↦ (value (φ n))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atBot_zero.comp hvalueBot
      have hinvVectorLimit :
          Tendsto (fun n ↦ fun _ : Fin 1 ↦ (value (φ n))⁻¹)
            atTop (𝓝 (0 : RealEuclidean 1)) := by
        rw [tendsto_pi_nhds]
        intro i
        simpa using hinvLimit
      apply Or.inr
      apply Or.inr
      apply mem_closure_iff_seq_limit.mpr
      refine ⟨fun n ↦ realEuclideanAppend (a (φ n))
        (fun _ : Fin 1 ↦ (value (φ n))⁻¹), ?_, ?_⟩
      · intro n
        apply (realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff
          (maxwellFunctionGraph U f) (a (φ n))
            ((value (φ n))⁻¹)).mpr
        have hneg : value (φ n) < 0 :=
          lt_of_lt_of_le (hφsmall n) (neg_nonpos.mpr (Nat.cast_nonneg n))
        have hconst : (fun _ : Fin 1 ↦ value (φ n)) = f (a (φ n)) := by
          funext i
          have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
          subst i
          rfl
        exact ⟨value (φ n),
          (realEuclideanAppend_mem_maxwellFunctionGraph_iff
            U f (a (φ n)) (fun _ : Fin 1 ↦ value (φ n))).mpr
              ⟨haU (φ n), hconst⟩,
          mul_inv_cancel₀ (ne_of_lt hneg), inv_lt_zero.mpr hneg⟩
      · exact tendsto_realEuclideanAppend hbaseLimit hinvVectorLimit

/-- Under the sequence dichotomy, the actual discontinuity locus is exactly
the closure-defined family member. -/
theorem maxwellScalarDiscontinuityLocus_eq_closureBadLocus
    (htopology : MaxwellScalarClosureSequenceDichotomy)
    {p : ℕ} (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1) :
    maxwellScalarDiscontinuityLocus U f =
      maxwellScalarClosureBadLocus U f := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxU, hxdiscontinuous⟩
    exact ⟨hxU, htopology U f x hxU hxdiscontinuous⟩
  · exact maxwellScalarClosureBadLocus_subset_discontinuityLocus U f

/-! ## The final Archimedean contradiction -/

/-- Data produced in the last part of the source proof after shrinking the
interior ball: `f` is bounded there, yet every value can be increased (or
decreased) by one fixed positive amount while remaining in the same set. -/
structure MaxwellScalarUniformEscapeWitness {p : ℕ}
    (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1) where
  B : Set (RealEuclidean p)
  B_nonempty : B.Nonempty
  B_subset : B ⊆ U
  M : ℝ
  bounded : ∀ x ∈ B, |f x 0| ≤ M
  delta : ℝ
  delta_pos : 0 < delta
  escape :
    (∀ x ∈ B, ∃ u ∈ B, f x 0 + delta ≤ f u 0) ∨
    (∀ x ∈ B, ∃ u ∈ B, f u 0 + delta ≤ f x 0)

/-- A bounded real-valued function cannot have a uniform upward escape on
a nonempty set. -/
theorem not_exists_maxwellScalarUniformUpwardEscape
    {p : ℕ} {B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hB : B.Nonempty) (M : ℝ)
    (hbounded : ∀ x ∈ B, |f x 0| ≤ M)
    {δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ x ∈ B, ∃ u ∈ B, f x 0 + δ ≤ f u 0) :
    False := by
  obtain ⟨x₀, hx₀B⟩ := hB
  have hiterate : ∀ n : ℕ, ∃ x ∈ B,
      f x₀ 0 + (n : ℝ) * δ ≤ f x 0 := by
    intro n
    induction n with
    | zero =>
        exact ⟨x₀, hx₀B, by simp⟩
    | succ n ih =>
        obtain ⟨x, hxB, hx⟩ := ih
        obtain ⟨u, huB, hu⟩ := hstep x hxB
        refine ⟨u, huB, ?_⟩
        calc
          f x₀ 0 + ((n + 1 : ℕ) : ℝ) * δ =
              (f x₀ 0 + (n : ℝ) * δ) + δ := by
                push_cast
                ring
          _ ≤ f u 0 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / δ)
  have hnδ : 2 * M < (n : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hn
  obtain ⟨x, hxB, hx⟩ := hiterate n
  have hx₀bounds := abs_le.mp (hbounded x₀ hx₀B)
  have hxbounds := abs_le.mp (hbounded x hxB)
  linarith

/-- The downward version of the same finite iteration. -/
theorem not_exists_maxwellScalarUniformDownwardEscape
    {p : ℕ} {B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hB : B.Nonempty) (M : ℝ)
    (hbounded : ∀ x ∈ B, |f x 0| ≤ M)
    {δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ x ∈ B, ∃ u ∈ B, f u 0 + δ ≤ f x 0) :
    False := by
  obtain ⟨x₀, hx₀B⟩ := hB
  have hiterate : ∀ n : ℕ, ∃ x ∈ B,
      f x 0 + (n : ℝ) * δ ≤ f x₀ 0 := by
    intro n
    induction n with
    | zero =>
        exact ⟨x₀, hx₀B, by simp⟩
    | succ n ih =>
        obtain ⟨x, hxB, hx⟩ := ih
        obtain ⟨u, huB, hu⟩ := hstep x hxB
        refine ⟨u, huB, ?_⟩
        calc
          f u 0 + ((n + 1 : ℕ) : ℝ) * δ =
              (f u 0 + δ) + (n : ℝ) * δ := by
                push_cast
                ring
          _ ≤ f x₀ 0 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / δ)
  have hnδ : 2 * M < (n : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hn
  obtain ⟨x, hxB, hx⟩ := hiterate n
  have hx₀bounds := abs_le.mp (hbounded x₀ hx₀B)
  have hxbounds := abs_le.mp (hbounded x hxB)
  linarith

/-- The final escape witness of the printed proof is contradictory, without
any additional definability or topology hypothesis. -/
theorem MaxwellScalarUniformEscapeWitness.false
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (h : MaxwellScalarUniformEscapeWitness U f) : False := by
  rcases h.escape with hup | hdown
  · exact not_exists_maxwellScalarUniformUpwardEscape
      h.B_nonempty h.M h.bounded h.delta_pos hup
  · exact not_exists_maxwellScalarUniformDownwardEscape
      h.B_nonempty h.M h.bounded h.delta_pos hdown

/-! ## The exact remaining geometric selection step -/

/-- The source-shaped remainder of Lemma 2.2.2(b).

Starting with an interior ball in the closure-defined bad locus, the source
uses bounded-value exhaustion, Lemma 2.2.1's constant fiber cardinality,
the maximum/minimum fiber formula, and another countable exhaustion to
produce a uniform escape witness.  The target below is that witness, rather
than the desired empty-interior statement. -/
def MaxwellScalarClosureBadLocusEscapeSelection
    (C : EuclideanSetFamily) : Prop :=
  ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p))
      (f : RealEuclidean p → RealEuclidean 1),
      U ∈ C p → maxwellFunctionGraph U f ∈ C (p + 1) →
      (interior (maxwellScalarClosureBadLocus U f)).Nonempty →
        Nonempty (MaxwellScalarUniformEscapeWitness U f)

/-- Escape selection immediately forces the closure-defined bad locus to
have empty interior. -/
theorem maxwellScalarClosureBadLocus_interior_eq_empty
    {C : EuclideanSetFamily}
    (hselection : MaxwellScalarClosureBadLocusEscapeSelection C)
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hU : U ∈ C p)
    (hgraph : maxwellFunctionGraph U f ∈ C (p + 1)) :
    interior (maxwellScalarClosureBadLocus U f) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hinterior
  obtain ⟨witness⟩ := hselection hp U f hU hgraph hinterior
  exact witness.false

/-! ## Assembly of Lemma 2.2.2 -/

/-- Family membership and empty interior of every scalar discontinuity
locus, from the two exact remaining source steps.  All closure syntax and the
final Archimedean contradiction are discharged above. -/
theorem maxwellScalarDiscontinuityControl_of_sequenceDichotomy_and_escapeSelection
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (htopology : MaxwellScalarClosureSequenceDichotomy)
    (hselection : MaxwellScalarClosureBadLocusEscapeSelection
      (charbonnelClosure S)) :
    MaxwellScalarDiscontinuityControl (charbonnelClosure S) := by
  intro p hp U f hU hgraph
  have heq := maxwellScalarDiscontinuityLocus_eq_closureBadLocus
    htopology U f
  constructor
  · rw [heq]
    exact maxwellScalarClosureBadLocus_mem_charbonnelClosure
      hC hp hU hgraph
  · rw [heq]
    exact maxwellScalarClosureBadLocus_interior_eq_empty
      hselection hp hU hgraph

/-- The metric bounded/unbounded sequence split has no additional
hypotheses, so the geometric escape-selection step is the only remaining
input to scalar discontinuity control. -/
theorem maxwellScalarDiscontinuityControl_of_escapeSelection
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hselection : MaxwellScalarClosureBadLocusEscapeSelection
      (charbonnelClosure S)) :
    MaxwellScalarDiscontinuityControl (charbonnelClosure S) :=
  maxwellScalarDiscontinuityControl_of_sequenceDichotomy_and_escapeSelection
    hC maxwellScalarClosureSequenceDichotomy_mathlib hselection

end AbelFormalization
