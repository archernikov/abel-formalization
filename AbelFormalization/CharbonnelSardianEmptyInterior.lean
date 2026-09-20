import AbelFormalization.CharbonnelSardianConstituents
import AbelFormalization.LowerDimensionalImageAvoidance
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Empty interior of Sardian constituent families

This file proves the codimension-one nullity step used for the finite
Sardian families in the Wilkie--Karpinski--Macintyre complement argument.
For a constituent with hidden arity `q`, its carrier is contained in the
range of

`z ↦ (takeLeft z, (equation i z)ᵢ) : ℝ^(n+q) → ℝ^(n+q+1)`.

If the constituent equations are at least once continuously
differentiable, this graph map is differentiable.  Mathlib's Hausdorff
measure version of the low-to-high-dimensional Sard lemma then makes its
range null for the target-dimensional Hausdorff measure.  Subsets and
finite unions remain null, and a null set for this measure has empty
interior.

This is an analytic smallness statement only.  It does not assert
complement closure or definability of a complement.
-/

noncomputable section

open Set Function MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelSardianConstituent

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n q : ℕ}

/-- The codimension-one graph whose range contains a Sardian constituent.
The first `n` output coordinates retain the visible variables; the final
`q + 1` coordinates are the constituent equations. -/
def graphMap
    (constituent : CharbonnelSardianConstituent G order n q) :
    RealEuclidean (n + q) → RealEuclidean (n + (q + 1)) :=
  fun z ↦ realEuclideanAppend (realEuclideanTakeLeft z)
    (fun i ↦ constituent.equation i z)

@[simp]
theorem graphMap_castAdd
    (constituent : CharbonnelSardianConstituent G order n q)
    (z : RealEuclidean (n + q)) (i : Fin n) :
    constituent.graphMap z (Fin.castAdd (q + 1) i) =
      z (Fin.castAdd q i) := by
  simp [graphMap, realEuclideanTakeLeft]

@[simp]
theorem graphMap_natAdd
    (constituent : CharbonnelSardianConstituent G order n q)
    (z : RealEuclidean (n + q)) (i : Fin (q + 1)) :
    constituent.graphMap z (Fin.natAdd n i) =
      constituent.equation i z := by
  simp [graphMap]

/-- Componentwise `C^order` regularity of the equations gives the same
regularity for the graph map. -/
theorem graphMap_contDiff
    (constituent : CharbonnelSardianConstituent G order n q) :
    ContDiff ℝ order constituent.graphMap := by
  rw [contDiff_pi]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)
  · simpa only [graphMap_castAdd] using
      (contDiff_apply ℝ ℝ (Fin.castAdd q i) :
        ContDiff ℝ order
          (fun z : RealEuclidean (n + q) ↦ z (Fin.castAdd q i)))
  · simpa only [graphMap_natAdd] using constituent.equation_contDiff i

/-- Only one derivative is needed for the Hausdorff-measure argument. -/
theorem graphMap_differentiable
    (constituent : CharbonnelSardianConstituent G order n q)
    (horder : order ≠ 0) :
    Differentiable ℝ constituent.graphMap :=
  constituent.graphMap_contDiff.differentiable (by simpa using horder)

/-- The input graph has exactly one fewer real coordinate than its target. -/
theorem graphMap_finrank_lt
    (_constituent : CharbonnelSardianConstituent G order n q) :
    Module.finrank ℝ (RealEuclidean (n + q)) <
      Module.finrank ℝ (RealEuclidean (n + (q + 1))) := by
  simp only [Module.finrank_fin_fun]
  omega

/-- Every point of the constituent is attained by its graph map.  Parameter
positivity is irrelevant for this containment. -/
theorem carrier_subset_range_graphMap
    (constituent : CharbonnelSardianConstituent G order n q) :
    constituent.carrier ⊆ Set.range constituent.graphMap := by
  intro v hv
  rcases (constituent.mem_carrier_iff).mp hv with ⟨⟨y, hy⟩, _hpositive⟩
  refine ⟨realEuclideanAppend (realEuclideanTakeLeft v) y, ?_⟩
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [graphMap, realEuclideanTakeLeft]
  · simpa [graphMap, realEuclideanTakeRight] using hy j

/-- The graph range is null for Hausdorff measure in the dimension of its
codomain.  This is the measure-theoretic low-to-high-dimensional Sard step
available in mathlib. -/
theorem graphMap_range_hausdorffMeasure_eq_zero
    (constituent : CharbonnelSardianConstituent G order n q)
    (horder : order ≠ 0) :
    (μH[Module.finrank ℝ (RealEuclidean (n + (q + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (q + 1))))
      (Set.range constituent.graphMap) = 0 := by
  simpa only [image_univ] using
    (hausdorffMeasure_image_eq_zero_of_finrank_lt
      (f := constituent.graphMap) (s := Set.univ)
      (constituent.graphMap_differentiable horder).differentiableOn
      constituent.graphMap_finrank_lt)

/-- A Sardian constituent itself is null for target-dimensional Hausdorff
measure. -/
theorem carrier_hausdorffMeasure_eq_zero
    (constituent : CharbonnelSardianConstituent G order n q)
    (horder : order ≠ 0) :
    (μH[Module.finrank ℝ (RealEuclidean (n + (q + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (q + 1))))
      constituent.carrier = 0 :=
  measure_mono_null constituent.carrier_subset_range_graphMap
    (constituent.graphMap_range_hausdorffMeasure_eq_zero horder)

/-- Consequently every once-differentiable Sardian constituent has empty
interior. -/
theorem carrier_interior_eq_empty
    (constituent : CharbonnelSardianConstituent G order n q)
    (horder : order ≠ 0) :
    interior constituent.carrier = ∅ :=
  (μH[Module.finrank ℝ (RealEuclidean (n + (q + 1)))] :
      MeasureTheory.Measure (RealEuclidean (n + (q + 1)))).interior_eq_empty_of_null
    (constituent.carrier_hausdorffMeasure_eq_zero horder)

end CharbonnelSardianConstituent

namespace CharbonnelSardianSet

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n q : ℕ}

/-- A finite union of same-depth Sardian constituents is still null for the
target-dimensional Hausdorff measure. -/
theorem carrier_hausdorffMeasure_eq_zero
    (s : CharbonnelSardianSet G order n q)
    (horder : order ≠ 0) :
    (μH[Module.finrank ℝ (RealEuclidean (n + (q + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (q + 1))))
      s.carrier = 0 := by
  let constituents := s.constituents
  change
    (μH[Module.finrank ℝ (RealEuclidean (n + (q + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (q + 1))))
      {v | ∃ constituent ∈ constituents, v ∈ constituent.carrier} = 0
  induction constituents with
  | nil => simp
  | cons constituent constituents ih =>
      have hcarrier :
          {v | ∃ piece ∈ constituent :: constituents,
              v ∈ piece.carrier} =
            constituent.carrier ∪
              {v | ∃ piece ∈ constituents, v ∈ piece.carrier} := by
        ext v
        simp
      rw [hcarrier]
      exact measure_union_null
        (constituent.carrier_hausdorffMeasure_eq_zero horder) ih

/-- The source's finite-family empty-interior conclusion. -/
theorem carrier_interior_eq_empty
    (s : CharbonnelSardianSet G order n q)
    (horder : order ≠ 0) :
    interior s.carrier = ∅ :=
  (μH[Module.finrank ℝ (RealEuclidean (n + (q + 1)))] :
      MeasureTheory.Measure (RealEuclidean (n + (q + 1)))).interior_eq_empty_of_null
    (s.carrier_hausdorffMeasure_eq_zero horder)

end CharbonnelSardianSet

namespace CharbonnelPaddedSardianConstituent

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Recover the original visible and hidden variables from the first
`n + hiddenArity` coordinates of a common-depth graph input. -/
def graphInput
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    RealEuclidean (n + K) →
      RealEuclidean (n + piece.hiddenArity) :=
  fun z ↦ realEuclideanAppend (realEuclideanTakeLeft z)
    (fun j ↦ realEuclideanTakeRight z
      (Fin.castLE piece.hiddenArity_le j))

@[simp]
theorem graphInput_castAdd
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (z : RealEuclidean (n + K)) (i : Fin n) :
    piece.graphInput z (Fin.castAdd piece.hiddenArity i) =
      z (Fin.castAdd K i) := by
  simp [graphInput, realEuclideanTakeLeft]

@[simp]
theorem graphInput_natAdd
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (z : RealEuclidean (n + K)) (j : Fin piece.hiddenArity) :
    piece.graphInput z (Fin.natAdd n j) =
      realEuclideanTakeRight z (Fin.castLE piece.hiddenArity_le j) := by
  simp [graphInput]

theorem graphInput_contDiff
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    ContDiff ℝ order piece.graphInput := by
  rw [contDiff_pi]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_)
  · simpa only [graphInput_castAdd] using
      (contDiff_apply ℝ ℝ (Fin.castAdd K i) :
        ContDiff ℝ order
          (fun z : RealEuclidean (n + K) ↦ z (Fin.castAdd K i)))
  · simpa only [graphInput_natAdd, realEuclideanTakeRight] using
      (contDiff_apply ℝ ℝ
        (Fin.natAdd n (Fin.castLE piece.hiddenArity_le j)) :
        ContDiff ℝ order
          (fun z : RealEuclidean (n + K) ↦
            z (Fin.natAdd n (Fin.castLE piece.hiddenArity_le j))))

/-- An output parameter strictly after the original `q + 1` equation
parameters is supplied by input coordinate `i - 1` in the common hidden
block. -/
def trailingInputIndex
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (i : Fin (K + 1))
    (hi : piece.hiddenArity + 1 ≤ i.val) : Fin K :=
  ⟨i.val - 1, by
    have hqK := piece.hiddenArity_le
    have hiK := i.isLt
    omega⟩

/-- Common-depth graph map.  Its first `hiddenArity + 1` parameter
coordinates are the original equations.  Later parameter coordinates are
free inputs, shifted by one so that the whole domain still has dimension
`n + K`. -/
def graphMap
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    RealEuclidean (n + K) → RealEuclidean (n + (K + 1)) :=
  fun z ↦ realEuclideanAppend (realEuclideanTakeLeft z)
    (fun i ↦
      if hi : i.val < piece.hiddenArity + 1 then
        piece.constituent.equation ⟨i.val, hi⟩ (piece.graphInput z)
      else
        realEuclideanTakeRight z
          (piece.trailingInputIndex i (Nat.le_of_not_gt hi)))

@[simp]
theorem graphMap_castAdd
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (z : RealEuclidean (n + K)) (i : Fin n) :
    piece.graphMap z (Fin.castAdd (K + 1) i) =
      z (Fin.castAdd K i) := by
  simp [graphMap, realEuclideanTakeLeft]

theorem graphMap_natAdd_of_lt
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (z : RealEuclidean (n + K)) (i : Fin (K + 1))
    (hi : i.val < piece.hiddenArity + 1) :
    piece.graphMap z (Fin.natAdd n i) =
      piece.constituent.equation ⟨i.val, hi⟩
        (piece.graphInput z) := by
  simp only [graphMap, realEuclideanAppend_natAdd]
  rw [dite_eq_left hi]

theorem graphMap_natAdd_of_le
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (z : RealEuclidean (n + K)) (i : Fin (K + 1))
    (hi : piece.hiddenArity + 1 ≤ i.val) :
    piece.graphMap z (Fin.natAdd n i) =
      realEuclideanTakeRight z (piece.trailingInputIndex i hi) := by
  simp only [graphMap, realEuclideanAppend_natAdd]
  rw [dite_eq_right (Nat.not_lt.mpr hi)]

theorem graphMap_contDiff
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    ContDiff ℝ order piece.graphMap := by
  rw [contDiff_pi]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)
  · simpa only [graphMap_castAdd] using
      (contDiff_apply ℝ ℝ (Fin.castAdd K i) :
        ContDiff ℝ order
          (fun z : RealEuclidean (n + K) ↦ z (Fin.castAdd K i)))
  · by_cases hi : i.val < piece.hiddenArity + 1
    · simpa only [graphMap_natAdd_of_lt piece _ i hi] using
        (piece.constituent.equation_contDiff ⟨i.val, hi⟩).fun_comp
          piece.graphInput_contDiff
    · let hle : piece.hiddenArity + 1 ≤ i.val := Nat.le_of_not_gt hi
      simpa only [graphMap_natAdd_of_le piece _ i hle,
        realEuclideanTakeRight] using
        (contDiff_apply ℝ ℝ
          (Fin.natAdd n (piece.trailingInputIndex i hle)) :
          ContDiff ℝ order
            (fun z : RealEuclidean (n + K) ↦
              z (Fin.natAdd n (piece.trailingInputIndex i hle))))

theorem graphMap_differentiable
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (horder : order ≠ 0) :
    Differentiable ℝ piece.graphMap :=
  piece.graphMap_contDiff.differentiable (by simpa using horder)

theorem graphMap_finrank_lt
    (_piece : CharbonnelPaddedSardianConstituent G order n K) :
    Module.finrank ℝ (RealEuclidean (n + K)) <
      Module.finrank ℝ (RealEuclidean (n + (K + 1))) := by
  simp only [Module.finrank_fin_fun]
  omega

/-- A graph input realizing a padded carrier point once a witness for the
original constituent relation has been chosen. -/
def graphWitnessInput
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (v : RealEuclidean (n + (K + 1)))
    (y : RealEuclidean piece.hiddenArity) :
    RealEuclidean (n + K) :=
  realEuclideanAppend (realEuclideanTakeLeft v)
    (fun j ↦
      if hj : j.val < piece.hiddenArity then
        y ⟨j.val, hj⟩
      else
        realEuclideanTakeRight v ⟨j.val + 1, by
          have hjK := j.isLt
          omega⟩)

@[simp]
theorem graphInput_graphWitnessInput
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (v : RealEuclidean (n + (K + 1)))
    (y : RealEuclidean piece.hiddenArity) :
    piece.graphInput (piece.graphWitnessInput v y) =
      realEuclideanAppend (realEuclideanTakeLeft v) y := by
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [graphInput, graphWitnessInput, realEuclideanTakeLeft]
  · simp [graphInput, graphWitnessInput]

theorem graphWitnessInput_trailing
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (v : RealEuclidean (n + (K + 1)))
    (y : RealEuclidean piece.hiddenArity)
    (i : Fin (K + 1))
    (hi : piece.hiddenArity + 1 ≤ i.val) :
    realEuclideanTakeRight (piece.graphWitnessInput v y)
        (piece.trailingInputIndex i hi) =
      realEuclideanTakeRight v i := by
  let j := piece.trailingInputIndex i hi
  have hjq : ¬j.val < piece.hiddenArity := by
    dsimp [j, trailingInputIndex]
    omega
  have hji :
      (⟨j.val + 1, by
        dsimp [j, trailingInputIndex]
        omega⟩ : Fin (K + 1)) = i := by
    apply Fin.ext
    dsimp [j, trailingInputIndex]
    omega
  simp only [graphWitnessInput, realEuclideanTakeRight_append]
  rw [dite_eq_right hjq]
  exact congrArg (realEuclideanTakeRight v) hji

/-- Every padded constituent remains contained in one differentiable graph
range of codimension one. -/
theorem carrier_subset_range_graphMap
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    piece.carrier ⊆ Set.range piece.graphMap := by
  intro v hv
  change
    v ∈ charbonnelParameterPad piece.hiddenArity_le
      piece.constituent.carrier at hv
  rw [mem_charbonnelParameterPad_iff] at hv
  rcases (piece.constituent.mem_carrier_iff).mp hv.1 with
    ⟨⟨y, hy⟩, _hpositive⟩
  refine ⟨piece.graphWitnessInput v y, ?_⟩
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [graphMap, graphWitnessInput, realEuclideanTakeLeft]
  · by_cases hj : j.val < piece.hiddenArity + 1
    · let jsmall : Fin (piece.hiddenArity + 1) := ⟨j.val, hj⟩
      have hcast :
          Fin.castLE (Nat.succ_le_succ piece.hiddenArity_le) jsmall = j := by
        apply Fin.ext
        rfl
      have hequation := hy jsmall
      have hequation' :
          piece.constituent.equation jsmall
              (realEuclideanAppend (realEuclideanTakeLeft v) y) =
            realEuclideanTakeRight v j := by
        simpa [charbonnelParameterPrefixLinearMap, jsmall, hcast] using
          hequation
      rw [graphMap_natAdd_of_lt piece _ j hj,
        graphInput_graphWitnessInput]
      simpa only [jsmall, realEuclideanTakeRight] using hequation'
    · let hjle : piece.hiddenArity + 1 ≤ j.val := Nat.le_of_not_gt hj
      rw [graphMap_natAdd_of_le piece _ j hjle]
      simpa only [realEuclideanTakeRight] using
        piece.graphWitnessInput_trailing v y j hjle

theorem graphMap_range_hausdorffMeasure_eq_zero
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (horder : order ≠ 0) :
    (μH[Module.finrank ℝ (RealEuclidean (n + (K + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (K + 1))))
      (Set.range piece.graphMap) = 0 := by
  simpa only [image_univ] using
    (hausdorffMeasure_image_eq_zero_of_finrank_lt
      (f := piece.graphMap) (s := Set.univ)
      (piece.graphMap_differentiable horder).differentiableOn
      piece.graphMap_finrank_lt)

theorem carrier_hausdorffMeasure_eq_zero
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (horder : order ≠ 0) :
    (μH[Module.finrank ℝ (RealEuclidean (n + (K + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (K + 1))))
      piece.carrier = 0 :=
  measure_mono_null piece.carrier_subset_range_graphMap
    (piece.graphMap_range_hausdorffMeasure_eq_zero horder)

theorem carrier_interior_eq_empty
    (piece : CharbonnelPaddedSardianConstituent G order n K)
    (horder : order ≠ 0) :
    interior piece.carrier = ∅ :=
  (μH[Module.finrank ℝ (RealEuclidean (n + (K + 1)))] :
      MeasureTheory.Measure (RealEuclidean (n + (K + 1)))).interior_eq_empty_of_null
    (piece.carrier_hausdorffMeasure_eq_zero horder)

end CharbonnelPaddedSardianConstituent

namespace CharbonnelFiniteSardianFamily

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

theorem carrier_hausdorffMeasure_eq_zero
    (family : CharbonnelFiniteSardianFamily G order n K)
    (horder : order ≠ 0) :
    (μH[Module.finrank ℝ (RealEuclidean (n + (K + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (K + 1))))
      family.carrier = 0 := by
  let constituents := family.constituents
  change
    (μH[Module.finrank ℝ (RealEuclidean (n + (K + 1)))] :
        MeasureTheory.Measure (RealEuclidean (n + (K + 1))))
      {v | ∃ constituent ∈ constituents, v ∈ constituent.carrier} = 0
  induction constituents with
  | nil => simp
  | cons constituent constituents ih =>
      have hcarrier :
          {v | ∃ piece ∈ constituent :: constituents,
              v ∈ piece.carrier} =
            constituent.carrier ∪
              {v | ∃ piece ∈ constituents, v ∈ piece.carrier} := by
        ext v
        simp
      rw [hcarrier]
      exact measure_union_null
        (constituent.carrier_hausdorffMeasure_eq_zero horder) ih

theorem carrier_interior_eq_empty
    (family : CharbonnelFiniteSardianFamily G order n K)
    (horder : order ≠ 0) :
    interior family.carrier = ∅ :=
  (μH[Module.finrank ℝ (RealEuclidean (n + (K + 1)))] :
      MeasureTheory.Measure (RealEuclidean (n + (K + 1)))).interior_eq_empty_of_null
    (family.carrier_hausdorffMeasure_eq_zero horder)

end CharbonnelFiniteSardianFamily

end AbelFormalization
