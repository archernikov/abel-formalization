import AbelFormalization.CharbonnelIntegerAffineSliceMetric
import AbelFormalization.CharbonnelSardianLiteralZeroLevelControls

/-!
# The compact radial-slice topological below step in Wilkie 3.12

At a fixed positive radial parameter, the visible reciprocal-radial
sublevel is compact. For a closed target and a nonzero integer-affine row,
closeness to the target together with a small squared slice level forces
closeness to the actual target–hyperplane intersection. The zero-row cases
are separate: zero constant gives the whole space; nonzero constant makes
every sufficiently small slice-level section empty.

The statements choose only the topological closeness scales. They do not
construct a nested approximation modulus or a Sardian certificate.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Fixed-radial compact below-clause scales for a nonzero
integer-affine hyperplane row. The old target is required to be closed,
as in the target closure of the Sardian approximation clauses. -/
theorem exists_compactRadial_integerAffineSlice_below_scales_of_nonzero
    {n : ℕ} (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    (radial : ℝ) (_hradial : 0 < radial)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaOld etaSlice : ℝ,
      0 < etaOld ∧ 0 < etaSlice ∧
        ∀ x : RealEuclidean n,
          literalZeroVisibleRadialDenominator x ≤ radial⁻¹ →
          (∃ y ∈ A, dist x y < etaOld) →
          (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ etaSlice →
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta := by
  let K : Set (RealEuclidean n) :=
    {x | literalZeroVisibleRadialDenominator x ≤ radial⁻¹}
  have hK : IsCompact K :=
    isCompact_literalZeroVisibleRadialDenominator_sublevel radial⁻¹
  have hH : IsClosed (integerAffineSliceHyperplane coeff constant) :=
    isClosed_integerAffineSliceHyperplane coeff constant
  obtain ⟨eta, heta, hnear⟩ :=
    compact_closed_intersection_thickening hK hA hH hdelta
  obtain ⟨epsilon, hepsilon, hlevelScale⟩ :=
    exists_integerAffineSlice_sqLevel_thickening_scale
      coeff constant hnonzero heta
  refine ⟨eta, epsilon, heta, hepsilon, ?_⟩
  intro x hxRadial hnearA hxLevel
  have hxK : x ∈ K := hxRadial
  obtain ⟨y, hyA, hxy⟩ := hnearA
  have hxNearA : x ∈ Metric.thickening eta A :=
    Metric.mem_thickening_iff.mpr ⟨y, hyA, hxy⟩
  have hxNearH : x ∈ Metric.thickening eta
      (integerAffineSliceHyperplane coeff constant) :=
    hlevelScale x hxLevel
  exact Metric.mem_thickening_iff.mp
    (hnear x hxK hxNearA hxNearH)

/-- If the row and constant vanish, the displayed hyperplane is all of
space. The old-target witness itself supplies the below clause; the
radial and slice-level premises impose no further topological condition. -/
theorem exists_compactRadial_integerAffineSlice_below_scales_of_zero_zero
    {n : ℕ} (A : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (hconstant : constant = 0)
    (radial : ℝ) (_hradial : 0 < radial)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaOld etaSlice : ℝ,
      0 < etaOld ∧ 0 < etaSlice ∧
        ∀ x : RealEuclidean n,
          literalZeroVisibleRadialDenominator x ≤ radial⁻¹ →
          (∃ y ∈ A, dist x y < etaOld) →
          (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ etaSlice →
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta := by
  refine ⟨delta, 1, hdelta, zero_lt_one, ?_⟩
  intro x _ ⟨y, hyA, hxy⟩ _
  refine ⟨y, ⟨hyA, ?_⟩, hxy⟩
  rw [integerAffineSliceHyperplane_eq_univ_of_coeff_zero
    coeff constant hzero hconstant]
  exact Set.mem_univ y

/-- If the row vanishes but its integer constant does not, all squared
slice levels below one are impossible. Thus the below clause for the empty
displayed hyperplane is vacuous at a positive scale below one. -/
theorem exists_compactRadial_integerAffineSlice_below_scales_of_zero_nonzero
    {n : ℕ} (A : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j, coeff j = 0) (hconstant : constant ≠ 0)
    (radial : ℝ) (_hradial : 0 < radial)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaOld etaSlice : ℝ,
      0 < etaOld ∧ 0 < etaSlice ∧
        ∀ x : RealEuclidean n,
          literalZeroVisibleRadialDenominator x ≤ radial⁻¹ →
          (∃ y ∈ A, dist x y < etaOld) →
          (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ etaSlice →
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta := by
  refine ⟨delta, (1 / 2 : ℝ), hdelta, by norm_num, ?_⟩
  intro x _ _ hxLevel
  exact False.elim
    ((no_small_integerAffineSliceLevel_of_coeff_zero_constant_ne
      coeff constant hzero hconstant (by norm_num) x) hxLevel)

/-- The row-independent fixed-radial below-clause interface. Its proof
classifies nonzero rows, zero rows with zero constant, and inconsistent
zero rows rather than imposing a false nondegeneracy premise on every
integer-affine equation. -/
theorem exists_compactRadial_integerAffineSlice_below_scales
    {n : ℕ} (A : Set (RealEuclidean n)) (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (radial : ℝ) (hradial : 0 < radial)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaOld etaSlice : ℝ,
      0 < etaOld ∧ 0 < etaSlice ∧
        ∀ x : RealEuclidean n,
          literalZeroVisibleRadialDenominator x ≤ radial⁻¹ →
          (∃ y ∈ A, dist x y < etaOld) →
          (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ etaSlice →
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta := by
  by_cases hnonzero : ∃ j : Fin n, coeff j ≠ 0
  · exact exists_compactRadial_integerAffineSlice_below_scales_of_nonzero
      A hA coeff constant hnonzero radial hradial hdelta
  · have hzero : ∀ j : Fin n, coeff j = 0 := by
      push Not at hnonzero
      exact hnonzero
    by_cases hconstant : constant = 0
    · exact exists_compactRadial_integerAffineSlice_below_scales_of_zero_zero
        A coeff constant hzero hconstant radial hradial hdelta
    · exact exists_compactRadial_integerAffineSlice_below_scales_of_zero_nonzero
        A coeff constant hzero hconstant radial hradial hdelta

/-- Set-section form of the fixed-radial below step. The new section has
exactly the old-section, radial-sublevel, and squared-level intersections
that occur in `wilkieAffineSliceConstituent_section_eq`. An old-section
proximity estimate at the chosen scale is an explicit premise. -/
theorem exists_compactRadial_integerAffineSlice_section_below_scales
    {n : ℕ} (A oldSection : Set (RealEuclidean n))
    (hA : IsClosed A)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (radial : ℝ) (hradial : 0 < radial)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaOld etaSlice : ℝ,
      0 < etaOld ∧ 0 < etaSlice ∧
        ((∀ x ∈ oldSection, ∃ y ∈ A, dist x y < etaOld) →
          ∀ x ∈
            oldSection ∩
              {x | literalZeroVisibleRadialDenominator x ≤ radial⁻¹} ∩
              {x | (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤
                etaSlice},
            ∃ z ∈ A ∩ integerAffineSliceHyperplane coeff constant,
              dist x z < delta) := by
  obtain ⟨etaOld, etaSlice, hetaOld, hetaSlice, hpoint⟩ :=
    exists_compactRadial_integerAffineSlice_below_scales
      A hA coeff constant radial hradial hdelta
  refine ⟨etaOld, etaSlice, hetaOld, hetaSlice, ?_⟩
  intro hOld x hx
  exact hpoint x hx.1.2 (hOld x hx.1.1) hx.2

end AbelFormalization
