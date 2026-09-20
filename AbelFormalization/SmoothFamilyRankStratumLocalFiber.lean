import AbelFormalization.SmoothFamilyJacobianRankStrata
import Mathlib.Analysis.Calculus.Implicit

/-!
# Local fiber charts selected by a nonzero Jacobian minor

A nonzero `k × k` Jacobian minor selects `k` output coordinates whose
derivative is surjective.  The finite-dimensional implicit function theorem
then gives a local chart in which those selected coordinates are the first
projection.

This is the regular-value consequence available from the current mathlib API.
It does not identify a fiber of the original map with a fiber of the selected
output map: that further step needs a constant-rank theorem, or a separate
stratification argument controlling the unselected output coordinates.
-/

noncomputable section

open Set Function
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Restrict a coordinate-valued map to an injectively selected family of
output coordinates. -/
def selectedOutputMap {a b k : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (rows : Fin k ↪ Fin b) :
    RealEuclidean a → RealEuclidean k :=
  fun x i ↦ g x (rows i)

/-- A selected-output maximal minor is definitionally the corresponding
row-and-column minor of the original Jacobian. -/
theorem standardJacobianColumnMinor_selectedOutputMap
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) (x : RealEuclidean a) :
    standardJacobianColumnMinor (selectedOutputMap g rows) cols x =
      standardJacobianMinor g rows cols x := by
  rfl

/-- A nonzero square minor makes the derivative of the corresponding selected
output map surjective. -/
theorem fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : DifferentiableAt ℝ g x)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hminor : standardJacobianMinor g rows cols x ≠ 0) :
    Function.Surjective (fderiv ℝ (selectedOutputMap g rows) x) := by
  have hselected : DifferentiableAt ℝ (selectedOutputMap g rows) x := by
    change DifferentiableAt ℝ (fun y i ↦ g y (rows i)) x
    rw [differentiableAt_pi]
    intro i
    exact differentiableAt_pi.mp hg (rows i)
  apply
    (AbelFormalization.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
      hselected).mpr
  refine ⟨cols, ?_⟩
  rw [standardJacobianColumnMinor_selectedOutputMap]
  exact hminor

/-- Near a point where a selected minor is nonzero, the selected output map is
the first projection in an implicit-function chart. -/
theorem exists_localProjectionChart_of_standardJacobianMinor_ne_zero
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : ContDiffAt ℝ 1 g x)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hminor : standardJacobianMinor g rows cols x ≠ 0) :
    ∃ e : OpenPartialHomeomorph (RealEuclidean a)
        (RealEuclidean k ×
          (fderiv ℝ (selectedOutputMap g rows) x).ker),
      x ∈ e.source ∧
        e x = (selectedOutputMap g rows x, 0) ∧
          ∀ y, (e y).1 = selectedOutputMap g rows y := by
  have hselected : ContDiffAt ℝ 1 (selectedOutputMap g rows) x := by
    change ContDiffAt ℝ 1 (fun y i ↦ g y (rows i)) x
    rw [contDiffAt_pi]
    intro i
    exact contDiffAt_pi.mp hg (rows i)
  have hstrict : HasStrictFDerivAt (selectedOutputMap g rows)
      (fderiv ℝ (selectedOutputMap g rows) x) x :=
    hselected.hasStrictFDerivAt one_ne_zero
  have hsurjective : Function.Surjective
      (fderiv ℝ (selectedOutputMap g rows) x) :=
    fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
      (hg.differentiableAt one_ne_zero) rows cols hminor
  have hsurj : (fderiv ℝ (selectedOutputMap g rows) x).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  let e := hstrict.implicitToOpenPartialHomeomorph
    (selectedOutputMap g rows)
    (fderiv ℝ (selectedOutputMap g rows) x) hsurj
  refine ⟨e, ?_, ?_, ?_⟩
  · exact hstrict.mem_implicitToOpenPartialHomeomorph_source hsurj
  · exact hstrict.implicitToOpenPartialHomeomorph_self hsurj
  · intro y
    exact hstrict.implicitToOpenPartialHomeomorph_fst hsurj y

/-- At every exact-rank-`k` point, some `k` selected output coordinates have
the local projection chart above.  This conclusion concerns the selected
output map; it does not assert that the exact-rank locus is itself a manifold. -/
theorem exists_selectedOutput_localProjectionChart_of_mem_standardJacobianRankLocus
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : ContDiffAt ℝ 1 g x)
    (hx : x ∈ standardJacobianRankLocus g k) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
      standardJacobianMinor g rows cols x ≠ 0 ∧
        ∃ e : OpenPartialHomeomorph (RealEuclidean a)
            (RealEuclidean k ×
              (fderiv ℝ (selectedOutputMap g rows) x).ker),
          x ∈ e.source ∧
            e x = (selectedOutputMap g rows x, 0) ∧
              ∀ y, (e y).1 = selectedOutputMap g rows y := by
  have hxrank : Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap) = k := hx
  have hminors :=
    (finrank_range_fderiv_eq_iff_standardJacobianMinors
      (hg.differentiableAt one_ne_zero)).mp hxrank
  obtain ⟨rows, cols, hminor⟩ := hminors.1
  obtain ⟨e, hxsource, hex, hfirst⟩ :=
    exists_localProjectionChart_of_standardJacobianMinor_ne_zero
      hg rows cols hminor
  exact ⟨rows, cols, hminor, e, hxsource, hex, hfirst⟩

end AbelFormalization
