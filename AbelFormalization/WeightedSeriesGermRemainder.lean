import AbelFormalization.WeightedSeriesGerm
import AbelFormalization.WeightedSeriesCoefficientSlice
import AbelFormalization.AnalyticGermComposition
import Mathlib.Algebra.BigOperators.Fin

/-! # Polynomial remainders with actual analytic-germ coefficients

A weighted convergent series with a cutoff in its distinguished variable is
a finite polynomial in that coordinate. Its coefficients are actual analytic
germs in the parameter variables, lifted by the coordinate projection.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Project an extended tuple onto its parameter coordinates. -/
def analyticGermOptionParameters : (Option ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (some j))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem analyticGermOptionParameters_apply (z : Option ι → ℝ) (j : ι) :
    analyticGermOptionParameters z j = z (some j) := rfl

/-- Lift an actual parameter germ to a germ independent of the distinguished
coordinate. -/
def analyticGermOptionLift :
    AnalyticGermAt (0 : ι → ℝ) →ₐ[ℝ] AnalyticGermAt (0 : Option ι → ℝ) :=
  analyticGermPullback analyticGermOptionParameters
    ((analyticGermOptionParameters : (Option ι → ℝ) →L[ℝ] (ι → ℝ)).analyticAt
      (0 : Option ι → ℝ)) (map_zero _)

/-- The germ of the distinguished coordinate. -/
def analyticGermOptionCoordinate : AnalyticGermAt (0 : Option ι → ℝ) :=
  analyticGermOf (fun z : Option ι → ℝ => z none)
    ((ContinuousLinearMap.proj none : (Option ι → ℝ) →L[ℝ] ℝ).analyticAt 0)

/-- A coefficient cutoff produces a polynomial identity in the actual germ
algebra, with coefficients in the lower-dimensional parameter germ algebra. -/
theorem weightedSeriesGerm_eq_sum_slices (ρ : ι → ℝ) (τ : ℝ)
    (hρ : ∀ j, 0 < ρ j) (hτ : 0 < τ)
    (R : WeightedSeries (optionRadius ρ τ) (optionRadius_pos hρ hτ)) (n : ℕ)
    (hcut : ∀ d, n ≤ d none → MvPowerSeries.coeff d R.val = 0) :
    weightedSeriesGerm (optionRadius ρ τ) (optionRadius_pos hρ hτ) R =
      ∑ k ∈ Finset.range n,
        analyticGermOptionLift
          (weightedSeriesGerm ρ hρ (weightedSeriesSliceCLM ρ τ hρ hτ k R)) *
          analyticGermOptionCoordinate ^ k := by
  let g : ℕ → (Option ι → ℝ) → ℝ := fun k z =>
    weightedSeriesEval (mvPowerSeriesCoefficientSlice k R.val)
      (fun j => z (some j)) * z none ^ k
  apply Subtype.ext
  calc
    _ = (Germ.coeRingHom (𝓝 (0 : Option ι → ℝ))) (∑ k ∈ Finset.range n, g k) := by
      apply Germ.coe_eq.mpr
      filter_upwards [eventually_abs_le_polyradius (optionRadius ρ τ)
        (optionRadius_pos hρ hτ)] with z hz
      have he := weightedSeriesEval_eq_sum_slices
        (fun j => hz (some j)) (hz none) R.property n hcut
      have hz' : optionRadius (fun j => z (some j)) (z none) = z := by
        funext j
        cases j <;> rfl
      simpa only [hz', Finset.sum_apply, g] using he
    _ = (analyticGermSubring (0 : Option ι → ℝ)).subtype
        (∑ k ∈ Finset.range n,
          analyticGermOptionLift
            (weightedSeriesGerm ρ hρ (weightedSeriesSliceCLM ρ τ hρ hτ k R)) *
            analyticGermOptionCoordinate ^ k) := by
      simp only [map_sum, map_mul, map_pow]
      apply Finset.sum_congr rfl
      intro k hk
      change (g k : Germ (𝓝 (0 : Option ι → ℝ)) ℝ) =
        ((fun z : Option ι → ℝ =>
          weightedSeriesEval (weightedSeriesSliceCLM ρ τ hρ hτ k R).val
            (fun j => z (some j)) * z none ^ k) : Germ (𝓝 (0 : Option ι → ℝ)) ℝ)
      apply Germ.coe_eq.mpr
      filter_upwards with z
      dsimp only [g]
      rw [weightedSeriesSliceCLM_val]

/-- The same actual germ polynomial identity, indexed by `Fin n` for finite
module-generation arguments. -/
theorem weightedSeriesGerm_eq_fin_sum_slices (ρ : ι → ℝ) (τ : ℝ)
    (hρ : ∀ j, 0 < ρ j) (hτ : 0 < τ)
    (R : WeightedSeries (optionRadius ρ τ) (optionRadius_pos hρ hτ)) (n : ℕ)
    (hcut : ∀ d, n ≤ d none → MvPowerSeries.coeff d R.val = 0) :
    weightedSeriesGerm (optionRadius ρ τ) (optionRadius_pos hρ hτ) R =
      ∑ k : Fin n,
        analyticGermOptionLift
          (weightedSeriesGerm ρ hρ (weightedSeriesSliceCLM ρ τ hρ hτ (k : ℕ) R)) *
          analyticGermOptionCoordinate ^ (k : ℕ) := by
  rw [weightedSeriesGerm_eq_sum_slices ρ τ hρ hτ R n hcut, Finset.sum_range]

end AbelFormalization
