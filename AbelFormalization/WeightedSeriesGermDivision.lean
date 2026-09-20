import AbelFormalization.WeightedSeriesRegularSmallness
import AbelFormalization.WeightedSeriesGermRemainder

/-! # Convergent division for actual analytic germs

A weighted convergent divisor regular and normalized in the distinguished
variable divides every actual analytic dividend germ. The remainder is a
polynomial of fixed degree bound, with actual analytic germs in the parameter
variables as coefficients. The proof derives the necessary smallness after
shrinking common radii; it assumes neither convergence of the quotient nor
solvability of division.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual analytic-germ division by a normalized regular weighted divisor.
The order `n` is fixed by the divisor. The smaller convergence radii of the
quotient and the coefficient germs are allowed to depend on the dividend. -/
theorem analyticGerm_division_of_normalized_weighted
    (ρ : Option ι → ℝ) (hρ : ∀ j, 0 < ρ j) (F : WeightedSeries ρ hρ) (n : ℕ)
    (hvanish : ∀ k < n, MvPowerSeries.coeff (Finsupp.single none k) F.val = 0)
    (hnormalized : MvPowerSeries.coeff (Finsupp.single none n) F.val = 1)
    (g : AnalyticGermAt (0 : Option ι → ℝ)) :
    ∃ q : AnalyticGermAt (0 : Option ι → ℝ),
      ∃ c : Fin n → AnalyticGermAt (0 : ι → ℝ),
        g = weightedSeriesGerm ρ hρ F * q +
          ∑ k : Fin n, analyticGermOptionLift (c k) *
            analyticGermOptionCoordinate ^ (k : ℕ) := by
  obtain ⟨r, hr, G, hGg⟩ := exists_weightedSeriesGerm_representation g
  let μ : Option ι → ℝ := fun j => min (ρ j) r
  have hμ : ∀ j, 0 < μ j := fun j => lt_min (hρ j) hr
  have hFμ : WeightedCoeffSummable μ F.val :=
    weightedCoeffSummable_of_radius_le (fun j => (hμ j).le)
      (fun j => min_le_left (ρ j) r) F.property
  have hGμ : WeightedCoeffSummable μ G.val :=
    weightedCoeffSummable_of_radius_le (fun j => (hμ j).le)
      (fun j => min_le_right (ρ j) r) G.property
  obtain ⟨δ, hδ, hδμ, hFδ, hdivision⟩ :=
    exists_regular_weighted_division hμ none n F.val hFμ hvanish hnormalized
  have hGδ : WeightedCoeffSummable δ G.val :=
    weightedCoeffSummable_of_radius_le (fun j => (hδ j).le)
      (fun j => (hδμ j).le) hGμ
  obtain ⟨q, hq, _⟩ := hdivision G.val hGδ
  let η : ι → ℝ := fun j => δ (some j)
  let t : ℝ := δ none
  have hη : ∀ j, 0 < η j := fun j => hδ (some j)
  have ht : 0 < t := hδ none
  have hrad : optionRadius η t = δ := by
    funext j
    cases j <;> rfl
  have hFη : WeightedCoeffSummable (optionRadius η t) F.val := by
    rw [hrad]
    exact hFδ
  have hGη : WeightedCoeffSummable (optionRadius η t) G.val := by
    rw [hrad]
    exact hGδ
  have hqη : WeightedCoeffSummable (optionRadius η t) q := by
    rw [hrad]
    exact hq.1
  let F' : WeightedSeries (optionRadius η t) (optionRadius_pos hη ht) := ⟨F.val, hFη⟩
  let G' : WeightedSeries (optionRadius η t) (optionRadius_pos hη ht) := ⟨G.val, hGη⟩
  let Q : WeightedSeries (optionRadius η t) (optionRadius_pos hη ht) := ⟨q, hqη⟩
  let R := G' - F' * Q
  have hRval : R.val = G.val - F.val * q := by
    change (G' - F' * Q).val = _
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul]
  have hRcut : ∀ d, n ≤ d none → MvPowerSeries.coeff d R.val = 0 := by
    intro d hd
    rw [hRval]
    exact hq.2 d hd
  have hR := weightedSeriesGerm_eq_fin_sum_slices η t hη ht R n hRcut
  have hF' : weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) F' =
      weightedSeriesGerm ρ hρ F := by
    apply (analyticGermOf_eq_iff _ _).mpr
    exact EventuallyEq.rfl
  have hG' : weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) G' = g := by
    calc
      _ = weightedSeriesGerm (fun _ => r) (fun _ => hr) G := by
        apply (analyticGermOf_eq_iff _ _).mpr
        exact EventuallyEq.rfl
      _ = g := hGg
  refine ⟨weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) Q,
    (fun k => weightedSeriesGerm η hη (weightedSeriesSliceCLM η t hη ht (k : ℕ) R)), ?_⟩
  have he : weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) G' =
      weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) F' *
        weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) Q +
      weightedSeriesGerm (optionRadius η t) (optionRadius_pos hη ht) R := by
    change weightedSeriesGermAlgHom _ _ G' =
      weightedSeriesGermAlgHom _ _ F' * weightedSeriesGermAlgHom _ _ Q +
        weightedSeriesGermAlgHom _ _ R
    rw [← map_mul, ← map_add]
    congr 1
    dsimp only [R]
    abel
  rw [hG', hF', hR] at he
  exact he

end AbelFormalization
