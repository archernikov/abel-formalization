import AbelFormalization.WeightedSeriesGermDivision
import AbelFormalization.WeightedSeriesAxis
import AbelFormalization.NoetherianByPrincipalQuotients
import AbelFormalization.AnalyticGermDimensionZero
import AbelFormalization.AnalyticGermNoetherianConsequences
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Noetherianity of actual real-analytic germs

Convergent division makes every regular principal quotient finite over the
lower-dimensional germ ring. Regularizing coordinates and a nonzero scalar
normalization reduce every nonzero principal quotient to this situation.
Induction on the number of variables then proves analytic Noetherianity.
-/

noncomputable section

namespace AbelFormalization

section OptionCoordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A normalized regular divisor has a Noetherian principal quotient once
the parameter germ ring is Noetherian. -/
theorem analyticGermOption_quotient_noetherian_of_normalized
    [IsNoetherianRing (AnalyticGermAt (0 : ι → ℝ))]
    (ρ : Option ι → ℝ) (hρ : ∀ j, 0 < ρ j) (F : WeightedSeries ρ hρ) (n : ℕ)
    (hvanish : ∀ k < n, MvPowerSeries.coeff (Finsupp.single none k) F.val = 0)
    (hnormalized : MvPowerSeries.coeff (Finsupp.single none n) F.val = 1) :
    IsNoetherianRing (AnalyticGermAt (0 : Option ι → ℝ) ⧸
      Ideal.span {weightedSeriesGerm ρ hρ F}) := by
  let : Algebra (AnalyticGermAt (0 : ι → ℝ)) (AnalyticGermAt (0 : Option ι → ℝ)) :=
    analyticGermOptionLift.toRingHom.toAlgebra
  apply isNoetherianRing_principal_quotient_of_division
    (R := AnalyticGermAt (0 : ι → ℝ)) (weightedSeriesGerm ρ hρ F)
    analyticGermOptionCoordinate n
  intro g
  obtain ⟨q, c, he⟩ :=
    analyticGerm_division_of_normalized_weighted ρ hρ F n hvanish hnormalized g
  refine ⟨q, c, ?_⟩
  exact he

/-- Adding one real-analytic variable preserves Noetherianity of the actual
germ ring. The principal quotient argument uses genuine convergent division. -/
theorem analyticGermOption_isNoetherian
    [IsNoetherianRing (AnalyticGermAt (0 : ι → ℝ))] :
    IsNoetherianRing (AnalyticGermAt (0 : Option ι → ℝ)) := by
  classical
  apply isNoetherianRing_of_nonzero_principal_quotients
  intro g hg
  obtain ⟨e, hregular⟩ := exists_regularizing_coordinate_linearChange none g hg
  let Φ := analyticGermLinearChange e
  obtain ⟨r, hr, F, hF⟩ := exists_weightedSeriesGerm_representation (Φ g)
  have haxis : analyticGermAlong (Pi.single none 1)
      (weightedSeriesGerm (fun _ => r) (fun _ => hr) F) ≠ 0 := by
    rw [hF]
    exact hregular
  obtain ⟨n, c, hc, hvanish, hnormalized⟩ :=
    weightedSeriesAxisCoeff_exists_normalization_of_germ
      (fun _ => r) (fun _ => hr) F none haxis
  have hnorm := analyticGermOption_quotient_noetherian_of_normalized
    (fun _ => r) (fun _ => hr) (c • F) n hvanish hnormalized
  have hscaled : weightedSeriesGerm (fun _ => r) (fun _ => hr) (c • F) = c • Φ g := by
    change weightedSeriesGermAlgHom (fun _ => r) (fun _ => hr) (c • F) = _
    rw [map_smul, weightedSeriesGermAlgHom_apply, hF]
  have hunit : IsUnit (algebraMap ℝ (AnalyticGermAt (0 : Option ι → ℝ)) c) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ _)
  have hideal : Ideal.span {c • Φ g} = Ideal.span {Φ g} := by
    simpa only [Algebra.smul_def] using Ideal.span_singleton_mul_left_unit hunit (Φ g)
  have hquot : IsNoetherianRing
      (AnalyticGermAt (0 : Option ι → ℝ) ⧸ Ideal.span {Φ g}) := by
    let := hnorm
    have heq : Ideal.span {weightedSeriesGerm (fun _ => r) (fun _ => hr) (c • F)} =
        Ideal.span {Φ g} := by rw [hscaled, hideal]
    exact isNoetherianRing_of_ringEquiv _ (Ideal.quotEquivOfEq heq)
  let := hquot
  let E := Ideal.quotientEquiv (Ideal.span {g}) (Ideal.span {Φ g}) Φ.toRingEquiv
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  exact isNoetherianRing_of_ringEquiv _ E.symm

end OptionCoordinates

/-- Reindexing the coordinates identifies the successor-dimensional germ
ring with the ring obtained by adding one distinguished Option coordinate. -/
def analyticGermFinSuccEquiv (p : ℕ) :
    AnalyticGermAt (0 : Option (Fin p) → ℝ) ≃ₐ[ℝ] RealAnalyticGerm (p + 1) := by
  let e : (Fin (p + 1) → ℝ) ≃L[ℝ] (Option (Fin p) → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Option (Fin p) => ℝ) (finSuccEquiv p)
  exact analyticGermEquivOfLocalInverse e e.symm
    (e.toContinuousLinearMap.analyticAt 0) (e.symm.toContinuousLinearMap.analyticAt 0)
    (map_zero _) (map_zero _)
    (Filter.Eventually.of_forall e.symm_apply_apply)
    (Filter.Eventually.of_forall e.apply_symm_apply)

/-- The actual ring of real-analytic germs is Noetherian in every finite
dimension, proved by convergent division and induction on the dimension. -/
theorem realAnalyticGerm_isNoetherian (p : ℕ) : IsNoetherianRing (RealAnalyticGerm p) := by
  induction p with
  | zero => exact realAnalyticGerm_zero_isNoetherian
  | succ p ih =>
    let := ih
    let := analyticGermOption_isNoetherian (ι := Fin p)
    exact isNoetherianRing_of_ringEquiv _ (analyticGermFinSuccEquiv p).toRingEquiv

instance realAnalyticGermNoetherianRing (p : ℕ) : IsNoetherianRing (RealAnalyticGerm p) :=
  realAnalyticGerm_isNoetherian p

/-- The analytic germ ring has exactly its number of variables as Krull dimension. -/
theorem realAnalyticGerm_dimension (p : ℕ) : ringKrullDim (RealAnalyticGerm p) = p :=
  realAnalyticGerm_dimension_of_isNoetherian p

/-- The actual real-analytic germ ring is a regular local ring. -/
theorem realAnalyticGerm_regular (p : ℕ) : IsRegularLocalRing (RealAnalyticGerm p) :=
  realAnalyticGerm_regular_of_isNoetherian p

instance realAnalyticGermRegularLocalRing (p : ℕ) : IsRegularLocalRing (RealAnalyticGerm p) :=
  realAnalyticGerm_regular p

end AbelFormalization
