import AbelFormalization.WeightedSeriesEvaluationMap

/-! # Restriction to smaller polyradii

Shrinking positive coordinate radii preserves weighted summability. The
coefficientwise identity is an injective continuous algebra homomorphism with
operator norm at most one, and leaves pointwise evaluation unchanged.
-/

noncomputable section

namespace AbelFormalization

variable {σ : Type*}

/-- Monomial weights increase with nonnegative coordinate radii. -/
theorem multiRadiusWeight_mono {τ ρ : σ → ℝ} (hτ : ∀ i, 0 ≤ τ i)
    (hτρ : ∀ i, τ i ≤ ρ i) (d : σ →₀ ℕ) :
    multiRadiusWeight τ d ≤ multiRadiusWeight ρ d :=
  Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hτ i) _)
    (fun i _ => pow_le_pow_left₀ (hτ i) (hτρ i) _)

theorem weightedCoeffSummable_of_radius_le {τ ρ : σ → ℝ} (hτ : ∀ i, 0 ≤ τ i)
    (hτρ : ∀ i, τ i ≤ ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) : WeightedCoeffSummable τ f :=
  hf.of_nonneg_of_le
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hτ d))
    (fun d => mul_le_mul_of_nonneg_left (multiRadiusWeight_mono hτ hτρ d) (norm_nonneg _))

theorem weightedCoeffNorm_mono_radius {τ ρ : σ → ℝ} (hτ : ∀ i, 0 ≤ τ i)
    (hτρ : ∀ i, τ i ≤ ρ i) {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) : weightedCoeffNorm τ f ≤ weightedCoeffNorm ρ f :=
  Summable.tsum_le_tsum
    (fun d => mul_le_mul_of_nonneg_left (multiRadiusWeight_mono hτ hτρ d) (norm_nonneg _))
    (weightedCoeffSummable_of_radius_le hτ hτρ hf) hf

/-- The coefficientwise identity, from larger to smaller positive radii. -/
def weightedSeriesRestrictAlgHom (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) :
    WeightedSeries ρ hρ →ₐ[ℝ] WeightedSeries τ hτ :=
  Subalgebra.inclusion (show weightedSeriesSubalgebra ρ (fun i => (hρ i).le) ≤
      weightedSeriesSubalgebra τ (fun i => (hτ i).le) from
    fun _ hf => weightedCoeffSummable_of_radius_le (fun i => (hτ i).le) hτρ hf)

@[simp]
theorem weightedSeriesRestrictAlgHom_val (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) (f : WeightedSeries ρ hρ) :
    (weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ f).val = f.val :=
  Subalgebra.coe_inclusion _ f

/-- Restricting the radius has operator bound one. -/
def weightedSeriesRestrictCLM (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) :
    WeightedSeries ρ hρ →L[ℝ] WeightedSeries τ hτ :=
  (weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ).toLinearMap.mkContinuous 1 fun f => by
    change ‖weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ f‖ ≤ 1 * ‖f‖
    rw [one_mul, weightedSeries_norm_eq τ hτ, weightedSeries_norm_eq ρ hρ,
      weightedSeriesRestrictAlgHom_val]
    exact weightedCoeffNorm_mono_radius (fun i => (hτ i).le) hτρ f.property

@[simp]
theorem weightedSeriesRestrictCLM_val (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) (f : WeightedSeries ρ hρ) :
    (weightedSeriesRestrictCLM ρ τ hρ hτ hτρ f).val = f.val := by
  unfold weightedSeriesRestrictCLM
  rw [LinearMap.mkContinuous_apply, AlgHom.toLinearMap_apply]
  exact weightedSeriesRestrictAlgHom_val ρ τ hρ hτ hτρ f

theorem weightedSeriesRestrictCLM_norm_le (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) :
    ‖weightedSeriesRestrictCLM ρ τ hρ hτ hτρ‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

def weightedSeriesRestrictContinuousAlgHom (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) :
    WeightedSeries ρ hρ →A[ℝ] WeightedSeries τ hτ where
  toAlgHom := weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ
  cont := (weightedSeriesRestrictCLM ρ τ hρ hτ hτρ).continuous

theorem weightedSeriesRestrict_injective (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) :
    Function.Injective (weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ) :=
  Subalgebra.inclusion_injective _

@[simp]
theorem weightedSeriesEval_restrict (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) (f : WeightedSeries ρ hρ)
    (x : σ → ℝ) :
    weightedSeriesEval (weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ f).val x =
      weightedSeriesEval f.val x := by
  rw [weightedSeriesRestrictAlgHom_val]

theorem weightedSeriesRestrict_comp (ρ τ υ : σ → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hτ : ∀ i, 0 < τ i) (hυ : ∀ i, 0 < υ i)
    (hτρ : ∀ i, τ i ≤ ρ i) (hυτ : ∀ i, υ i ≤ τ i) :
    (weightedSeriesRestrictAlgHom τ υ hτ hυ hυτ).comp
      (weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ) =
        weightedSeriesRestrictAlgHom ρ υ hρ hυ (fun i => (hυτ i).trans (hτρ i)) := by
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  simp only [AlgHom.comp_apply, weightedSeriesRestrictAlgHom_val]

end AbelFormalization
