import AbelFormalization.LocalizationLowerBoundTransport

/-!
# Cofinal reindexing of quantitative estimates

All quantitative estimates used in the separated-cluster argument are
filter-local.  They therefore survive pullback along a map tending to the
original filter.  These lemmas let independently chosen finite tails be
combined without rebuilding any analytic or algebraic transfer data.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Topology

variable {X Y ι κ : Type*}

theorem HasPolynomialUpperBound.comp_tendsto
    {l : Filter X} {l' : Filter Y} {scale f : X → ℝ}
    (hf : HasPolynomialUpperBound l scale f)
    (reindex : Y → X) (hreindex : Tendsto reindex l' l) :
    HasPolynomialUpperBound l' (scale ∘ reindex) (f ∘ reindex) := by
  obtain ⟨C, hC, P, hbound⟩ := hf
  exact ⟨C, hC, P, by
    simpa only [Function.comp_apply] using hreindex.eventually hbound⟩

theorem HasUniformPolynomialUpperBound.comp_tendsto
    {l : Filter X} {l' : Filter Y} {scale : X → ℝ}
    {a : κ → ι → X → ℝ}
    (ha : HasUniformPolynomialUpperBound l scale a)
    (reindex : Y → X) (hreindex : Tendsto reindex l' l) :
    HasUniformPolynomialUpperBound l' (scale ∘ reindex)
      (fun k i y ↦ a k i (reindex y)) := by
  obtain ⟨C, hC, P, hbound⟩ := ha
  exact ⟨C, hC, P, by
    simpa only [Function.comp_apply] using hreindex.eventually hbound⟩

theorem HasScalarInversePowerLowerBound.comp_tendsto
    {l : Filter X} {l' : Filter Y} {scale f : X → ℝ}
    (hf : HasScalarInversePowerLowerBound l scale f)
    (reindex : Y → X) (hreindex : Tendsto reindex l' l) :
    HasScalarInversePowerLowerBound l' (scale ∘ reindex) (f ∘ reindex) := by
  obtain ⟨c, hc, M, hlower⟩ := hf
  exact ⟨c, hc, M, by
    simpa only [Function.comp_apply] using hreindex.eventually hlower⟩

theorem HasInversePowerLowerBound.comp_tendsto
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {l' : Filter Y} {scale : X → ℝ}
    {f : ι → X → ℝ}
    (hf : HasInversePowerLowerBound l scale f)
    (reindex : Y → X) (hreindex : Tendsto reindex l' l) :
    HasInversePowerLowerBound l' (scale ∘ reindex)
      (fun i y ↦ f i (reindex y)) := by
  obtain ⟨c, hc, M, hlower⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  simpa only [Function.comp_apply, finiteFamilyMaxAbs] using
    hreindex.eventually hlower

theorem Asymptotics.SuperpolynomialDecay.comp_tendsto
    {l : Filter X} {l' : Filter Y} {scale error : X → ℝ}
    (herror : Asymptotics.SuperpolynomialDecay l scale error)
    (reindex : Y → X) (hreindex : Tendsto reindex l' l) :
    Asymptotics.SuperpolynomialDecay l' (scale ∘ reindex)
      (error ∘ reindex) := by
  intro n
  change Tendsto ((fun x ↦ scale x ^ n * error x) ∘ reindex) l' (𝓝 0)
  exact (herror n).comp hreindex

end AbelFormalization
