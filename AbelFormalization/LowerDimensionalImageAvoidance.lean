import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Avoiding countably many lower-dimensional differentiable images

This file packages the measure-theoretic step needed in the generic-center
argument.  A differentiable image from a smaller finite-dimensional real
normed space has zero Hausdorff measure in the target dimension.  Consequently
one point simultaneously avoids any countable family of such images.
-/

noncomputable section

open Set Function
open scoped MeasureTheory ENNReal

namespace AbelFormalization

set_option autoImplicit false

theorem hausdorffMeasure_image_eq_zero_of_finrank_lt
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E}
    (hf : DifferentiableOn ℝ f s)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) :
    μH[Module.finrank ℝ F] (f '' s) = 0 := by
  refine hausdorffMeasure_of_dimH_lt
    (d := (Module.finrank ℝ F : NNReal)) ?_
  calc
    dimH (f '' s) ≤ dimH s := hf.dimH_image_le
    _ ≤ dimH (Set.univ : Set E) := dimH_mono (Set.subset_univ s)
    _ = (Module.finrank ℝ E : ENNReal) := Real.dimH_univ_eq_finrank E
    _ < (Module.finrank ℝ F : ENNReal) := by exact_mod_cast hdim

theorem exists_avoiding_countable_differentiable_images
    {ι E F : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (f : ι → E → F) (s : ι → Set E)
    (hf : ∀ i, DifferentiableOn ℝ (f i) (s i))
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) :
    ∃ c : F, ∀ i, c ∉ f i '' s i := by
  let bad : Set F := ⋃ i, f i '' s i
  have hbad : μH[Module.finrank ℝ F] bad = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro i
    exact hausdorffMeasure_image_eq_zero_of_finrank_lt (hf i) hdim
  have hbadne : bad ≠ Set.univ := by
    intro hbaduniv
    have hunivzero : μH[Module.finrank ℝ F] (Set.univ : Set F) = 0 := by
      simpa [hbaduniv] using hbad
    exact (isOpen_univ.measure_ne_zero
      (μH[Module.finrank ℝ F] : MeasureTheory.Measure F) univ_nonempty)
      hunivzero
  obtain ⟨c, hc⟩ := Set.nonempty_compl.mpr hbadne
  refine ⟨c, fun i hci ↦ ?_⟩
  exact hc (Set.mem_iUnion.2 ⟨i, hci⟩)

end AbelFormalization
