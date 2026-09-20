import AbelFormalization.RegularZeroBasics

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

theorem regularZeroSet_preimage_add_right
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E) (Omega : Set E) (f : E → F) :
    regularZeroSet ((fun x : E ↦ x + c) ⁻¹' Omega)
        (fun x ↦ f (x + c)) =
      (fun x : E ↦ x + c) ⁻¹' regularZeroSet Omega f := by
  ext x
  simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [fderiv_comp_add_right]

theorem finite_regularZeroSet_add_right_iff
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E) (Omega : Set E) (f : E → F) :
    (regularZeroSet ((fun x : E ↦ x + c) ⁻¹' Omega)
      (fun x ↦ f (x + c))).Finite ↔
      (regularZeroSet Omega f).Finite := by
  rw [regularZeroSet_preimage_add_right]
  constructor
  · intro h
    apply h.of_preimage
    intro x
    exact ⟨x - c, by abel⟩
  · intro h
    exact Set.Finite.preimage
      (Set.injOn_of_injective (fun _ _ hxy ↦ add_right_cancel hxy)) h

end AbelFormalization
