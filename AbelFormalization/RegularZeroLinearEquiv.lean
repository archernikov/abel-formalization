import AbelFormalization.RegularZeroBasics

/-!
# Regular zeros under continuous linear equivalences

This module records the exact invariance of regular-zero sets under invertible
linear changes of source and target coordinates.  It is the differential
transport used when a bounded representative coordinate is reclassified as
a bounded-box coordinate in the outer induction.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Regular zeros are invariant under continuous linear equivalences in the
source and target. -/
theorem regularZeroSet_preimage_continuousLinearEquiv
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : E' ≃L[ℝ] E) (q : F ≃L[ℝ] F')
    (Omega : Set E) (f : E → F) :
    regularZeroSet (e ⁻¹' Omega) (q ∘ f ∘ e) =
      e ⁻¹' regularZeroSet Omega f := by
  ext x
  simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_preimage]
  have hderiv :
      fderiv ℝ (q ∘ f ∘ e) x =
        (q : F →L[ℝ] F').comp
          ((fderiv ℝ f (e x)).comp (e : E' →L[ℝ] E)) := by
    rw [q.comp_fderiv, e.comp_right_fderiv]
  constructor
  · rintro ⟨hx, hzero, hsurj⟩
    refine ⟨hx, ?_, ?_⟩
    · exact q.injective (by simpa only [Function.comp_apply, map_zero] using hzero)
    · intro y
      obtain ⟨z, hz⟩ := hsurj (q y)
      refine ⟨e z, ?_⟩
      rw [hderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply] at hz
      exact q.injective hz
  · rintro ⟨hx, hzero, hsurj⟩
    refine ⟨hx, ?_, ?_⟩
    · simpa only [Function.comp_apply, hzero, map_zero]
    · intro y
      obtain ⟨z, hz⟩ := hsurj (q.symm y)
      refine ⟨e.symm z, ?_⟩
      have hez : (e : E' →L[ℝ] E) (e.symm z) = z :=
        e.apply_symm_apply z
      have hqy : (q : F →L[ℝ] F') (q.symm y) = y :=
        q.apply_symm_apply y
      rw [hderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, hez, hz, hqy]

/-- Source and target continuous linear equivalences preserve finiteness of
the regular-zero set. -/
theorem finite_regularZeroSet_comp_continuousLinearEquiv_iff
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : E' ≃L[ℝ] E) (q : F ≃L[ℝ] F')
    (Omega : Set E) (f : E → F) :
    (regularZeroSet (e ⁻¹' Omega) (q ∘ f ∘ e)).Finite ↔
      (regularZeroSet Omega f).Finite := by
  rw [regularZeroSet_preimage_continuousLinearEquiv]
  constructor
  · intro h
    exact h.of_preimage e.surjective
  · intro h
    exact Set.Finite.preimage (Set.injOn_of_injective e.injective) h

end AbelFormalization
