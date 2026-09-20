import AbelFormalization.RestrictedAbelAuxExtension

/-!
# Simultaneous last-generator lifting for square systems

The scalar polynomial lift can be chosen for every component of a system at
once.  After adding one unrestricted coordinate, all lifted components lie
one exponential level lower and recover the original system when the last
exponential generator is substituted into that coordinate.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {ι κ : Type*}

/-- Abel-typed form of the scalar last-generator lift. -/
theorem RestrictedExpressionTower.exists_restrictedAbelLastGeneratorLift_of_mem_level_succ
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (i : Fin ell)
    (f : RestrictedSource m p a → ℝ) (hf : f ∈ T.level (i.val + 1)) :
    ∃ F : RestrictedSource m p (a + 1) → ℝ,
      F ∈ (T.extendAuxAbel A representative offset 1).level i.val ∧
        ∀ x, F (restrictedSourceAppendAuxOne x (T.generator i x)) = f x := by
  obtain ⟨F, hF, hFeval⟩ :=
    T.exists_restrictedLastGeneratorLift_of_mem_level_succ i f hf
  refine ⟨F, ?_, hFeval⟩
  rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
  exact hF

/-- Simultaneously lift every component of a system using the last
exponential generator. -/
theorem RestrictedExpressionTower.exists_restrictedAbelLastGeneratorSystemLift_of_mem_level_succ
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (i : Fin ell)
    (F : κ → RestrictedSource m p a → ℝ)
    (hF : ∀ k, F k ∈ T.level (i.val + 1)) :
    ∃ Ftilde : κ → RestrictedSource m p (a + 1) → ℝ,
      (∀ k, Ftilde k ∈
        (T.extendAuxAbel A representative offset 1).level i.val) ∧
      (∀ x k,
        Ftilde k (restrictedSourceAppendAuxOne x (T.generator i x)) =
          F k x) := by
  have hchoice : ∀ k, ∃ ftilde : RestrictedSource m p (a + 1) → ℝ,
      ftilde ∈ (T.extendAuxAbel A representative offset 1).level i.val ∧
        ∀ x, ftilde
          (restrictedSourceAppendAuxOne x (T.generator i x)) = F k x :=
    fun k ↦ T.exists_restrictedAbelLastGeneratorLift_of_mem_level_succ
      A representative offset i (F k) (hF k)
  choose Ftilde hFtilde hFtilde_eval using hchoice
  exact ⟨Ftilde, hFtilde, fun x k ↦ hFtilde_eval k x⟩

/-- Pointwise vector-valued form of simultaneous recovery. -/
theorem RestrictedExpressionTower.exists_restrictedAbelLastGeneratorSystemLift_apply
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (i : Fin ell)
    (F : κ → RestrictedSource m p a → ℝ)
    (hF : ∀ k, F k ∈ T.level (i.val + 1)) :
    ∃ Ftilde : κ → RestrictedSource m p (a + 1) → ℝ,
      (∀ k, Ftilde k ∈
        (T.extendAuxAbel A representative offset 1).level i.val) ∧
      (∀ x,
        (fun k ↦ Ftilde k
          (restrictedSourceAppendAuxOne x (T.generator i x))) =
        fun k ↦ F k x) := by
  obtain ⟨Ftilde, hmem, heval⟩ :=
    T.exists_restrictedAbelLastGeneratorSystemLift_of_mem_level_succ
      A representative offset i F hF
  refine ⟨Ftilde, hmem, ?_⟩
  intro x
  funext k
  exact heval x k

end AbelFormalization
