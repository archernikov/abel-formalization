import AbelFormalization.RestrictedBoundedReclassificationOffsets

/-!
# Scratch: expression bases after bounded-representative reclassification

The source reclassification sends fixed generators to fixed generators.  A
retained Abel jet becomes the corresponding jet over the enlarged box, while
a pivot Abel jet becomes an analytic coefficient over that box.  Consequently
the pullback of the old restricted expression base is contained in the
reclassified base.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

@[simp]
theorem precomp_restrictedSCoordinate_reclassifyAt_pivot
    {m p a : ℕ} (i : Fin (m + 1)) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)
        (restrictedSCoordinate (p := p) (a := a) i) =
      restrictedWCoordinate (m := m) (p := p + 1) (a := a)
        (Fin.last p) := by
  funext x
  exact restrictedSourceReclassifyAt_apply_pivot i x

@[simp]
theorem precomp_restrictedSCoordinate_reclassifyAt_succAbove
    {m p a : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)
        (restrictedSCoordinate (p := p) (a := a) (i.succAbove j)) =
      restrictedSCoordinate (p := p + 1) (a := a) j := by
  funext x
  exact restrictedSourceReclassifyAt_apply_succAbove i x j

@[simp]
theorem precomp_restrictedAuxCoordinate_reclassifyAt
    {m p a : ℕ} (i : Fin (m + 1)) (k : Fin a) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)
        (restrictedAuxCoordinate (m := m + 1) (p := p) k) =
      restrictedAuxCoordinate (m := m) (p := p + 1) k := by
  funext x
  exact restrictedSourceReclassifyAt_apply_aux i x k

@[simp]
theorem precomp_restrictedBoxCoefficientPullback_reclassifyAt
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1))
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)
        (restrictedBoxCoefficientPullback (m := m + 1) (a := a)
          (f : RestrictedBoxSpace p → ℝ)) =
      restrictedBoxCoefficientPullback (m := m) (a := a)
        (D.pullbackSnoc R M hRM f : RestrictedBoxSpace (p + 1) → ℝ) := by
  funext x
  change
    (f : RestrictedBoxSpace p → ℝ)
        (restrictedSourceReclassifyAt i x).1.2 =
      (f : RestrictedBoxSpace p → ℝ)
        (restrictedBoxInitCLM p x.1.2)
  apply congrArg (f : RestrictedBoxSpace p → ℝ)
  funext j
  exact restrictedSourceReclassifyAt_apply_w i x j

/-- Every old fixed generator remains a fixed generator after moving one
unbounded coordinate into the bounded box. -/
theorem image_restrictedFixedGenerators_reclassifyAt_subset
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1)) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i) ''
        restrictedFixedGenerators (m := m + 1) (a := a) D ⊆
      restrictedFixedGenerators (m := m) (a := a) (D.snoc R M hRM) := by
  rintro g ⟨f, hf, rfl⟩
  rcases hf with (hf | hf)
  · rcases hf with (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · by_cases hji : j = i
      · subst j
        rw [precomp_restrictedSCoordinate_reclassifyAt_pivot]
        refine Or.inr ⟨
          ⟨fun w : RestrictedBoxSpace (p + 1) ↦ w (Fin.last p),
            (D.snoc R M hRM).analyticNearClosedBox_apply (Fin.last p)⟩,
          ?_⟩
        rfl
      · rcases Fin.exists_succAbove_eq hji with ⟨j, rfl⟩
        rw [precomp_restrictedSCoordinate_reclassifyAt_succAbove]
        exact Or.inl (Or.inl ⟨j, rfl⟩)
    · rw [precomp_restrictedAuxCoordinate_reclassifyAt]
      exact Or.inl (Or.inr ⟨k, rfl⟩)
  · rcases hf with ⟨f, rfl⟩
    rw [precomp_restrictedBoxCoefficientPullback_reclassifyAt D R M hRM i]
    exact Or.inr ⟨D.pullbackSnoc R M hRM f, rfl⟩

/-- Pullback of the old Abel restricted-expression base lies in the base
obtained by retaining the non-pivot jets and enlarging the bounded box. -/
theorem IsAbel.map_restrictedExpressionBase_reclassifyAt_le
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset) :
    (restrictedExpressionBase D
        (restrictedAbelJetGenerators (a := a) A representative offset)).map
        (functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)) ≤
      restrictedExpressionBase (D.snoc R M hRM)
        (restrictedAbelJetGenerators (a := a) A
          (restrictedReclassifiedRepresentative representative i)
          (restrictedReclassifiedOffset
            D R M hRM representative offset i)) := by
  rw [restrictedExpressionBase, AlgHom.map_adjoin]
  apply Algebra.adjoin_mono
  rintro g ⟨f, hf, rfl⟩
  rcases hf with hf | hf
  · exact Or.inl
      (image_restrictedFixedGenerators_reclassifyAt_subset
        D R M hRM i ⟨f, hf, rfl⟩)
  · rcases hf with ⟨⟨k, r⟩, rfl⟩
    by_cases hk : representative k = i
    · let kp : RestrictedPivotOffsetIndex representative i := ⟨k, hk⟩
      rw [hA.precomp_restrictedAbelJet_reclassified_pivot
        D R M hRM representative offset i hDomain kp r]
      refine Or.inl (Or.inr ⟨
        hA.restrictedReclassifiedPivotJetCoefficient
          D R M hRM representative offset i hDomain kp r, ?_⟩)
      rfl
    · let kr : RestrictedRetainedOffsetIndex representative i := ⟨k, hk⟩
      rw [precomp_restrictedAbelJet_reclassified_retained
        A D R M hRM representative offset i kr r]
      exact Or.inr ⟨(kr, r), rfl⟩

end AbelFormalization
