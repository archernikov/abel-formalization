import AbelFormalization.RestrictedBoundedReclassificationOffsets
import AbelFormalization.ExponentialTowerPullback

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

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
        (functionPrecompAlgHom (restrictedSourceReclassifyAt i)) ≤
      restrictedExpressionBase (D.snoc R M hRM)
        (restrictedAbelJetGenerators (a := a) A
          (restrictedReclassifiedRepresentative representative i)
          (restrictedReclassifiedOffset D R M hRM representative offset i)) := by
  rw [restrictedExpressionBase, AlgHom.map_adjoin]
  apply Algebra.adjoin_mono
  rintro g ⟨f, hf, rfl⟩
  rcases hf with hf | hf
  · rcases hf with (hf | hf)
    · rcases hf with hf | hf
      · obtain ⟨j, rfl⟩ := hf
        refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
        · have hfun :
              functionPrecompAlgHom (restrictedSourceReclassifyAt (p := p) (a := a) i)
                  (restrictedSCoordinate (p := p) (a := a) i) =
                restrictedWCoordinate (m := m) (a := a) (Fin.last p) := by
            funext x
            simp [restrictedSCoordinate, restrictedWCoordinate]
          rw [hfun]
          exact Or.inl (Or.inr
            ⟨⟨fun w ↦ w (Fin.last p),
                (D.snoc R M hRM).analyticNearClosedBox_apply (Fin.last p)⟩, rfl⟩)
        · have hfun :
              functionPrecompAlgHom (restrictedSourceReclassifyAt (p := p) (a := a) i)
                  (restrictedSCoordinate (p := p) (a := a) (i.succAbove k)) =
                restrictedSCoordinate (p := p + 1) (a := a) k := by
            funext x
            simp [restrictedSCoordinate]
          rw [hfun]
          exact Or.inl (Or.inl ⟨k, rfl⟩)
      · obtain ⟨k, rfl⟩ := hf
        have hfun :
            functionPrecompAlgHom (restrictedSourceReclassifyAt (p := p) (a := a) i)
                (restrictedAuxCoordinate (m := m + 1) (p := p) k) =
              restrictedAuxCoordinate (m := m) (p := p + 1) k := by
          funext x
          simp [restrictedAuxCoordinate]
        rw [hfun]
        exact Or.inl (Or.inr ⟨k, rfl⟩)
    · obtain ⟨f, rfl⟩ := hf
      have hfun :
          functionPrecompAlgHom (restrictedSourceReclassifyAt (p := p) (a := a) i)
              (restrictedBoxCoefficientPullback (m := m + 1) (a := a)
                (f : RestrictedBoxSpace p → ℝ)) =
            restrictedBoxCoefficientPullback (m := m) (a := a)
              (D.pullbackSnoc R M hRM f : RestrictedBoxSpace (p + 1) → ℝ) := by
        funext x
        rfl
      rw [hfun]
      exact Or.inr ⟨D.pullbackSnoc R M hRM f, rfl⟩
  · obtain ⟨⟨k, r⟩, rfl⟩ := hf
    by_cases hki : representative k = i
    · let pk : RestrictedPivotOffsetIndex representative i := ⟨k, hki⟩
      rw [hA.precomp_restrictedAbelJet_reclassified_pivot
        D R M hRM representative offset i hDomain pk r]
      exact Or.inl (Or.inr
        ⟨hA.restrictedReclassifiedPivotJetCoefficient
            D R M hRM representative offset i hDomain pk r, rfl⟩)
    · let rk : RestrictedRetainedOffsetIndex representative i := ⟨k, hki⟩
      rw [precomp_restrictedAbelJet_reclassified_retained
        A D R M hRM representative offset i rk r]
      exact Or.inr ⟨(rk, r), rfl⟩

end AbelFormalization
