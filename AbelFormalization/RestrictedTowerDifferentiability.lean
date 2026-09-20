import AbelFormalization.RestrictedAdjunctionJacobianTowerExpression

/-!
# Differentiability supplied by restricted Abel towers

Directional closure records full differentiability at every point of the
common Abel-jet domain.  These lemmas expose that fact directly and apply it
to the product-coordinate system used in exponential adjunction.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Membership in an Abel tower level gives differentiability at every point
of the common positive jet domain. -/
theorem IsAbel.differentiableAt_of_mem_restrictedAbelTower_level
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    {j : ℕ} {f : RestrictedSource m p a → ℝ}
    (hf : f ∈ T.level j)
    {x : RestrictedSource m p a}
    (hx : x ∈ restrictedAbelJetDomain D representative offset) :
    DifferentiableAt ℝ f x := by
  obtain ⟨df, hdf, hderiv⟩ :=
    hA.restrictedAbelTower_directionallyClosedOn_level
      representative offset T (0 : RestrictedSource m p a) j f hf
  exact (hderiv x hx).1

/-- Appending one arbitrary auxiliary coordinate preserves the Abel-jet
domain because the shifted arguments do not depend on auxiliary variables. -/
theorem restrictedSourceAppendAuxOne_mem_restrictedAbelJetDomain
    {m p a : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin m}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    {x : RestrictedSource m p a}
    (hx : x ∈ restrictedAbelJetDomain D representative offset)
    (Y : ℝ) :
    restrictedSourceAppendAuxOne x Y ∈
      restrictedAbelJetDomain (a := a + 1) D representative offset := by
  constructor
  · exact hx.1
  · intro t
    exact hx.2 t

/-- A tuple of lower-level expressions becomes differentiable in the split
`(x,Y)` coordinates at every point over the common jet domain. -/
theorem IsAbel.differentiableAt_restrictedSystemProductForm_of_mem
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    {j : ℕ} (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (hH : ∀ k, H k ∈
      (T.extendAuxAbel A representative offset 1).level j)
    {x : RestrictedSource m p a}
    (hx : x ∈ restrictedAbelJetDomain D representative offset)
    (Y : ℝ) :
    DifferentiableAt ℝ (restrictedSystemProductForm H) (x, Y) := by
  apply differentiableAt_pi.mpr
  intro k
  have hy := restrictedSourceAppendAuxOne_mem_restrictedAbelJetDomain hx Y
  have hk := hA.differentiableAt_of_mem_restrictedAbelTower_level
    representative offset (T.extendAuxAbel A representative offset 1)
    (hH k) hy
  have hcomp := hk.comp (x, Y)
    (restrictedSourceAuxOneContinuousLinearEquiv (m := m) (p := p)
      (a := a)).symm.differentiableAt
  change DifferentiableAt ℝ
    (H k ∘ (restrictedSourceAuxOneContinuousLinearEquiv
      (m := m) (p := p) (a := a)).symm) (x, Y)
  exact hcomp

end AbelFormalization
