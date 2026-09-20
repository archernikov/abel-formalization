import AbelFormalization.RestrictedBoundedReclassificationBase

/-!
# Finite towers after bounded-representative reclassification

Moving one unbounded representative coordinate into the bounded box pulls
back every level of a restricted exponential tower.  The retained Abel jets
remain special generators and the pivot jets become analytic coefficients.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Pull an Abel restricted-expression tower through the source
reclassification which moves coordinate `i` into the bounded box. -/
def RestrictedExpressionTower.reclassifyAt
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin (m + 1)}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (R M : ℝ) (hRM : R < M) (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset) :
    RestrictedExpressionTower (D.snoc R M hRM)
      (restrictedAbelJetGenerators (a := a) A
        (restrictedReclassifiedRepresentative representative i)
        (restrictedReclassifiedOffset D R M hRM representative offset i))
      (ell := ell) :=
  T.pullbackChangeBase (restrictedSourceReclassifyAt i)
    (restrictedExpressionBase (D.snoc R M hRM)
      (restrictedAbelJetGenerators (a := a) A
        (restrictedReclassifiedRepresentative representative i)
        (restrictedReclassifiedOffset D R M hRM representative offset i)))
    (hA.map_restrictedExpressionBase_reclassifyAt_le
      D R M hRM representative offset i hDomain)

/-- Membership in an old tower level is preserved after reclassification
and precomposition. -/
theorem RestrictedExpressionTower.precomp_mem_reclassifyAt_level
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin (m + 1)}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (R M : ℝ) (hRM : R < M) (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    {j : ℕ} {f : RestrictedSource (m + 1) p a → ℝ}
    (hf : f ∈ T.level j) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt i) f ∈
      (T.reclassifyAt hA R M hRM i hDomain).level j :=
  T.precomp_mem_pullbackChangeBase_level
    (restrictedSourceReclassifyAt i)
    (restrictedExpressionBase (D.snoc R M hRM)
      (restrictedAbelJetGenerators (a := a) A
        (restrictedReclassifiedRepresentative representative i)
        (restrictedReclassifiedOffset D R M hRM representative offset i)))
    (hA.map_restrictedExpressionBase_reclassifyAt_le
      D R M hRM representative offset i hDomain) hf

@[simp]
theorem RestrictedExpressionTower.reclassifyAt_generator_apply
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin (m + 1)}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (R M : ℝ) (hRM : R < M) (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (k : Fin ell) (x : RestrictedSource m (p + 1) a) :
    (T.reclassifyAt hA R M hRM i hDomain).generator k x =
      T.generator k (restrictedSourceReclassifyAt i x) :=
  rfl

end AbelFormalization
