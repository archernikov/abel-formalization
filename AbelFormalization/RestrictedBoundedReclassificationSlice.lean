import AbelFormalization.RestrictedRegularZeroReclassification
import AbelFormalization.RestrictedRegularZeroInduction

/-!
# Scratch: the bounded slice in the outer representative induction

If one representative coordinate is bounded above, move that coordinate
into the bounded box.  The resulting base system has one fewer unbounded
representative coordinate, so the outer induction hypothesis applies.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Componentwise base membership for the reindexed equation family. -/
theorem IsAbel.restrictedReclassifiedEquationFamily_mem_base
    {A : ℝ → ℝ} (hA : IsAbel A)
    {ι : Type*}
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (hF : ∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    ∀ k, restrictedReclassifiedEquationFamily i F k ∈
      restrictedExpressionBase (D.snoc R M hRM)
        (restrictedAbelJetGenerators (a := a) A
          (restrictedReclassifiedRepresentative representative i)
          (restrictedReclassifiedOffset
            D R M hRM representative offset i)) := by
  intro k
  change
    functionPrecompAlgHom (restrictedSourceReclassifyAt i)
        (F ((restrictedReclassificationEquationIndexEquiv m p a).symm k)) ∈
      restrictedExpressionBase (D.snoc R M hRM)
        (restrictedAbelJetGenerators (a := a) A
          (restrictedReclassifiedRepresentative representative i)
          (restrictedReclassifiedOffset
            D R M hRM representative offset i))
  apply hA.map_restrictedExpressionBase_reclassifyAt_le
    D R M hRM representative offset i hDomain
  rw [Subalgebra.mem_map]
  exact ⟨F ((restrictedReclassificationEquationIndexEquiv m p a).symm k),
    hF _, rfl⟩

/-- The bounded-coordinate slice of an `(m+1)`-representative base system
has finitely many regular zeros if the base assertion is known for `m`
representatives. -/
theorem IsAbel.finite_regularZeroSet_base_slice_of_lowerRepresentativeCount
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (houter : RestrictedBaseRegularZeroFiniteForRepresentativeCount A m)
    {ι : Type} [Finite ι] {p a : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R M : ℝ) (hRM : R < M) (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (hF : ∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    (regularZeroSet
        (restrictedBaseOpenDomain D R ∩ {x | x.1.1 i < M})
        (constraintMap F)).Finite := by
  let representative' : RestrictedRetainedOffsetIndex representative i → Fin m :=
    restrictedReclassifiedRepresentative representative i
  let offset' : RestrictedRetainedOffsetIndex representative i →
      RestrictedBox.analyticNearClosedBoxSubalgebra (D.snoc R M hRM) :=
    restrictedReclassifiedOffset D R M hRM representative offset i
  have hDomain' :
      restrictedBaseClosedDomain (m := m) (a := a)
          (D.snoc R M hRM) R ⊆
        restrictedAbelJetDomain (a := a) (D.snoc R M hRM)
          representative' offset' := by
    exact restrictedBaseClosedDomain_subset_reclassifiedAbelJetDomain
      D R M hRM representative offset i hDomain
  have hF' : ∀ k, restrictedReclassifiedEquationFamily i F k ∈
      restrictedExpressionBase (D.snoc R M hRM)
        (restrictedAbelJetGenerators (a := a) A representative' offset') := by
    exact hA.restrictedReclassifiedEquationFamily_mem_base
      D R M hRM representative offset i hDomain F hF
  have hfinite' :
      (regularZeroSet (restrictedBaseOpenDomain (D.snoc R M hRM) R)
        (constraintMap (restrictedReclassifiedEquationFamily i F))).Finite := by
    exact houter (D.snoc R M hRM) representative' offset'
      R hDomain' (restrictedReclassifiedEquationFamily i F) hF'
  exact (finite_regularZeroSet_reclassifyAt_slice_iff
    D R M hRM i F).mp hfinite'

end AbelFormalization
