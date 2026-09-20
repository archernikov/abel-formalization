import AbelFormalization.RestrictedExponentialAdjunctionStep
import AbelFormalization.RestrictedAdjunctionCanonicalMorse
import AbelFormalization.RestrictedAdjunctionGenericMorse
import AbelFormalization.RestrictedAdjunctionRegularArc

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- The canonical exponential-adjunction step.  The Morse center is supplied
by parametric Sard, and normalized cofactor flow supplies the regular arcs. -/
theorem IsAbel.finite_regularZeroSet_level_succ_of_canonicalMorse
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (i : Fin ell) (R : ℝ)
    (F : Fin ((m + p) + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ k, F k ∈ T.level (i.val + 1))
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    (hregularFinite : ∀ G :
        RestrictedSource m p ((a + 1) + 1) →
          Fin ((((m + p) + a) + 1) + 1) → ℝ,
      (∀ k, (fun x ↦ G x k) ∈
        ((T.extendAuxAbel A representative offset 1).extendAuxAbel
          A representative offset 1).level i.val) →
      (regularZeroSet
        (restrictedBaseOpenDomain (m := m) (a := (a + 1) + 1) D R)
        G).Finite) :
    (regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)).Finite := by
  apply hA.finite_regularZeroSet_level_succ_of_adjunctionGeometry
    representative offset T i R F (restrictedSourceBasis m p a)
      hF hDomain
  intro H J hH hJ hJeq
  obtain ⟨center, hMorse⟩ :=
    hA.exists_restrictedAdjunctionMorseCenter
      representative offset (T.extendAuxAbel A representative offset 1)
        i.val R H J (T.exponent i) hH hJ hJeq hDomain
  refine ⟨?_, ?_⟩
  · exact hA.finite_connectedComponents_restrictedAdjunctionClosedCurve_of_canonical_morse
      representative offset (T.extendAuxAbel A representative offset 1)
        i.val R H J (T.exponent i) center hH hJ hJeq hDomain
        hregularFinite hMorse
  · intro x y hy hxy
    exact hA.regularArcIn_restrictedExponentialAdjunctionClosedCurve_of_mem_connectedComponent
      representative offset T i R H J hH hJ hJeq hDomain x y hy hxy

end AbelFormalization
