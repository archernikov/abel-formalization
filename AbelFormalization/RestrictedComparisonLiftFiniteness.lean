import AbelFormalization.RestrictedComparisonFiniteness

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

theorem finite_openComparisonZero_of_finite_closedComparisonZero
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J h : RestrictedSource m p a → ℝ)
    (hclosed : ({x : restrictedClosedDenominatorLocus H u
        (boundaryDenominator J u) |
      h (restrictedSourceDropAux 1 x) = 0} :
        Set (restrictedClosedDenominatorLocus H u
          (boundaryDenominator J u))).Finite) :
    ({x : RestrictedSource m p a |
      x ∈ restrictedOpenDenominatorLocus H u J ∧ h x = 0} :
        Set (RestrictedSource m p a)).Finite := by
  rw [← Set.finite_coe_iff] at hclosed ⊢
  let lift :
      {x : RestrictedSource m p a |
        x ∈ restrictedOpenDenominatorLocus H u J ∧ h x = 0} →
      {x : restrictedClosedDenominatorLocus H u (boundaryDenominator J u) |
        h (restrictedSourceDropAux 1 x) = 0} :=
    fun x ↦ ⟨restrictedCanonicalDenominatorLift H u J
      ⟨x, x.property.1⟩, by
        have hdrop := congrArg Subtype.val
          (restrictedCanonicalDenominatorDrop_lift H u J ⟨x, x.property.1⟩)
        change restrictedSourceDropAux 1
          (restrictedCanonicalDenominatorLift H u J ⟨x, x.property.1⟩) =
            (x : RestrictedSource m p a) at hdrop
        change h (restrictedSourceDropAux 1
          (restrictedCanonicalDenominatorLift H u J ⟨x, x.property.1⟩)) = 0
        rw [hdrop]
        exact x.property.2⟩
  apply Finite.of_injective lift
  intro x y hxy
  apply Subtype.ext
  have hlift : restrictedCanonicalDenominatorLift H u J
      ⟨x, x.property.1⟩ =
      restrictedCanonicalDenominatorLift H u J ⟨y, y.property.1⟩ :=
    congrArg Subtype.val hxy
  have hdrop := congrArg (restrictedCanonicalDenominatorDrop H u J) hlift
  rw [restrictedCanonicalDenominatorDrop_lift,
    restrictedCanonicalDenominatorDrop_lift] at hdrop
  exact congrArg
    (fun z : restrictedOpenDenominatorLocus H u J ↦
      (z : RestrictedSource m p a)) hdrop

theorem finite_regularZeroSet_of_equiv_openComparisonZero
    {X Y : Type*} {Z : Set X} {V : Set Y}
    (e : Nonempty (Z ≃ V)) (hV : V.Finite) : Z.Finite := by
  rw [← Set.finite_coe_iff] at hV ⊢
  obtain ⟨e⟩ := e
  exact Finite.of_injective e e.injective

end AbelFormalization
