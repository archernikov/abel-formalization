import AbelFormalization.CanonicalDenominatorLift

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Linear form of splitting off the final restricted auxiliary coordinate. -/
def restrictedSourceAuxOneContinuousLinearEquiv {m p a : ℕ} :
    RestrictedSource m p (a + 1) ≃L[ℝ] RestrictedSource m p a × ℝ where
  toFun := restrictedDenominatorProjection
  invFun := fun x ↦ restrictedSourceAppendAuxOne x.1 x.2
  left_inv := restrictedSourceAppendAuxOne_projection
  right_inv := fun x ↦ restrictedDenominatorProjection_appendAuxOne x.1 x.2
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · rfl
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · rfl
    · rfl
  continuous_toFun := continuous_restrictedDenominatorProjection
  continuous_invFun := continuous_restrictedSourceAppendAuxOne

@[simp]
theorem restrictedSourceAuxOneContinuousLinearEquiv_apply {m p a : ℕ}
    (x : RestrictedSource m p (a + 1)) :
    restrictedSourceAuxOneContinuousLinearEquiv x =
      restrictedDenominatorProjection x := rfl

@[simp]
theorem restrictedSourceAuxOneContinuousLinearEquiv_symm_apply {m p a : ℕ}
    (x : RestrictedSource m p a × ℝ) :
    restrictedSourceAuxOneContinuousLinearEquiv.symm x =
      restrictedSourceAppendAuxOne x.1 x.2 := rfl

end AbelFormalization
