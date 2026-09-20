import Mathlib.Data.Set.Basic

/-!
# The linear algebra step in Wilkie's regular coordinate slices

Theorem 2.8 supplies a value at which `(F, coordinate)` is regular.  At a
point of that coordinate slice, the derivative of the sliced map is the
restriction of `dF` to the zero-coordinate hyperplane.  The lemma below
proves the surjectivity implication once the insertion map and its
hyperplane-range identity have been supplied.  It does not assert the
finite exceptional-value theorem, the coordinate chain rule, or any
definability property.
-/

namespace AbelFormalization

set_option autoImplicit false

/-- If the augmented map `(D, q)` is surjective and the image of a slice
insertion contains the `q = q₀` directions, then `D` restricted to that
slice is surjective.  For a coordinate slice, `q₀` is zero and `D` is the
derivative of `F` at the inserted point. -/
theorem surjective_restricted_map_of_surjective_augmented
    {E E' K Q : Type*} (D : E → K) (q : E → Q) (insert : E' → E)
    (q₀ : Q)
    (haug : Function.Surjective (fun v : E ↦ (D v, q v)))
    (hker : ∀ v : E, q v = q₀ → ∃ w : E', insert w = v) :
    Function.Surjective (fun w : E' ↦ D (insert w)) := by
  intro target
  obtain ⟨v, hv⟩ := haug (target, q₀)
  obtain ⟨w, hw⟩ := hker v (congrArg Prod.snd hv)
  refine ⟨w, ?_⟩
  change D (insert w) = target
  rw [hw]
  exact congrArg Prod.fst hv

end AbelFormalization
