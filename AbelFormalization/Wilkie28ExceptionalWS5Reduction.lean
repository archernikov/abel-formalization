import AbelFormalization.CharbonnelSection5ElementaryInputs
import AbelFormalization.Wilkie28ExceptionalMathlibOnly

/-!
# Wilkie 2.8: WS5 reduction for a regular fiber's exceptional values

Theorem 2.8 needs the exceptional unary set to belong to the expanded weak
family.  This file takes that membership and the smooth singular-witness
selection explicitly.  It applies the maintained WS5 unary decomposition and
then the mathlib-only differential contradiction to obtain finiteness.
Neither family membership nor selection is manufactured by this reduction.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- WS5 makes any empty-interior unary weak-family member finite, after
identifying `ℝ¹` with its unique coordinate. -/
theorem PositiveArityOMinimalWeakSetStructure.finite_unary_member_of_empty_interior
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (B : Set ℝ)
    (hBmem : {v : RealEuclidean 1 | v 0 ∈ B} ∈ C 1)
    (hBempty : interior B = ∅) : B.Finite := by
  have hpieces := hC.coordinateImage_unaryPieceDecomposable hBmem
  have hImage :
      realEuclideanOneCoordinateImage
        {v : RealEuclidean 1 | v 0 ∈ B} = B := by
    ext x
    simp only [realEuclideanOneCoordinateImage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨fun _ ↦ x, hx, rfl⟩
  rw [hImage] at hpieces
  exact hpieces.finite_of_interior_eq_empty hBempty

/-- Wilkie's finite exceptional-coordinate-value conclusion from the exact
two source bridges still absent in the maintained library: membership of the
singular-value slice in the expanded weak family, and smooth weak selection
of singular witnesses.  All regular-fiber and WS5 consequences are proved. -/
theorem wilkie28_exceptionalCoordinateValues_finite_of_WS5_and_selection
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K)
    (hFdiff : ∀ x : E, DifferentiableAt ℝ F x)
    (hfdiff : ∀ x : E, DifferentiableAt ℝ f x)
    (hregular : ∀ x : E, F x = a →
      Function.Surjective (fderiv ℝ F x))
    (hBmem :
      {v : RealEuclidean 1 |
        v 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet F f a} ∈ C 1)
    (hselection : Wilkie28MathlibOnly.SmoothSingularWitnessSelection F f a) :
    (Wilkie28MathlibOnly.exceptionalParameterSet F f a).Finite := by
  exact Wilkie28MathlibOnly.exceptionalParameterSet_finite_of_tameness_and_smooth_selection
    F f a hFdiff hfdiff hregular
    (fun hempty ↦ hC.finite_unary_member_of_empty_interior
      (Wilkie28MathlibOnly.exceptionalParameterSet F f a) hBmem hempty)
    hselection

end AbelFormalization
