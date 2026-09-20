import AbelFormalization.Wilkie28ExceptionalMembership
import AbelFormalization.Wilkie28ExceptionalWS5Reduction

/-!
# Wilkie 2.8 exceptional values: the family and WS5 steps

The exceptional unary set belongs to the literal-zero Charbonnel closure by
the sum-of-squares projection description.  WS5 then reduces its finiteness
to the smooth singular-witness selection used in Wilkie's proof.  That
selection remains an explicit premise here.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The exceptional-value membership and unary-tameness premises of Wilkie
2.8 follow from the geometric derivative-closed family and WS5.  The
smooth singular-witness selector is the precise remaining source input. -/
theorem wilkie28_exceptionalCoordinateValues_finite_of_family_WS5_selection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hregular : ∀ x : RealEuclidean n, F x = a →
      Function.Surjective (fderiv ℝ F x))
    (hselection : Wilkie28MathlibOnly.SmoothSingularWitnessSelection F f a) :
    (Wilkie28MathlibOnly.exceptionalParameterSet F f a).Finite := by
  have hFdiff : ∀ x : RealEuclidean n, DifferentiableAt ℝ F x := by
    intro x
    rw [differentiableAt_pi]
    intro i
    exact ((hsmooth n (fun y ↦ F y i) (hF i)).differentiable
      (by simp)).differentiableAt
  have hfdiff : ∀ x : RealEuclidean n, DifferentiableAt ℝ f x := by
    intro x
    exact ((hsmooth n f hf).differentiable (by simp)).differentiableAt
  exact wilkie28_exceptionalCoordinateValues_finite_of_WS5_and_selection
    hC F f a hFdiff hfdiff hregular
    (wilkie28_exceptionalParameterSet_mem_literalZeroCharbonnel
      hG hsmooth hderiv F f a hF hf)
    hselection

end AbelFormalization
