import AbelFormalization.Wilkie28WeakSelectionCompactExtraction

open Set
open AbelFormalization

#check Homeomorph.isClosedMap
#check Homeomorph.image_interior
#check ContinuousLinearEquiv.isClosedMap
#check ContinuousLinearEquiv.differentiable
#check ContinuousLinearEquiv.differentiableAt
#check ContinuousLinearMap.differentiable
#check DifferentiableAt.comp
#check DifferentiableAt.congr_of_eventuallyEq
#check DifferentiableAt.congr
#check ContinuousLinearEquiv.symm_apply_apply
#check realEuclideanOneEquivReal
#check charbonnelClosure_projection

example {U : Set ℝ} (hU : IsOpen U) :
    IsOpen {x : RealEuclidean 1 | x 0 ∈ U} := by
  exact hU.preimage (continuous_apply 0)

example {A : Set (RealEuclidean 1)} (hA : IsClosed A) :
    IsClosed (realEuclideanOneEquivReal '' A) := by
  exact realEuclideanOneEquivReal.toHomeomorph.isClosedMap A hA

example (t : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => realEuclideanOneEquivReal.symm s) t := by
  exact realEuclideanOneEquivReal.symm.differentiable.differentiableAt
