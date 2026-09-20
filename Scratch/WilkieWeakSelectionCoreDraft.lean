import AbelFormalization.Wilkie28ExceptionalMembership
import AbelFormalization.CharbonnelClosureInteriorRegularity

/-!
# The algebraic input to Wilkie weak selection in the singular-value slice

Wilkie's Theorem 2.3 applies to a member `A` of the expanded weak family and
an incidence member `B` whose projection covers `A`.  For the singular values
of `(F,f)` with `F = a`, the maintained sum-of-squares residual provides an
especially strong incidence set: it is itself a closed literal zero set.

This source-only draft proves that precise input package.  Theorem 2.3 still
requires the separate weak-selection argument of Maxwell [10], and Theorem
2.4 requires his almost-everywhere smoothness argument.  Wilkie's 1999 paper
states those results but refers to [10] for their proofs.

This file is deliberately uncompiled.  Every declaration has a proof.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The parameter/witness relation for the singular values of the augmented
map.  Its zero equation simultaneously expresses `F x = a`, `f x = b`, and
the vanishing of all maximal augmented Jacobian minors. -/
def wilkie28WeakSelectionIncidence {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) :
    Set (RealEuclidean (1 + n)) :=
  {w | wilkie28ExceptionalResidual F f a w = 0}

/-- The source-shaped set-family and full-fiber input to Wilkie 2.3 for the
singular-value relation.  In particular, each parameter in the exceptional
slice has a singular witness in the incidence set.  This theorem makes no
selection or smoothness claim. -/
theorem wilkie28WeakSelectionIncidence_sourceData
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    IsClosed (wilkie28WeakSelectionIncidence F f a) ∧
      wilkie28WeakSelectionIncidence F f a ∈
        charbonnelClosure (literalZeroSetFamily G) (1 + n) ∧
      wilkie28FlatExceptionalSlice F f a ∈
        charbonnelClosure (literalZeroSetFamily G) 1 ∧
      wilkie28FlatExceptionalSlice F f a =
        realEuclideanExistentialProjection
          (wilkie28WeakSelectionIncidence F f a) := by
  let B : Set (RealEuclidean (1 + n)) :=
    wilkie28WeakSelectionIncidence F f a
  have hresidual : wilkie28ExceptionalResidual F f a ∈ G (1 + n) :=
    wilkie28ExceptionalResidual_mem hG hderiv F f a hF hf
  have hBbase : B ∈ literalZeroSetFamily G (1 + n) := by
    change IsLiteralZeroSet G B
    exact ⟨wilkie28ExceptionalResidual F f a, hresidual, rfl⟩
  have hBclosed : IsClosed B :=
    (literalZeroSetFamily_isClosed hsmooth) (by omega) hBbase
  have hBmem : B ∈
      charbonnelClosure (literalZeroSetFamily G) (1 + n) :=
    mem_charbonnelClosure_of_mem (by omega) hBbase
  have hprojection : wilkie28FlatExceptionalSlice F f a =
      realEuclideanExistentialProjection B := by
    ext b
    simp only [wilkie28FlatExceptionalSlice,
      realEuclideanExistentialProjection,
      B, wilkie28WeakSelectionIncidence, Set.mem_setOf_eq]
    exact exists_congr (fun x ↦
      (wilkie28ExceptionalResidual_append_eq_zero_iff F f a b x).symm)
  have hAmem : wilkie28FlatExceptionalSlice F f a ∈
      charbonnelClosure (literalZeroSetFamily G) 1 := by
    rw [hprojection]
    exact charbonnelClosure_projection (by omega) hBmem
  exact ⟨hBclosed, hBmem, hAmem, hprojection⟩

end AbelFormalization
