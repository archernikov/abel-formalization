import AbelFormalization.Wilkie28WeakSelectionIncidence
import AbelFormalization.CharbonnelSection5ElementaryInputs
import AbelFormalization.CharbonnelApproximationTraceSmallness
import AbelFormalization.CharbonnelClosureInteriorRegularity

/-!
# Compact/Baire reduction for Wilkie weak selection

If the exceptional unary set has interior, one bounded compact truncation of
its closed singular-witness incidence already has a visible projection with
interior.  The truncation and its projection remain in the same Charbonnel
closure.  The remaining Maxwell step is local graph extraction from this
compact family member.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A countable closed exhaustion with interior has a member with interior. -/
theorem exists_nonempty_interior_of_iUnion_of_closed
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    (F : ℕ → Set X) (hclosed : ∀ m, IsClosed (F m))
    (hinterior : (interior (⋃ m, F m)).Nonempty) :
    ∃ m, (interior (F m)).Nonempty := by
  by_contra hnone
  have hempty : ∀ m, interior (F m) = ∅ := by
    intro m
    apply not_nonempty_iff_eq_empty.mp
    intro hm
    exact hnone ⟨m, hm⟩
  rw [interior_iUnion_eq_empty_of_closed hclosed hempty] at hinterior
  simpa using hinterior

/-- The compact Baire reduction applied to the literal singular-witness
incidence used in Wilkie 2.8. -/
theorem wilkie28_exists_compact_incidence_projection_with_interior
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hinterior :
      (interior (wilkie28FlatExceptionalSlice F f a)).Nonempty) :
    ∃ m : ℕ,
      IsCompact (charbonnelCompactTruncation
        (wilkie28WeakSelectionIncidence F f a) m) ∧
      maxwellClosedLiftProjectionTruncation
          (wilkie28WeakSelectionIncidence F f a) m ∈
        charbonnelClosure (literalZeroSetFamily G) 1 ∧
      (interior (maxwellClosedLiftProjectionTruncation
        (wilkie28WeakSelectionIncidence F f a) m)).Nonempty ∧
      maxwellClosedLiftProjectionTruncation
          (wilkie28WeakSelectionIncidence F f a) m ⊆
        wilkie28FlatExceptionalSlice F f a := by
  obtain ⟨hBclosed, hBmem, _hAmem, hprojection⟩ :=
    wilkie28WeakSelectionIncidence_sourceData
      hG hsmooth hderiv F f a hF hf
  let B := wilkie28WeakSelectionIncidence F f a
  let P : ℕ → Set (RealEuclidean 1) :=
    maxwellClosedLiftProjectionTruncation B
  have hclosedP : ∀ m, IsClosed (P m) := by
    intro m
    exact (maxwellClosedLiftProjectionTruncation_isCompact hBclosed m).isClosed
  have hUnion : ⋃ m, P m = wilkie28FlatExceptionalSlice F f a := by
    rw [show (⋃ m, P m) = realEuclideanExistentialProjection B from
      iUnion_maxwellClosedLiftProjectionTruncation B]
    exact hprojection.symm
  have hinteriorUnion : (interior (⋃ m, P m)).Nonempty := by
    rw [hUnion]
    exact hinterior
  obtain ⟨m, hmInterior⟩ :=
    exists_nonempty_interior_of_iUnion_of_closed P hclosedP hinteriorUnion
  have htruncMem : charbonnelCompactTruncation B m ∈
      charbonnelClosure (literalZeroSetFamily G) (1 + n) :=
    literalZeroSet_charbonnelClosure_compactTruncationMembership
      hG hsmooth (by omega) hBmem m
  have hprojectionMem : P m ∈
      charbonnelClosure (literalZeroSetFamily G) 1 := by
    exact charbonnelClosure_projection (by omega) htruncMem
  refine ⟨m, charbonnelCompactTruncation_isCompact hBclosed m,
    hprojectionMem, hmInterior, ?_⟩
  rw [← hUnion]
  exact subset_iUnion P m

end AbelFormalization
