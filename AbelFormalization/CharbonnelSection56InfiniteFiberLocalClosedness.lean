import AbelFormalization.CharbonnelSection56InfiniteFiberLocus
import AbelFormalization.MaxwellMeagreClosureFamilyEquivalence

/-!
# Repair of Charbonnel 5.5 by closing the infinite-fibre locus

Charbonnel 5.5 asserts that the base points with an infinite vertical fibre
form a locally closed set.  The printed justification projects an
open-in-compact ordered-tuple incidence.  Such a projection need not be
locally closed, and the asserted statement is false even for compact
semialgebraic families.

The compact argument needs only a *locally closed exceptional base* outside
which all fibres are finite.  The closure of the infinite-fibre locus is a
canonical such base.  It is closed, remains in a Charbonnel closure, and its
interior lifts to the compact relation once the Maxwell--Servi
closure-interior regularity already used by the main pipeline is available.

Thus this file removes the spurious local-closedness premise from
Charbonnel 5.4--5.6 without adding a new source assumption.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Interior lift from closure regularity -/

/-- Closure-interior regularity turns interior of the closure of the
infinite-fibre locus into interior of the locus itself.  The rational-slab
argument already proved in `CharbonnelSection56InfiniteFiberLocus` then
lifts that interior to the original closed relation. -/
theorem
    charbonnelInfiniteVerticalFiberLocus_closure_interior_lift_of_ws5_and_regular
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + 1))}
    (hSclosed : IsClosed S)
    (hSmem : S ∈ charbonnelClosure S0 (n + 1))
    (hlocusClosure :
      (interior (closure (charbonnelInfiniteVerticalFiberLocus S))).Nonempty) :
    (interior S).Nonempty := by
  have hlocusMem : charbonnelInfiniteVerticalFiberLocus S ∈
      charbonnelClosure S0 n :=
    charbonnelInfiniteVerticalFiberLocus_mem_charbonnelClosure_of_ws5
      hC hn hSmem
  have hlocusInterior :
      (interior (charbonnelInfiniteVerticalFiberLocus S)).Nonempty := by
    by_contra hnot
    have hempty :
        interior (charbonnelInfiniteVerticalFiberLocus S) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnot
    have hclosureEmpty :
        interior (closure (charbonnelInfiniteVerticalFiberLocus S)) = ∅ :=
      hregularity hn hlocusMem hempty
    rw [hclosureEmpty] at hlocusClosure
    exact hlocusClosure.ne_empty rfl
  exact charbonnelInfiniteVerticalFiberLocus_interior_lift_of_ws5
    hC hn hSclosed hSmem hlocusInterior

/-! ## The closed exceptional base -/

/-- The closure of the infinite-fibre locus is the corrected exceptional
base for a compact member of a Charbonnel closure. -/
noncomputable def
    charbonnelCompactExceptionalFiberBase_of_infiniteFiberLocusClosure
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    (S : Set (RealEuclidean (n + 1)))
    (hScompact : IsCompact S)
    (hSmem : S ∈ charbonnelClosure S0 (n + 1)) :
    CharbonnelCompactExceptionalFiberBase (charbonnelClosure S0) S where
  base := closure (charbonnelInfiniteVerticalFiberLocus S)
  base_mem := charbonnelClosure_topologicalClosure
    (charbonnelInfiniteVerticalFiberLocus_mem_charbonnelClosure_of_ws5
      hC hn hSmem)
  base_locallyClosed := isClosed_closure.isLocallyClosed
  fiber_finite_off := by
    intro x hx
    apply charbonnelVerticalFiber_finite_of_not_mem_infiniteLocus
    intro hxInfinite
    exact hx (subset_closure hxInfinite)
  interior_lift :=
    charbonnelInfiniteVerticalFiberLocus_closure_interior_lift_of_ws5_and_regular
      hC hregularity hn hScompact.isClosed hSmem

/-- Consequently the complete compact-fibre reduction follows from the
closure-interior regularity already required by the main Charbonnel
pipeline. -/
theorem
    charbonnelSection56CompactFiberReduction_of_closureInteriorRegularity
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0)) :
    CharbonnelSection56CompactFiberReduction (charbonnelClosure S0) := by
  intro n hn S hScompact hSmem
  exact ⟨charbonnelCompactExceptionalFiberBase_of_infiniteFiberLocusClosure
    hC hregularity hn S hScompact hSmem⟩

/-- Maxwell's family-geometric meagre-selection premise supplies the same
compact reduction through its already proved equivalence with
closure-interior regularity. -/
theorem charbonnelSection56CompactFiberReduction_of_maxwellMeagreSelection
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure S0)) :
    CharbonnelSection56CompactFiberReduction (charbonnelClosure S0) :=
  charbonnelSection56CompactFiberReduction_of_closureInteriorRegularity hC
    ((hasMaxwellMeagreClosureComponentSelection_iff_closureInteriorRegularity
      hC).mp hselection)

/-! ## Section 5 adapters -/

/-- The corrected closed exceptional base and the bounded graph reduction
reconstruct the complete Section 5 analytic step. -/
theorem
    charbonnelSection5AnalyticStep_of_closureInteriorRegularity_and_graphReduction
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure S0)) :
    CharbonnelSection5AnalyticStep (charbonnelClosure S0) :=
  charbonnelSection5AnalyticStep_of_fiberAndGraphReductions hmem
    (charbonnelSection56CompactFiberReduction_of_closureInteriorRegularity
      hC hregularity)
    hbounded

/-- Source-shaped variant using Maxwell meagre selection directly. -/
theorem
    charbonnelSection5AnalyticStep_of_maxwellMeagreSelection_and_graphReduction
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure S0))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure S0)) :
    CharbonnelSection5AnalyticStep (charbonnelClosure S0) :=
  charbonnelSection5AnalyticStep_of_closureInteriorRegularity_and_graphReduction
    hC hmem
    ((hasMaxwellMeagreClosureComponentSelection_iff_closureInteriorRegularity
      hC).mp hselection)
    hbounded

/-- Literal-zero specialization: the compact part of 5.4--5.6 now uses the
same Maxwell premise already present in the final source pipeline. -/
theorem
    literalZeroSet_charbonnelClosure_section5AnalyticStep_of_maxwellMeagreSelection_and_graphReduction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  exact
    charbonnelSection5AnalyticStep_of_maxwellMeagreSelection_and_graphReduction
      hC
      (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
      hselection hbounded

end AbelFormalization
