import AbelFormalization.CharbonnelRelativeCoverComplement
import AbelFormalization.CharbonnelComplementPipeline

/-!
# Bounded-coordinate complement assembly

Wilkie proves cell decomposition after transporting a closed WS6 lift to the
open cube.  This module packages the exact relative cover needed after that
transport and proves that it suffices for complement closure.  The pullback
uses the semialgebraic bounded-coordinate incidence, so no complement closure
is used in the reduction itself.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The bounded form of the remaining higher-dimensional cell theorem.  For
a closed WS6 lift `B`, it asks only for a relative compatible cover of the
open visible cube, with target the bounded image of the visible projection. -/
def WilkieBoundedProjectedClosedLiftCellCoverProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 1 < n →
    ∀ {B : Set (RealEuclidean (n + q))}, IsClosed B → B ∈ C (n + q) →
      Nonempty (CharbonnelFiniteCompatibleRelativeCellCover C
        (wilkieOpenCube n)
        (wilkieBoundedImage (realEuclideanExistentialProjection B)))

/-- Bounded projected closed-lift covers prove positive-arity complement
closure for a Charbonnel closure. -/
theorem charbonnelClosure_compl_mem_of_boundedProjectedClosedLiftCellCovers
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hcovers : WilkieBoundedProjectedClosedLiftCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) :
    Aᶜ ∈ charbonnelClosure S n := by
  by_cases hone : n = 1
  · subst n
    exact hC.compl_mem_one hA
  · have htwo : 1 < n := by omega
    obtain ⟨q, B, hBclosed, hBmem, hprojection⟩ :=
      hC.ws6_closedLift hn hA
    obtain ⟨cover⟩ := hcovers htwo hBclosed hBmem
    have hbounded :
        wilkieOpenCube n \
            wilkieBoundedImage (realEuclideanExistentialProjection B) ∈
          charbonnelClosure S n :=
      wilkieOpenCube_sdiff_mem_charbonnelClosure
        hC.toPositiveArityWeakSetStructure hn cover
    have hpullback :
        (realEuclideanExistentialProjection B)ᶜ ∈
          charbonnelClosure S n :=
      compl_mem_charbonnelClosure_of_openCube_sdiff_boundedImage_mem
        hC.toPositiveArityWeakSetStructure hn hbounded
    rw [hprojection]
    exact hpullback

/-- Source-facing bounded cell assembly: the Section 3 boundary theorem is
allowed as input exactly as in the existing closed-boundary assembly, while
the output is the smaller cube-relative projected-lift cover property. -/
def CharbonnelBoundedClosedBoundaryCellCoverAssembly
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  CharbonnelClosedBoundaryCarrierProperty G →
    WilkieBoundedProjectedClosedLiftCellCoverProperty
      (charbonnelClosure (literalZeroSetFamily G))

/-- The bounded-coordinate cover assembly discharges the older abstract
closed-boundary complement premise. -/
theorem charbonnelClosedBoundaryComplementAssembly_of_boundedCellCovers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly G) :
    CharbonnelClosedBoundaryComplementAssembly G := by
  intro hboundary n hn A hA
  exact charbonnelClosure_compl_mem_of_boundedProjectedClosedLiftCellCovers
    (literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF)
    (hcells hboundary) hn hA

end AbelFormalization
