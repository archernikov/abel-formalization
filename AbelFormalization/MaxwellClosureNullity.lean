import AbelFormalization.CharbonnelClosureInteriorRegularity
import AbelFormalization.CharbonnelComplementPipeline
import AbelFormalization.MaxwellCompactComponentMembership

/-!
# Maxwell closure and nullity induction

Figueiredo's Lemmas 2.1.16--2.1.17, following Maxwell, prove two
different assertions by induction on the ambient dimension.

* An empty-interior member is Lebesgue null.
* The closure of an empty-interior member still has empty interior.

The one-dimensional bases and all of the measure-theoretic glue already
exist in the project.  The genuinely geometric successor arguments are
separated here.  The closure successor produces the source's contradiction
to WS5: arbitrarily many connected components in one affine section.  The
nullity successor is needed only for connected compact positive-measure
members; WS5 and component isolation recover the arbitrary compact conclusion
used by closed-ball exhaustion.  Neither premise states the final all-arity
conclusion.

The remainder of the file proves the dimension inductions and the four
closure/interior/nullity equivalences of Figueiredo's Corollary 2.1.18.  In
particular, once closure regularity is available, the corollary needs neither
the stronger finite locally closed decomposition nor the section 5.8
closure-nullity witness.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## The closure-interior dimension induction -/

/-- Closure preserves empty interior for members in one fixed arity. -/
def MaxwellClosureInteriorRegularityAt
    (C : EuclideanSetFamily) (d : ℕ) : Prop :=
  ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
    interior S = ∅ → interior (closure S) = ∅

/-- WS5 proves the one-dimensional base of Maxwell's closure induction.
Indeed, an empty-interior unary member has only point components, hence is
finite and closed. -/
theorem PositiveArityOMinimalWeakSetStructure.maxwellClosureInteriorRegularityAt_one
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C) :
    MaxwellClosureInteriorRegularityAt C 1 := by
  intro S hS hSInterior
  have hcoordinateInterior :
      interior (realEuclideanOneCoordinateImage S) = ∅ := by
    rw [realEuclideanOneCoordinateImage_eq_equivImage]
    change interior (realEuclideanOneEquivReal.toHomeomorph '' S) = ∅
    rw [← realEuclideanOneEquivReal.toHomeomorph.image_interior]
    simp [hSInterior]
  have hcoordinateFinite :
      (realEuclideanOneCoordinateImage S).Finite :=
    (hC.coordinateImage_unaryPieceDecomposable hS)
      |>.finite_of_interior_eq_empty hcoordinateInterior
  have himageFinite : (realEuclideanOneEquivReal '' S).Finite := by
    rwa [← realEuclideanOneCoordinateImage_eq_equivImage]
  have hSFinite : S.Finite :=
    himageFinite.of_finite_image
      realEuclideanOneEquivReal.injective.injOn
  rw [hSFinite.isClosed.closure_eq]
  exact hSInterior

/-- The missing successor argument in Maxwell's proof of closure regularity.
Assuming closure regularity in arity `n`, an interior gap in arity `n + 1`
must select arbitrarily many components in one affine section.  WS5 then
rules out that gap.

This is a witness-producing intermediate statement: it does not assume
closure regularity in the successor arity.  Under WS5 it is equivalent to
that regularity, as proved setwise in
`maxwellInteriorGapComponentSelection_iff_closureInteriorRegularity`. -/
def MaxwellClosureInteriorDimensionStep
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    MaxwellClosureInteriorRegularityAt C n →
    ∀ {A : Set (RealEuclidean (n + 1))}, A ∈ C (n + 1) →
      MaxwellInteriorGapComponentSelection A

/-- One closure successor step follows by comparing the selected components
with the WS5 affine-section bound. -/
theorem maxwellClosureInteriorRegularityAt_succ
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hstep : MaxwellClosureInteriorDimensionStep C)
    {n : ℕ} (hn : 0 < n)
    (hprevious : MaxwellClosureInteriorRegularityAt C n) :
    MaxwellClosureInteriorRegularityAt C (n + 1) := by
  intro A hA hAInterior
  exact interior_closure_eq_empty_of_maxwellComponentSelection
    (hC.maxwellFiniteAffineSectionComponentBound (by omega) hA)
    (hstep hn hprevious hA) hAInterior

/-- The unary base and the source-shaped successor component selection prove
closure-interior regularity in every positive arity. -/
theorem charbonnelClosureInteriorRegularity_of_maxwellDimensionStep
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hstep : MaxwellClosureInteriorDimensionStep C) :
    CharbonnelClosureInteriorRegularity C := by
  have hall : ∀ k : ℕ,
      MaxwellClosureInteriorRegularityAt C (k + 1) := by
    intro k
    induction k with
    | zero =>
        exact (hC.maxwellClosureInteriorRegularityAt_one :
          MaxwellClosureInteriorRegularityAt C 1)
    | succ k ih =>
        exact maxwellClosureInteriorRegularityAt_succ
          hC hstep (by omega) ih
  intro d hd S hS hSInterior
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact hall k hS hSInterior

/-- The already isolated family-wide finite-selection premise is stronger
than the source-shaped dimension step because it does not need the induction
hypothesis. -/
theorem maxwellClosureInteriorDimensionStep_of_componentSelection
    {C : EuclideanSetFamily}
    (hselection : HasMaxwellInteriorGapComponentSelection C) :
    MaxwellClosureInteriorDimensionStep C := by
  intro n _hn _hprevious A hA
  exact hselection (by omega) hA

/-- In the presence of WS6, the meagre-selection formulation also supplies
the source-shaped dimension step: closed lifts make every member `F_sigma`,
so empty interior implies meagreness. -/
theorem maxwellClosureInteriorDimensionStep_of_meagreSelection
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hselection : HasMaxwellMeagreClosureComponentSelection C) :
    MaxwellClosureInteriorDimensionStep C := by
  intro n _hn _hprevious A hA
  exact maxwellInteriorGapComponentSelection_of_countableUnionClosed
    (hC.isCountableUnionOfClosedSets (by omega) hA)
    (hselection (by omega) hA)

/-! ## The closed-set nullity dimension induction -/

/-- The connected-component carriers cover their ambient set. -/
theorem iUnion_maxwellConnectedComponentCarrier
    {E : Type*} [TopologicalSpace E] (A : Set E) :
    (⋃ c : ConnectedComponents A,
      maxwellConnectedComponentCarrier c) = A := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hx
    exact maxwell_connectedComponentCarrier_subset c hxc
  · intro x hx
    let p : A := ⟨x, hx⟩
    exact Set.mem_iUnion.mpr
      ⟨ConnectedComponents.mk p, ⟨p, rfl, rfl⟩⟩

/-- A finite-component Euclidean set of positive volume has a
positive-volume connected-component carrier. -/
theorem exists_maxwellConnectedComponentCarrier_positive_volume
    {d : ℕ} {A : Set (RealEuclidean d)}
    (hfinite : Finite (ConnectedComponents A))
    (hpositive : 0 < (volume : Measure (RealEuclidean d)) A) :
    ∃ c : ConnectedComponents A,
      0 < (volume : Measure (RealEuclidean d))
        (maxwellConnectedComponentCarrier c) := by
  classical
  letI : Finite (ConnectedComponents A) := hfinite
  by_contra hnone
  have hzero : ∀ c : ConnectedComponents A,
      (volume : Measure (RealEuclidean d))
          (maxwellConnectedComponentCarrier c) = 0 := by
    intro c
    apply le_antisymm
    · apply le_of_not_gt
      intro hc
      exact hnone ⟨c, hc⟩
    · exact bot_le
  have hAzero : (volume : Measure (RealEuclidean d)) A = 0 := by
    rw [← iUnion_maxwellConnectedComponentCarrier A]
    exact measure_iUnion_null hzero
  exact (ne_of_gt hpositive) hAzero

/-- The genuinely geometric successor output in Maxwell's nullity proof,
restricted to connected compact members.  Assuming `P'_n`, every connected
compact family member of positive measure in arity `n + 1` has nonempty
interior. -/
def MaxwellConnectedClosedNullityDimensionStep
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
    ∀ S : Set (RealEuclidean (n + 1)),
      IsCompact S → IsConnected S → S ∈ C (n + 1) →
      0 < (volume : Measure (RealEuclidean (n + 1))) S →
        (interior S).Nonempty

/-- Compatibility interface with the arbitrary-compact formulation.
Closed-ball exhaustion turns this conclusion into `P'_(n+1)` below.

This compact conclusion is the geometric form used before closed-ball
exhaustion and does not mention arbitrary successor-arity members. -/
def MaxwellClosedNullityDimensionStep
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
    CharbonnelCompactPositiveVolumeInterior C (n + 1)

/-- WS5 reduces the arbitrary compact successor to connected compact
members.  Its finite component carriers remain family members by WS1--WS2,
and positive total volume forces one carrier to have positive volume. -/
theorem maxwellClosedNullityDimensionStep_of_connected
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hstep : MaxwellConnectedClosedNullityDimensionStep C) :
    MaxwellClosedNullityDimensionStep C := by
  intro n hn hPPrime S hScompact hSmem hSpositive
  obtain ⟨N, hN⟩ := hC.ws5_affineSections (by omega) hSmem
  have hcard := hN (⊤ : AffineSubspace ℝ (RealEuclidean (n + 1)))
  rw [AffineSubspace.top_coe, inter_univ] at hcard
  have hfinite : Finite (ConnectedComponents S) := by
    rw [← ENat.card_lt_top]
    exact hcard.trans_lt (WithTop.coe_lt_top N)
  obtain ⟨c, hcpositive⟩ :=
    exists_maxwellConnectedComponentCarrier_positive_volume
      hfinite hSpositive
  have hccompact : IsCompact (maxwellConnectedComponentCarrier c) :=
    maxwell_connectedComponentCarrier_isCompact_of_isCompact hScompact c
  have hcmem : maxwellConnectedComponentCarrier c ∈ C (n + 1) :=
    compact_connectedComponentCarrier_mem
      hC.toPositiveArityWeakSetStructure (by omega)
      hScompact hSmem hfinite c
  have hcInterior := hstep hn hPPrime
    (maxwellConnectedComponentCarrier c) hccompact
    (maxwell_connectedComponentCarrier_isConnected c) hcmem hcpositive
  exact hcInterior.mono
    (interior_mono (maxwell_connectedComponentCarrier_subset c))

/-- WS1 and WS2 already keep integral closed-ball truncations in any
positive-arity weak structure. -/
theorem PositiveArityWeakSetStructure.maxwellCompactTruncationMembership
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C) :
    CharbonnelCompactTruncationMembership C := by
  intro d hd S hS m
  change S ∩ Metric.closedBall 0 (m : ℝ) ∈ C d
  exact hC.ws1_inter hd hS
    (hC.ws2_polynomialSign hd
      (polynomialSignConstructible_closedBall_zero d m))

/-- The first field of the maintained Charbonnel section 5 analytic package
is one way to discharge Maxwell's compact nullity successor.  Its bounded
`Q_n` field is not needed for Lemma 2.1.16 or Corollary 2.1.18. -/
theorem CharbonnelSection5AnalyticStep.toMaxwellClosedNullityDimensionStep
    {C : EuclideanSetFamily}
    (hanalytic : CharbonnelSection5AnalyticStep C) :
    MaxwellClosedNullityDimensionStep C := by
  intro n hn hPPrime
  exact hanalytic.compactPositiveVolumeInterior_of_pPrime hn hPPrime

/-- The maintained analytic package also discharges the weaker connected
compact successor directly. -/
theorem CharbonnelSection5AnalyticStep.toMaxwellConnectedClosedNullityDimensionStep
    {C : EuclideanSetFamily}
    (hanalytic : CharbonnelSection5AnalyticStep C) :
    MaxwellConnectedClosedNullityDimensionStep C := by
  intro n hn hPPrime S hScompact _hSconnected hS hSpositive
  exact hanalytic.compactPositiveVolumeInterior_of_pPrime hn hPPrime
    S hScompact hS hSpositive

/-- Closed-ball exhaustion converts the compact geometric successor into
the next `P'` assertion. -/
theorem charbonnelPPrime_succ_of_maxwellClosedNullityDimensionStep
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    (hstep : MaxwellClosedNullityDimensionStep C)
    {n : ℕ} (hn : 0 < n)
    (hPPrime : CharbonnelPPrime C n) :
    CharbonnelPPrime C (n + 1) :=
  charbonnelPPrime_of_compactPositiveVolumeInterior (by omega)
    hC.maxwellCompactTruncationMembership
    (hstep hn hPPrime)

/-- WS5 supplies `P'_1`; the compact successor then proves `P'_n` in every
positive arity. -/
theorem charbonnelPPrime_all_of_maxwellClosedNullityDimensionStep
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hstep : MaxwellClosedNullityDimensionStep C) :
    ∀ {d : ℕ}, 0 < d → CharbonnelPPrime C d := by
  intro d hd
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  induction k with
  | zero =>
      simpa using hC.charbonnelPPrime_one
  | succ k ih =>
      exact charbonnelPPrime_succ_of_maxwellClosedNullityDimensionStep
        hC.toPositiveArityWeakSetStructure hstep (Nat.succ_pos k)
          (ih (Nat.succ_pos k))

/-! ## The minimal two-step package and its consequences -/

/-- The two independent geometric successor obligations in Maxwell's
closure/nullity argument.  The closure field exposes the affine-section
component witness, while the nullity field is restricted to connected compact
members; neither states the final all-arity theorem. -/
structure MaxwellClosureNullityDimensionInduction
    (C : EuclideanSetFamily) : Prop where
  closureStep : MaxwellClosureInteriorDimensionStep C
  nullityStep : MaxwellConnectedClosedNullityDimensionStep C

/-- Existing family-wide component selection and the compact field of the
section 5 analytic package instantiate the minimal induction package. -/
theorem maxwellClosureNullityDimensionInduction_of_selection_and_analyticStep
    {C : EuclideanSetFamily}
    (hselection : HasMaxwellInteriorGapComponentSelection C)
    (hanalytic : CharbonnelSection5AnalyticStep C) :
    MaxwellClosureNullityDimensionInduction C :=
  ⟨maxwellClosureInteriorDimensionStep_of_componentSelection hselection,
    hanalytic.toMaxwellConnectedClosedNullityDimensionStep⟩

/-- The source-shaped meagre selection premise gives the same package after
WS6 supplies the `F_sigma` reduction. -/
theorem maxwellClosureNullityDimensionInduction_of_meagreSelection_and_analyticStep
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hselection : HasMaxwellMeagreClosureComponentSelection C)
    (hanalytic : CharbonnelSection5AnalyticStep C) :
    MaxwellClosureNullityDimensionInduction C :=
  ⟨maxwellClosureInteriorDimensionStep_of_meagreSelection hC hselection,
    hanalytic.toMaxwellConnectedClosedNullityDimensionStep⟩

theorem MaxwellClosureNullityDimensionInduction.closureInteriorRegularity
    {C : EuclideanSetFamily}
    (hMaxwell : MaxwellClosureNullityDimensionInduction C)
    (hC : PositiveArityOMinimalWeakSetStructure C) :
    CharbonnelClosureInteriorRegularity C :=
  charbonnelClosureInteriorRegularity_of_maxwellDimensionStep
    hC hMaxwell.closureStep

theorem MaxwellClosureNullityDimensionInduction.pPrime_all
    {C : EuclideanSetFamily}
    (hMaxwell : MaxwellClosureNullityDimensionInduction C)
    (hC : PositiveArityOMinimalWeakSetStructure C) :
    ∀ {d : ℕ}, 0 < d → CharbonnelPPrime C d :=
  charbonnelPPrime_all_of_maxwellClosedNullityDimensionStep
    hC (maxwellClosedNullityDimensionStep_of_connected
      hC hMaxwell.nullityStep)

/-- `P'_n`, closure membership, and closure-interior regularity imply all
four equivalences of Figueiredo's Corollary 2.1.18 directly.  The implication
from source nullity to closure nullity factors through empty interior, so no
separate section 5.8 witness or `Q_n` premise is needed. -/
theorem charbonnelTheorem21_of_pPrime_and_closureInteriorRegularity
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hregularity : CharbonnelClosureInteriorRegularity C)
    (hPPrime : ∀ {d : ℕ}, 0 < d → CharbonnelPPrime C d) :
    CharbonnelTheorem21 C := by
  intro d hd S hS
  have hclosurePPrime :
      (volume : Measure (RealEuclidean d)) (closure S) = 0 ↔
        interior (closure S) = ∅ :=
    hPPrime hd (closure S) isClosed_closure
      (hmem.closure_mem hd hS)
  refine ⟨?_, ?_, hclosurePPrime.symm⟩
  · constructor
    · intro hSInterior
      exact measure_mono_null subset_closure
        (hclosurePPrime.mpr (hregularity hd hS hSInterior))
    · intro hSNull
      exact (volume : Measure (RealEuclidean d)).interior_eq_empty_of_null
        hSNull
  · constructor
    · intro hSNull
      exact hregularity hd hS
        ((volume : Measure (RealEuclidean d)).interior_eq_empty_of_null
          hSNull)
    · intro hclosureInterior
      exact measure_mono_null subset_closure
        (hclosurePPrime.mpr hclosureInterior)

/-- The minimal dimension-induction package proves Maxwell's empty-interior
to nullity statement, in fact as an equivalence, for every family member. -/
theorem MaxwellClosureNullityDimensionInduction.interiorNullity_all
    {C : EuclideanSetFamily}
    (hMaxwell : MaxwellClosureNullityDimensionInduction C)
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hmem : CharbonnelSection5TraceMembership C) :
    ∀ {d : ℕ}, 0 < d → CharbonnelInteriorNullity C d := by
  let h21 : CharbonnelTheorem21 C :=
    charbonnelTheorem21_of_pPrime_and_closureInteriorRegularity
      hmem (hMaxwell.closureInteriorRegularity hC)
        (hMaxwell.pPrime_all hC)
  intro d hd S hS
  exact (h21 hd hS).1.symm

/-- The complete Maxwell/Figueiredo closure-nullity corollary from the two
geometric dimension steps. -/
theorem MaxwellClosureNullityDimensionInduction.theorem21
    {C : EuclideanSetFamily}
    (hMaxwell : MaxwellClosureNullityDimensionInduction C)
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hmem : CharbonnelSection5TraceMembership C) :
    CharbonnelTheorem21 C :=
  charbonnelTheorem21_of_pPrime_and_closureInteriorRegularity
    hmem (hMaxwell.closureInteriorRegularity hC)
      (hMaxwell.pPrime_all hC)

/-- The same hypotheses also give Charbonnel's `P_n`: nullity of a member,
or empty interior of its closure, implies nullity of its closure. -/
theorem MaxwellClosureNullityDimensionInduction.charbonnelP_all
    {C : EuclideanSetFamily}
    (hMaxwell : MaxwellClosureNullityDimensionInduction C)
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hmem : CharbonnelSection5TraceMembership C) :
    ∀ {d : ℕ}, 0 < d → CharbonnelP C d := by
  let h21 : CharbonnelTheorem21 C := hMaxwell.theorem21 hC hmem
  intro d hd S hS hsmall
  rcases hsmall with hSNull | hclosureInterior
  · exact (h21 hd hS).2.2.mp ((h21 hd hS).2.1.mp hSNull)
  · exact (h21 hd hS).2.2.mp hclosureInterior

/-! ## Literal-zero Charbonnel specialization -/

/-- For the maintained literal-zero Charbonnel closure, all structural,
one-dimensional, truncation, and closure-membership hypotheses are already
proved.  Only the two geometric successor fields remain. -/
theorem literalZeroSet_charbonnelClosure_theorem21_of_maxwellDimensionInduction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hMaxwell : MaxwellClosureNullityDimensionInduction
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)) :=
  hMaxwell.theorem21
    (literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF)
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)

/-- Concrete adapter from the two currently isolated stronger premises:
Maxwell meagre finite selection and the Charbonnel section 5 analytic step. -/
theorem literalZeroSet_charbonnelClosure_theorem21_of_meagreSelection_and_analyticStep
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  intro n hn S hS
  exact
    ((maxwellClosureNullityDimensionInduction_of_meagreSelection_and_analyticStep
      hC hselection hanalytic).theorem21 hC
        (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth))
      hn hS

end AbelFormalization
