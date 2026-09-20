import AbelFormalization.MaxwellDifferenceQuotientEmptyInterior
import AbelFormalization.MaxwellSlopeClusterSmallness
import AbelFormalization.MaxwellFirstOrderAssembly

/-!
# Source-level adapter for Maxwell's first-order analytic core

This file joins the source-faithful pieces of Figueiredo--Maxwell
Lemmas 2.3.2, 2.3.3, and 2.3.8--2.3.11 to the two-field analytic core used
by `MaxwellFirstOrderAssembly`.

There are three reductions here.

* The old empty-interior hypothesis on a directional quotient is eliminated:
  it follows from the input pseudofunction's null multivalued locus.
* The intermediate-value input for a one-sided extended slope trace is stated
  as the four exact order-convexity consequences used in the finite/finite,
  finite/infinite, and opposite-infinity cases.  These consequences imply the
  interval-filling interface consumed by the Fubini argument.
* The coordinate slope-bad locus is covered by the two one-sided extended
  multivalued loci and Maxwell's three hard cases.  The existing
  nondifferentiability cluster-data interface is needed only on the literal
  residual after removing the first two loci.

Thus the final adapter has no measure, interior, family-membership, or
quotient-empty-interior assumptions among its analytic residuals.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## The exact one-sided intermediate-value consequence -/

/-- Source-shaped IVT data for one connected side of the step variable.
The finite cluster fiber has the intermediate-value property, while an
infinite cluster supplies finite values arbitrarily far in the corresponding
direction.  This is the direct output of applying continuity and IVT before
the Fubini argument in Lemma 2.3.3. -/
structure MaxwellOneSidedSlopeIVTData
    {p : ℕ} (G : MaxwellRelation p 1)
    (P N : Set (RealEuclidean p)) : Prop where
  finite_intermediateValue : MaxwellFiniteSlopeIntervalFibers G
  positiveInfinity_unbounded : ∀ (x : RealEuclidean p), x ∈ P →
    ∀ M : ℝ, ∃ y : ℝ, M < y ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G
  negativeInfinity_unbounded : ∀ (x : RealEuclidean p), x ∈ N →
    ∀ M : ℝ, ∃ y : ℝ, y < M ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G

/-- The order-convexity and unboundedness conclusions supplied by continuity
and the intermediate value theorem for one connected side of the step
variable.

`finite_between` treats two finite cluster values.  The next two fields treat
a finite value together with one infinite cluster value.  The last field
treats simultaneous `-infinity` and `+infinity`.  These are precisely the
four cases used in the interval-filling proof of source Lemma 2.3.3. -/
structure MaxwellExtendedSlopeIntermediateValue
    {p : ℕ} (G : MaxwellRelation p 1)
    (P N : Set (RealEuclidean p)) : Prop where
  finite_between : MaxwellFiniteSlopeIntervalFibers G
  finite_to_positiveInfinity : ∀ (x : RealEuclidean p) (a b : ℝ),
    a ≤ b →
    realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈ G →
    x ∈ P →
    realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈ G
  negativeInfinity_to_finite : ∀ (x : RealEuclidean p) (a b : ℝ),
    b ≤ a →
    realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈ G →
    x ∈ N →
    realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈ G
  negativeInfinity_to_positiveInfinity : ∀ (x : RealEuclidean p) (y : ℝ),
    x ∈ P → x ∈ N →
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G

/-- Unbounded one-sided finite values plus the ordinary finite IVT give all
four order-convexity consequences needed for extended slope values. -/
theorem MaxwellOneSidedSlopeIVTData.extendedIntermediateValue
    {p : ℕ} {G : MaxwellRelation p 1}
    {P N : Set (RealEuclidean p)}
    (h : MaxwellOneSidedSlopeIVTData G P N) :
    MaxwellExtendedSlopeIntermediateValue G P N := by
  constructor
  · exact h.finite_intermediateValue
  · intro x a b hab ha hxP
    obtain ⟨c, hbc, hc⟩ := h.positiveInfinity_unbounded x hxP b
    exact h.finite_intermediateValue x a c (lt_of_le_of_lt hab hbc)
      ha hc ⟨hab, le_of_lt hbc⟩
  · intro x a b hba ha hxN
    obtain ⟨c, hcb, hc⟩ := h.negativeInfinity_unbounded x hxN b
    exact h.finite_intermediateValue x c a (lt_of_lt_of_le hcb hba)
      hc ha ⟨le_of_lt hcb, hba⟩
  · intro x y hxP hxN
    obtain ⟨a, hay, ha⟩ := h.negativeInfinity_unbounded x hxN y
    obtain ⟨b, hyb, hb⟩ := h.positiveInfinity_unbounded x hxP y
    exact h.finite_intermediateValue x a b (lt_trans hay hyb)
      ha hb ⟨le_of_lt hay, le_of_lt hyb⟩

/-- The four IVT consequences above imply the interval in every multivalued
extended fiber required by the Fubini reduction. -/
theorem MaxwellExtendedSlopeIntermediateValue.intervalFilling
    {p : ℕ} {G : MaxwellRelation p 1}
    {P N : Set (RealEuclidean p)}
    (h : MaxwellExtendedSlopeIntermediateValue G P N) :
    MaxwellExtendedSlopeIntervalFilling G
      (maxwellOneSidedExtendedMultivaluedLocus G P N) := by
  intro x hx
  rcases hx with ⟨a, b, ha, hb, hab⟩
  cases a with
  | finite a =>
      cases b with
      | finite b =>
          have hab' : a ≠ b := by
            intro heq
            apply hab
            exact congrArg MaxwellExtendedSlopeValue.finite heq
          rcases lt_or_gt_of_ne hab' with hlt | hgt
          · exact ⟨a, b, hlt, h.finite_between x a b hlt ha hb⟩
          · exact ⟨b, a, hgt, h.finite_between x b a hgt hb ha⟩
      | positiveInfinity =>
          refine ⟨a, a + 1, by linarith, ?_⟩
          intro y hy
          exact h.finite_to_positiveInfinity x a y hy.1 ha hb
      | negativeInfinity =>
          refine ⟨a - 1, a, by linarith, ?_⟩
          intro y hy
          exact h.negativeInfinity_to_finite x a y hy.2 ha hb
  | positiveInfinity =>
      cases b with
      | finite b =>
          refine ⟨b, b + 1, by linarith, ?_⟩
          intro y hy
          exact h.finite_to_positiveInfinity x b y hy.1 hb ha
      | positiveInfinity => exact False.elim (hab rfl)
      | negativeInfinity =>
          refine ⟨-1, 1, by norm_num, ?_⟩
          intro y _hy
          exact h.negativeInfinity_to_positiveInfinity x y ha hb
  | negativeInfinity =>
      cases b with
      | finite b =>
          refine ⟨b - 1, b, by linarith, ?_⟩
          intro y hy
          exact h.negativeInfinity_to_finite x b y hy.2 hb ha
      | positiveInfinity =>
          refine ⟨-1, 1, by norm_num, ?_⟩
          intro y _hy
          exact h.negativeInfinity_to_positiveInfinity x y hb ha
      | negativeInfinity => exact False.elim (hab rfl)

/-- Direct form of the one-sided IVT conclusion consumed by the Fubini
smallness theorem. -/
theorem MaxwellOneSidedSlopeIVTData.intervalFilling
    {p : ℕ} {G : MaxwellRelation p 1}
    {P N : Set (RealEuclidean p)}
    (h : MaxwellOneSidedSlopeIVTData G P N) :
    MaxwellExtendedSlopeIntervalFilling G
      (maxwellOneSidedExtendedMultivaluedLocus G P N) :=
  MaxwellExtendedSlopeIntermediateValue.intervalFilling
    h.extendedIntermediateValue

/-! ## Quotient smallness with no empty-interior premise -/

/-- Lemma 2.3.2 specialized to a directional quotient of a pseudofunction.
The quotient's empty interior is a theorem, not an analytic premise. -/
theorem maxwellDifferenceQuotientPositiveZeroTraceSmallness_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R) :
    MaxwellTwoSidedZeroTraceSmallness S
      (maxwellStepLastDifferenceQuotientRelation U R i) := by
  exact maxwellDifferenceQuotientPositiveZeroTraceSmallness
    hC hmem h21 h22 i hU hR
      (maxwellDifferenceQuotientRelation_interior_eq_empty i hRpseudo)

theorem maxwellDifferenceQuotientZeroTrace_volume_eq_zero_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R) :
    (volume : Measure (RealEuclidean (p + 1)))
        (maxwellDifferenceQuotientZeroTrace U R i) = 0 := by
  exact maxwellDifferenceQuotientZeroTrace_volume_eq_zero
    hC hmem h21 h22 i hU hR
      (maxwellDifferenceQuotientRelation_interior_eq_empty i hRpseudo)

theorem maxwellDifferenceQuotientZeroTrace_interior_eq_empty_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R) :
    interior (maxwellDifferenceQuotientZeroTrace U R i) = ∅ := by
  exact maxwellDifferenceQuotientZeroTrace_interior_eq_empty
    hC hmem h21 h22 i hU hR
      (maxwellDifferenceQuotientRelation_interior_eq_empty i hRpseudo)

theorem maxwellOneSidedFiniteSlopeBadLociSmallness_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R)
    (hpositiveInterval : MaxwellFiniteSlopeIntervalFibers
      (maxwellPositiveStepZeroTrace U R i))
    (hnegativeInterval : MaxwellFiniteSlopeIntervalFibers
      (maxwellNegativeStepZeroTrace U R i)) :
    MaxwellOneSidedFiniteSlopeBadLociSmallness S U R i := by
  exact maxwellOneSidedFiniteSlopeBadLociSmallness
    hC hmem h21 h22 i hU hR
      (maxwellDifferenceQuotientRelation_interior_eq_empty i hRpseudo)
      hpositiveInterval hnegativeInterval

theorem maxwellDifferenceQuotientFiniteSlopeBadLocusSmallness_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R)
    (hinterval : MaxwellFiniteSlopeIntervalFibers
      (maxwellDifferenceQuotientZeroTrace U R i)) :
    MaxwellFiniteSlopeBadLocusSmallness S
      (maxwellDifferenceQuotientZeroTrace U R i) := by
  exact maxwellDifferenceQuotientFiniteSlopeBadLocusSmallness
    hC hmem h21 h22 i hU hR
      (maxwellDifferenceQuotientRelation_interior_eq_empty i hRpseudo)
      hinterval

/-- Lemmas 2.3.2 and 2.3.3 for both one-sided extended slope traces, with
the quotient-empty-interior premise eliminated and the IVT input exposed in
its exact four-case order-convex form. -/
theorem maxwellOneSidedExtendedSlopeBadLociSmallness_of_pseudofunction_and_intermediateValue
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R)
    (hpositiveIVT : MaxwellExtendedSlopeIntermediateValue
      (maxwellPositiveStepZeroTrace U R i)
      (maxwellPositiveStepPositiveInfinityBase U R i)
      (maxwellPositiveStepNegativeInfinityBase U R i))
    (hnegativeIVT : MaxwellExtendedSlopeIntermediateValue
      (maxwellNegativeStepZeroTrace U R i)
      (maxwellNegativeStepPositiveInfinityBase U R i)
      (maxwellNegativeStepNegativeInfinityBase U R i)) :
    MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i := by
  exact maxwellOneSidedExtendedSlopeBadLociSmallness
    hC hmem h21 h22 i hU hR
      (maxwellDifferenceQuotientRelation_interior_eq_empty i hRpseudo)
      hpositiveIVT.intervalFilling hnegativeIVT.intervalFilling

/-- Compatibility form of the preceding theorem for the older, stronger
unbounded-finite-value interface. -/
theorem maxwellOneSidedExtendedSlopeBadLociSmallness_of_pseudofunction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R)
    (hpositiveIVT : MaxwellOneSidedSlopeIVTData
      (maxwellPositiveStepZeroTrace U R i)
      (maxwellPositiveStepPositiveInfinityBase U R i)
      (maxwellPositiveStepNegativeInfinityBase U R i))
    (hnegativeIVT : MaxwellOneSidedSlopeIVTData
      (maxwellNegativeStepZeroTrace U R i)
      (maxwellNegativeStepPositiveInfinityBase U R i)
      (maxwellNegativeStepNegativeInfinityBase U R i)) :
    MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i := by
  exact
    maxwellOneSidedExtendedSlopeBadLociSmallness_of_pseudofunction_and_intermediateValue
      hC hmem h21 h22 i hU hR hRpseudo
        hpositiveIVT.extendedIntermediateValue
        hnegativeIVT.extendedIntermediateValue

/-! ## The exact residual passed to the three-hard-case argument -/

/-- Remove the two one-sided extended multivalued loci from the global
coordinate slope-bad locus.  Only this residual needs the pointwise cluster
classification used in Lemmas 2.3.9--2.3.11. -/
def maxwellCoordinateSlopeBadResidualLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellCoordinateSlopeBadLocus U R i \
    (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
      maxwellNegativeStepExtendedMultivaluedLocus U R i)

/-- The existing nondifferentiability cluster classification, used only on
the literal residual, covers the entire global slope-bad locus by the two
one-sided bad loci and the three hard cases. -/
theorem maxwellCoordinateSlopeBadLocus_subset_oneSidedBad_union_threeHard
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p}
    (hresidual : MaxwellNondifferentiableOneSidedClusterData U R i
      (maxwellCoordinateSlopeBadResidualLocus U R i)) :
    maxwellCoordinateSlopeBadLocus U R i ⊆
      (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
        maxwellNegativeStepExtendedMultivaluedLocus U R i) ∪
      maxwellThreeHardSlopeCasesLocus U R i := by
  intro x hx
  by_cases hpositive :
      x ∈ maxwellPositiveStepExtendedMultivaluedLocus U R i
  · exact Or.inl (Or.inl hpositive)
  by_cases hnegative :
      x ∈ maxwellNegativeStepExtendedMultivaluedLocus U R i
  · exact Or.inl (Or.inr hnegative)
  · apply Or.inr
    apply hresidual.subset_threeHardCases
    refine ⟨hx, ?_⟩
    simp only [Set.mem_union, not_or]
    exact ⟨hpositive, hnegative⟩

/-! ## Coordinate and family-wide source mechanisms -/

/-- The genuinely analytic inputs still needed for one fixed coordinate.
Each field names the exact source mechanism that produces it.  All family
membership and nullity conclusions are derived below. -/
structure MaxwellCoordinateFirstOrderAnalyticMechanisms
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  positiveStep_intermediateValue : MaxwellExtendedSlopeIntermediateValue
    (maxwellPositiveStepZeroTrace U R i)
    (maxwellPositiveStepPositiveInfinityBase U R i)
    (maxwellPositiveStepNegativeInfinityBase U R i)
  negativeStep_intermediateValue : MaxwellExtendedSlopeIntermediateValue
    (maxwellNegativeStepZeroTrace U R i)
    (maxwellNegativeStepPositiveInfinityBase U R i)
    (maxwellNegativeStepNegativeInfinityBase U R i)
  equalInfinity_continuous : ContinuousOn (maxwellChosenScalarValue R)
    (maxwellSamePositiveInfinityLocus U R i ∪
      maxwellSameNegativeInfinityLocus U R i)
  positiveInfinity_affineChord : MaxwellWS5AffineChordCrossingMechanism
    (maxwellChosenScalarValue R) i .positiveInfinity
      (maxwellSamePositiveInfinityLocus U R i)
  negativeInfinity_affineChord : MaxwellWS5AffineChordCrossingMechanism
    (maxwellChosenScalarValue R) i .negativeInfinity
      (maxwellSameNegativeInfinityLocus U R i)
  differingSlopes_translatedSeparation :
    MaxwellTranslatedOneSidedSeparationMechanism
      (maxwellChosenScalarValue R) i
      (maxwellOneSidedSlopeDisagreementLocus U R i)
  residual_oneSidedClusterData :
    MaxwellNondifferentiableOneSidedClusterData U R i
      (maxwellCoordinateSlopeBadResidualLocus U R i)

/-- Figueiredo--Maxwell Lemmas 2.3.2, 2.3.3, and 2.3.11 imply nullity of
the exact coordinate slope-bad locus consumed by the assembly module. -/
theorem maxwellCoordinateSlopeBadLocus_volume_eq_zero_of_sourceMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunction R)
    (hsource : MaxwellCoordinateFirstOrderAnalyticMechanisms U R i) :
    (volume : Measure (RealEuclidean p))
      (maxwellCoordinateSlopeBadLocus U R i) = 0 := by
  have honeSided :=
    maxwellOneSidedExtendedSlopeBadLociSmallness_of_pseudofunction_and_intermediateValue
      hC hmem h21 h22 i hU hR hRpseudo
        hsource.positiveStep_intermediateValue
        hsource.negativeStep_intermediateValue
  have hhard := maxwellThreeHardSlopeCasesSmallness
    hC hmem h21 i hU hR (maxwellChosenScalarValue R)
      hsource.equalInfinity_continuous
      hsource.positiveInfinity_affineChord
      hsource.negativeInfinity_affineChord
      hsource.differingSlopes_translatedSeparation
  have hcover : maxwellCoordinateSlopeBadLocus U R i ⊆
      (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
        maxwellNegativeStepExtendedMultivaluedLocus U R i) ∪
      maxwellThreeHardSlopeCasesLocus U R i :=
    maxwellCoordinateSlopeBadLocus_subset_oneSidedBad_union_threeHard
      hsource.residual_oneSidedClusterData
  have hcoverNull :
      (volume : Measure (RealEuclidean p))
        ((maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
            maxwellNegativeStepExtendedMultivaluedLocus U R i) ∪
          maxwellThreeHardSlopeCasesLocus U R i) = 0 := by
    exact measure_union_null
      (measure_union_null
        honeSided.positiveBadLocus.locus_volume_eq_zero
        honeSided.negativeBadLocus.locus_volume_eq_zero)
      hhard.unionSmallness.locus_volume_eq_zero
  exact measure_mono_null hcover hcoverNull

/-- Family-wide source mechanisms.  The coordinate field contains the exact
IVT, chord, translation, and residual cluster assertions above.  The final
field is precisely the differentiability conclusion of source Lemma 2.3.10;
it is kept separate because it is logically independent of the nullity
reduction in Lemma 2.3.11. -/
structure MaxwellScalarFirstOrderSourceMechanisms
    (C : EuclideanSetFamily) : Prop where
  coordinate_mechanisms : ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∀ i : Fin p, MaxwellCoordinateFirstOrderAnalyticMechanisms U R i
  chosen_differentiable : ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∀ x ∈ U \ maxwellFirstOrderExceptionalLocus U R,
        DifferentiableAt ℝ (maxwellChosenScalarValue R) x

/-- The source mechanisms imply the exact two-field analytic core used by
`maxwellScalarFirstOrderPackage_of_analyticCore`.  In particular, the first
field of that core is now assembled without any quotient-empty-interior,
measure, or family-membership residual. -/
theorem maxwellScalarFirstOrderAnalyticCore_of_sourceMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarFirstOrderSourceMechanisms
      (charbonnelClosure S)) :
    MaxwellScalarFirstOrderAnalyticCore (charbonnelClosure S) := by
  constructor
  · intro p hp U R hUopen hU hR hRpseudo i
    exact maxwellCoordinateSlopeBadLocus_volume_eq_zero_of_sourceMechanisms
      hC hmem h21 h22 i hU hR hRpseudo.multivalued_null
        (hsource.coordinate_mechanisms hp U R hUopen hU hR hRpseudo i)
  · intro p hp U R hUopen hU hR hRpseudo x hx
    exact hsource.chosen_differentiable hp U R hUopen hU hR
      hRpseudo x hx

/-- End-to-end scalar first-order package from the source mechanisms. -/
theorem maxwellScalarFirstOrderPackage_of_sourceMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarFirstOrderSourceMechanisms
      (charbonnelClosure S)) :
    MaxwellScalarFirstOrderPackage (charbonnelClosure S) := by
  exact maxwellScalarFirstOrderPackage_of_analyticCore hC h21
    (maxwellScalarFirstOrderAnalyticCore_of_sourceMechanisms
      hC hmem h21 h22 hsource)

/-- Every finite scalar differentiability order from the same source
mechanisms. -/
theorem maxwellScalarPseudofunctionOrderSmoothness_of_sourceMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarFirstOrderSourceMechanisms
      (charbonnelClosure S)) :
    ∀ N : ℕ,
      MaxwellScalarPseudofunctionOrderSmoothness
        (charbonnelClosure S) N := by
  exact maxwellScalarPseudofunctionOrderSmoothness_of_analyticCore hC h21
    (maxwellScalarFirstOrderAnalyticCore_of_sourceMechanisms
      hC.toPositiveArityWeakSetStructure hmem h21 h22 hsource)

/-- Maxwell's all-orders finite-output smoothness conclusion from the exact
source mechanisms isolated in this file. -/
theorem maxwellAlmostEverywhereSmoothness_of_sourceMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarFirstOrderSourceMechanisms
      (charbonnelClosure S)) :
    MaxwellAlmostEverywhereSmoothness (charbonnelClosure S) := by
  exact maxwellAlmostEverywhereSmoothness_of_analyticCore hC h21
    (maxwellScalarFirstOrderAnalyticCore_of_sourceMechanisms
      hC.toPositiveArityWeakSetStructure hmem h21 h22 hsource)

end AbelFormalization
