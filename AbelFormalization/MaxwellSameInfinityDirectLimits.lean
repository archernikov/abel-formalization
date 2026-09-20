import AbelFormalization.MaxwellOneSidedBoundedClusterExtraction
import AbelFormalization.MaxwellChosenInfinitySmallness
import AbelFormalization.MaxwellTranslatedSeparationExtraction
import AbelFormalization.MaxwellWS5AffineChordExtraction

/-!
# Direct limits on the regular part of Maxwell's equal-infinity loci

The source-defined infinity bases are closure loci, so their witnesses may
move in the base variable.  At a point where the corresponding extended
one-sided fiber is single-valued, however, that moving-base witness forces a
moving-base *uniform* bound.  Indeed, failure of such a bound produces a
bounded one-sided sequence; bounded cluster extraction then gives either a
finite cluster or the opposite infinity, contradicting single-valuedness.

On the open pseudofunction domain the moving-base bound specializes to the
fixed-base direct limit used by the affine-chord argument.  Removing the
closures of the two already-small extended-multivalued loci therefore gives
direct same-infinity limits.  A localization argument then lifts the chord
mechanism back to the full equal-infinity loci, and hence proves their empty
interior and smallness.
-/

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Moving-base uniform divergence from a single extended value -/

/-- A positive-infinite one-sided cluster is locally uniformly above every
fixed cutoff, provided that the extended one-sided fiber is not multivalued.
The base point is allowed to move; this is stronger than the fixed-base limit
needed below. -/
theorem IsMaxwellPseudofunctionOn.oneSidedDifferenceQuotientLocallyGtAt_of_positiveInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R)
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p} (cutoff : ℝ)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .positive)
    (hsingle : x ∉ maxwellOneSidedExtendedMultivaluedLocus
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative)) :
    MaxwellOneSidedDifferenceQuotientLocallyGtAt U
      (maxwellChosenScalarValue R) i side x cutoff := by
  have hinfinity' : MaxwellExtendedSlopeValue.positiveInfinity ∈
      maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x := by
    simpa using hinfinity
  apply hR.oneSidedDifferenceQuotient_locally_gt_of_unique_positiveInfinity
    i side hinfinity'
  intro a ha
  by_contra hne
  apply hsingle
  exact ⟨a, .positiveInfinity, ha, hinfinity', hne⟩

/-- A negative-infinite one-sided cluster is locally uniformly below every
fixed cutoff, provided that the extended one-sided fiber is not multivalued. -/
theorem IsMaxwellPseudofunctionOn.oneSidedDifferenceQuotientLocallyLtAt_of_negativeInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R)
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p} (cutoff : ℝ)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .negative)
    (hsingle : x ∉ maxwellOneSidedExtendedMultivaluedLocus
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative)) :
    MaxwellOneSidedDifferenceQuotientLocallyLtAt U
      (maxwellChosenScalarValue R) i side x cutoff := by
  have hinfinity' : MaxwellExtendedSlopeValue.negativeInfinity ∈
      maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x := by
    simpa using hinfinity
  apply hR.oneSidedDifferenceQuotient_locally_lt_of_unique_negativeInfinity
    i side hinfinity'
  intro a ha
  by_contra hne
  apply hsingle
  exact ⟨a, .negativeInfinity, ha, hinfinity', hne⟩

/-! ## Fixed-base consequences on the open domain -/

private theorem tendsto_fixedBase_oneSided_atTop_of_localGt
    {p : ℕ} {U : Set (RealEuclidean p)} {f : RealEuclidean p → ℝ}
    {i : Fin p} {side : MaxwellOneSidedStep}
    (hU : IsOpen U) {x : RealEuclidean p} (hx : x ∈ U)
    (hlocal : ∀ cutoff : ℝ,
      MaxwellOneSidedDifferenceQuotientLocallyGtAt
        U f i side x cutoff) :
    Tendsto (fun t : ℝ ↦
      maxwellOneSidedDifferenceQuotient f i side (x, t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  let v : RealEuclidean p := Pi.single i 1
  have hshift : Tendsto
      (fun t : ℝ ↦ x + (side.sign * t) • v)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x) := by
    have ht : Tendsto (fun t : ℝ ↦ t)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    have hsigned : Tendsto (fun t : ℝ ↦ side.sign * t)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      simpa using (tendsto_const_nhds.mul ht)
    simpa only [mul_zero, zero_smul, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x)).add (hsigned.smul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ v)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds v)))
  have hshiftU : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      x + (side.sign * t) • v ∈ U :=
    hshift.eventually (hU.mem_nhds hx)
  rw [tendsto_atTop]
  intro cutoff
  obtain ⟨rho, hrho, delta, hdelta, hbound⟩ := hlocal cutoff
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < delta :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hdelta)
  filter_upwards [hshiftU, hsmall, self_mem_nhdsWithin] with t htU htSmall htPos
  exact (hbound (x, t) ⟨hx, by simpa only [v] using htU, htPos⟩
    (by simpa using hrho) htSmall).le

private theorem tendsto_fixedBase_oneSided_atBot_of_localLt
    {p : ℕ} {U : Set (RealEuclidean p)} {f : RealEuclidean p → ℝ}
    {i : Fin p} {side : MaxwellOneSidedStep}
    (hU : IsOpen U) {x : RealEuclidean p} (hx : x ∈ U)
    (hlocal : ∀ cutoff : ℝ,
      MaxwellOneSidedDifferenceQuotientLocallyLtAt
        U f i side x cutoff) :
    Tendsto (fun t : ℝ ↦
      maxwellOneSidedDifferenceQuotient f i side (x, t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atBot := by
  let v : RealEuclidean p := Pi.single i 1
  have hshift : Tendsto
      (fun t : ℝ ↦ x + (side.sign * t) • v)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x) := by
    have ht : Tendsto (fun t : ℝ ↦ t)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    have hsigned : Tendsto (fun t : ℝ ↦ side.sign * t)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      simpa using (tendsto_const_nhds.mul ht)
    simpa only [mul_zero, zero_smul, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x)).add (hsigned.smul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ v)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds v)))
  have hshiftU : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      x + (side.sign * t) • v ∈ U :=
    hshift.eventually (hU.mem_nhds hx)
  rw [tendsto_atBot]
  intro cutoff
  obtain ⟨rho, hrho, delta, hdelta, hbound⟩ := hlocal cutoff
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < delta :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hdelta)
  filter_upwards [hshiftU, hsmall, self_mem_nhdsWithin] with t htU htSmall htPos
  exact (hbound (x, t) ⟨hx, by simpa only [v] using htU, htPos⟩
    (by simpa using hrho) htSmall).le

theorem IsMaxwellPseudofunctionOn.tendsto_oneSidedDifferenceQuotient_atTop_of_positiveInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p} (hx : x ∈ U)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .positive)
    (hsingle : x ∉ maxwellOneSidedExtendedMultivaluedLocus
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative)) :
    Tendsto (fun t : ℝ ↦ maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (x, t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  apply tendsto_fixedBase_oneSided_atTop_of_localGt hU hx
  intro cutoff
  exact hR.oneSidedDifferenceQuotientLocallyGtAt_of_positiveInfinity
    i side cutoff hinfinity hsingle

theorem IsMaxwellPseudofunctionOn.tendsto_oneSidedDifferenceQuotient_atBot_of_negativeInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p} (hx : x ∈ U)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .negative)
    (hsingle : x ∉ maxwellOneSidedExtendedMultivaluedLocus
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative)) :
    Tendsto (fun t : ℝ ↦ maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (x, t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atBot := by
  apply tendsto_fixedBase_oneSided_atBot_of_localLt hU hx
  intro cutoff
  exact hR.oneSidedDifferenceQuotientLocallyLtAt_of_negativeInfinity
    i side cutoff hinfinity hsingle

/-! ## Direct same-infinity limits after the already-small deletion -/

/-- The closed deletion used to make both one-sided extended fibers unique. -/
def maxwellOneSidedExtendedMultivaluedExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  closure (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
    maxwellNegativeStepExtendedMultivaluedLocus U R i)

theorem isClosed_maxwellOneSidedExtendedMultivaluedExceptionalLocus
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    IsClosed (maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i) :=
  isClosed_closure

/-- The largest locus supplied by extended-fiber uniqueness: points of the
open domain and the chosen equal-infinity locus which lie in neither raw
one-sided extended-multivalued locus. -/
def maxwellSameInfinityFiberRegularLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (s : MaxwellSameInfinitySign) :
    Set (RealEuclidean p) :=
  U ∩ ((match s with
    | .positiveInfinity => maxwellSamePositiveInfinityLocus U R i
    | .negativeInfinity => maxwellSameNegativeInfinityLocus U R i) \
      (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
        maxwellNegativeStepExtendedMultivaluedLocus U R i))

/-- The smaller closed-deletion locus used for open-set localization. -/
def maxwellSameInfinityDirectLimitLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (s : MaxwellSameInfinitySign) :
    Set (RealEuclidean p) :=
  U ∩ ((match s with
    | .positiveInfinity => maxwellSamePositiveInfinityLocus U R i
    | .negativeInfinity => maxwellSameNegativeInfinityLocus U R i) \
      maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i)

/-- On the full raw fiber-regular part of either actual equal-infinity locus,
both genuine fixed-base one-sided quotient limits have the asserted sign. -/
theorem IsMaxwellPseudofunctionOn.directSameInfinityLimitsOn_fiberRegularLocus
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (s : MaxwellSameInfinitySign) :
    MaxwellDirectSameInfinityLimitsOn
      (maxwellChosenScalarValue R) i s
      (maxwellSameInfinityFiberRegularLocus U R i s) := by
  intro x hx
  have hnotMultivalued :
      x ∉ maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
        maxwellNegativeStepExtendedMultivaluedLocus U R i :=
    hx.2.2
  have hnotPositive :
      x ∉ maxwellPositiveStepExtendedMultivaluedLocus U R i := by
    intro hbad
    exact hnotMultivalued (Or.inl hbad)
  have hnotNegative :
      x ∉ maxwellNegativeStepExtendedMultivaluedLocus U R i := by
    intro hbad
    exact hnotMultivalued (Or.inr hbad)
  cases s with
  | positiveInfinity =>
      have hinfinity : x ∈ maxwellSamePositiveInfinityLocus U R i :=
        hx.2.1
      constructor
      · have hright :=
          hR.tendsto_oneSidedDifferenceQuotient_atTop_of_positiveInfinity
            hU i .positive hx.1 hinfinity.1 hnotPositive
        simpa [maxwellOneSidedDifferenceQuotient,
          maxwellRightDifferenceQuotient] using hright
      · have hleft :=
          hR.tendsto_oneSidedDifferenceQuotient_atTop_of_positiveInfinity
            hU i .negative hx.1 hinfinity.2 hnotNegative
        simpa [maxwellOneSidedDifferenceQuotient,
          maxwellReflectedLeftDifferenceQuotient, sub_eq_add_neg] using hleft

  | negativeInfinity =>
      have hinfinity : x ∈ maxwellSameNegativeInfinityLocus U R i :=
        hx.2.1
      constructor
      · have hright :=
          hR.tendsto_oneSidedDifferenceQuotient_atBot_of_negativeInfinity
            hU i .positive hx.1 hinfinity.1 hnotPositive
        simpa [maxwellOneSidedDifferenceQuotient,
          maxwellRightDifferenceQuotient] using hright
      · have hleft :=
          hR.tendsto_oneSidedDifferenceQuotient_atBot_of_negativeInfinity
            hU i .negative hx.1 hinfinity.2 hnotNegative
        simpa [maxwellOneSidedDifferenceQuotient,
          maxwellReflectedLeftDifferenceQuotient, sub_eq_add_neg] using hleft

/-- The closed-deletion locus is a subset of the raw fiber-regular locus, so
it inherits the same direct limits.  This is the form used by the chord
localization below. -/
theorem IsMaxwellPseudofunctionOn.directSameInfinityLimitsOn_regularLocus
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (s : MaxwellSameInfinitySign) :
    MaxwellDirectSameInfinityLimitsOn
      (maxwellChosenScalarValue R) i s
      (maxwellSameInfinityDirectLimitLocus U R i s) := by
  intro x hx
  apply hR.directSameInfinityLimitsOn_fiberRegularLocus hU i s
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro hbad
  exact hx.2.2 (subset_closure hbad)

/-! ## Lifting the chord mechanism across the small deletion -/

theorem interior_maxwellOneSidedExtendedMultivaluedExceptionalLocus_eq_empty
    {S : EuclideanSetFamily} {p : ℕ}
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p}
    (hsmall : MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i) :
    interior (maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i) = ∅ := by
  rw [maxwellOneSidedExtendedMultivaluedExceptionalLocus, closure_union]
  rw [interior_union_isClosed_of_interior_empty isClosed_closure]
  · exact hsmall.positiveBadLocus.closure_interior_eq_empty
  · exact hsmall.negativeBadLocus.closure_interior_eq_empty

/-- A chord mechanism proved on the open-domain part away from a closed
nowhere-dense set lifts to a locus contained in the closure of that domain. -/
theorem maxwellWS5AffineChordCrossingMechanism_of_off_closed
    {p : ℕ} {U E A : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign}
    (hUopen : IsOpen U) (hAclosure : A ⊆ closure U)
    (hEclosed : IsClosed E) (hEempty : interior E = ∅)
    (hregular : MaxwellWS5AffineChordCrossingMechanism f i s
      (U ∩ (A \ E))) :
    MaxwellWS5AffineChordCrossingMechanism f i s A := by
  intro V hVopen hVnonempty hVA
  obtain ⟨x, hxV⟩ := hVnonempty
  have hVU_nonempty : (V ∩ U).Nonempty :=
    (mem_closure_iff_nhds.mp (hAclosure (hVA hxV))) V
      (hVopen.mem_nhds hxV)
  have hVU_open : IsOpen (V ∩ U) := hVopen.inter hUopen
  obtain ⟨x₀, epsilon, hepsilon, hball⟩ :=
    exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
      hVU_open hVU_nonempty hEclosed hEempty
  let B : Set (RealEuclidean p) := Metric.ball x₀ epsilon
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBnonempty : B.Nonempty :=
    ⟨x₀, Metric.mem_ball_self hepsilon⟩
  have hBV : B ⊆ V := fun _ hx ↦ (hball hx).1.1
  have hBregular : B ⊆ U ∩ (A \ E) := by
    intro y hy
    exact ⟨(hball hy).1.2, hVA (hBV hy), (hball hy).2⟩
  obtain ⟨hobstruction⟩ :=
    hregular B hBopen hBnonempty hBregular
  exact ⟨hobstruction.mono hBV⟩

/-- The already-small one-sided extended-multivalued loci supply the full
positive equal-infinity affine-chord mechanism. -/
theorem IsMaxwellPseudofunctionOn.positiveInfinity_affineChord_of_oneSidedBadSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hUopen : IsOpen U)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (i : Fin p)
    (hsmall : MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i) :
    MaxwellWS5AffineChordCrossingMechanism
      (maxwellChosenScalarValue R) i .positiveInfinity
      (maxwellSamePositiveInfinityLocus U R i) := by
  let E : Set (RealEuclidean p) :=
    maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i
  let D : Set (RealEuclidean p) :=
    maxwellSameInfinityDirectLimitLocus U R i .positiveInfinity
  have hlimits : MaxwellDirectSameInfinityLimitsOn
      (maxwellChosenScalarValue R) i .positiveInfinity D := by
    exact hR.directSameInfinityLimitsOn_regularLocus hUopen i .positiveInfinity
  have hDclosure : D ⊆ closure U := by
    intro x hx
    exact subset_closure hx.1
  have hregular : MaxwellWS5AffineChordCrossingMechanism
      (maxwellChosenScalarValue R) i .positiveInfinity D :=
    maxwellWS5AffineChordCrossingMechanism_of_pseudofunction
      hC h21 hp hRmem hR hUopen hDclosure hlimits
  apply maxwellWS5AffineChordCrossingMechanism_of_off_closed
    hUopen
    (maxwellSamePositiveInfinityLocus_subset_closure_domain U R i)
    (isClosed_maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i)
    (interior_maxwellOneSidedExtendedMultivaluedExceptionalLocus_eq_empty
      hsmall)
  simpa only [D, E, maxwellSameInfinityDirectLimitLocus] using hregular

/-- The already-small one-sided extended-multivalued loci supply the full
negative equal-infinity affine-chord mechanism. -/
theorem IsMaxwellPseudofunctionOn.negativeInfinity_affineChord_of_oneSidedBadSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hUopen : IsOpen U)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (i : Fin p)
    (hsmall : MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i) :
    MaxwellWS5AffineChordCrossingMechanism
      (maxwellChosenScalarValue R) i .negativeInfinity
      (maxwellSameNegativeInfinityLocus U R i) := by
  let E : Set (RealEuclidean p) :=
    maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i
  let D : Set (RealEuclidean p) :=
    maxwellSameInfinityDirectLimitLocus U R i .negativeInfinity
  have hlimits : MaxwellDirectSameInfinityLimitsOn
      (maxwellChosenScalarValue R) i .negativeInfinity D := by
    exact hR.directSameInfinityLimitsOn_regularLocus hUopen i .negativeInfinity
  have hDclosure : D ⊆ closure U := by
    intro x hx
    exact subset_closure hx.1
  have hregular : MaxwellWS5AffineChordCrossingMechanism
      (maxwellChosenScalarValue R) i .negativeInfinity D :=
    maxwellWS5AffineChordCrossingMechanism_of_pseudofunction
      hC h21 hp hRmem hR hUopen hDclosure hlimits
  apply maxwellWS5AffineChordCrossingMechanism_of_off_closed
    hUopen
    (maxwellSameNegativeInfinityLocus_subset_closure_domain U R i)
    (isClosed_maxwellOneSidedExtendedMultivaluedExceptionalLocus U R i)
    (interior_maxwellOneSidedExtendedMultivaluedExceptionalLocus_eq_empty
      hsmall)
  simpa only [D, E, maxwellSameInfinityDirectLimitLocus] using hregular

/-! ## Empty interior and smallness of both equal-infinity loci -/

theorem maxwellEqualInfinityLoci_interior_eq_empty_of_oneSidedBadSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hUopen : IsOpen U) (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (hsmall : MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i) :
    interior (maxwellSamePositiveInfinityLocus U R i) = ∅ ∧
      interior (maxwellSameNegativeInfinityLocus U R i) = ∅ := by
  let C : Set (RealEuclidean p) :=
    maxwellChosenContinuityExceptionalLocus U R
  have hCsmall :=
    maxwellChosenContinuityBadLocusSmallness_of_theorem21
      hC h21 hp hRmem hR
  have hCclosed : IsClosed C :=
    isClosed_maxwellChosenContinuityExceptionalLocus U R
  have hCempty : interior C = ∅ :=
    hCsmall.exceptionalLocus_interior_eq_empty
  have hf : ContinuousOn (maxwellChosenScalarValue R) (U \ C) := by
    simpa only [C] using
      hR.continuousOn_chosenScalarValue_compl_exceptional
  have hpositive :=
    hR.positiveInfinity_affineChord_of_oneSidedBadSmallness
      hC h21 hp hUopen hRmem i hsmall
  have hnegative :=
    hR.negativeInfinity_affineChord_of_oneSidedBadSmallness
      hC h21 hp hUopen hRmem i hsmall
  constructor
  · exact interior_eq_empty_of_ws5AffineChordCrossing_off_closed
      hUopen
      (maxwellSamePositiveInfinityLocus_subset_closure_domain U R i)
      hCclosed hCempty hf hpositive
  · exact interior_eq_empty_of_ws5AffineChordCrossing_off_closed
      hUopen
      (maxwellSameNegativeInfinityLocus_subset_closure_domain U R i)
      hCclosed hCempty hf hnegative

/-- Once the two one-sided extended-multivalued loci have their existing
smallness package, both actual equal-infinity loci inherit full Charbonnel
smallness, including their closures. -/
theorem maxwellEqualInfinityLociSmallness_of_oneSidedBadSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hUopen : IsOpen U) (hUmem : U ∈ charbonnelClosure S p)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (hsmall : MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i) :
    MaxwellSlopeBaseLocusSmallness S
        (maxwellSamePositiveInfinityLocus U R i) ∧
      MaxwellSlopeBaseLocusSmallness S
        (maxwellSameNegativeInfinityLocus U R i) := by
  have hinterior :=
    maxwellEqualInfinityLoci_interior_eq_empty_of_oneSidedBadSmallness
      hC h21 hp hUopen hRmem hR i hsmall
  have hmembership := maxwellThreeHardSlopeCasesMembership
    hC.toPositiveArityWeakSetStructure hmem i hUmem hRmem
  exact ⟨
    maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
      h21 hp hmembership.samePositiveInfinity_mem hinterior.1,
    maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
      h21 hp hmembership.sameNegativeInfinity_mem hinterior.2⟩

end AbelFormalization
