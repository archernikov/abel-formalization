import AbelFormalization.MaxwellPositiveZeroTraceSmallness

/-!
# One-sided extended slope clusters and Maxwell's three hard cases

This file follows Figueiredo--Maxwell Lemmas 2.3.3 and 2.3.8--2.3.11.
The step variable is kept until after reciprocating the slope, so the four
one-sided infinite cluster loci distinguish the sign of the step from the
sign of infinity.  The finite trace, `+infinity`, and `-infinity` are then
assembled into an exact three-constructor extended fiber.

The analytic input to Lemma 2.3.3 is recorded as interval filling in a
finite trace fiber.  Fubini and Charbonnel Theorem 2.1 turn that geometric
input into nullity and empty interior.  The remaining cases in Lemma 2.3.11
are reduced to the two source contradictions: an affine chord crossing
for equal infinities and the translated identity between right and reflected
left difference quotients for unequal one-sided values.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Reciprocate the slope before tracing the step -/

/-- Put the step coordinate last after replacing a positive slope by its
positive reciprocal.  In these coordinates a positive zero trace is a
right-hand `+infinity` trace. -/
def maxwellPositiveReciprocalStepLastRelation {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean ((p + 1) + 1)) :=
  maxwellMoveStepToLastLinearEquiv p ''
    maxwellPositiveReciprocalRelation
      (maxwellDifferenceQuotientRelation U R i)

/-- The analogous step-last relation for negative slope reciprocals. -/
def maxwellNegativeReciprocalStepLastRelation {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean ((p + 1) + 1)) :=
  maxwellMoveStepToLastLinearEquiv p ''
    maxwellNegativeReciprocalRelation
      (maxwellDifferenceQuotientRelation U R i)

/-- Right-step reciprocal trace for slopes tending to `+infinity`. -/
def maxwellPositiveStepPositiveReciprocalTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  charbonnelPositiveZeroTrace
    (maxwellPositiveReciprocalStepLastRelation U R i)

/-- Right-step reciprocal trace for slopes tending to `-infinity`. -/
def maxwellPositiveStepNegativeReciprocalTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  charbonnelPositiveZeroTrace
    (maxwellNegativeReciprocalStepLastRelation U R i)

/-- Reflected-left-step reciprocal trace for slopes tending to `+infinity`. -/
def maxwellNegativeStepPositiveReciprocalTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  maxwellNegativeZeroTrace
    (maxwellPositiveReciprocalStepLastRelation U R i)

/-- Reflected-left-step reciprocal trace for slopes tending to `-infinity`. -/
def maxwellNegativeStepNegativeReciprocalTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellRelation p 1 :=
  maxwellNegativeZeroTrace
    (maxwellNegativeReciprocalStepLastRelation U R i)

/-- Bases with a right-step `+infinity` cluster. -/
def maxwellPositiveStepPositiveInfinityBase {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (maxwellPositiveStepPositiveReciprocalTrace U R i)

/-- Bases with a right-step `-infinity` cluster. -/
def maxwellPositiveStepNegativeInfinityBase {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (maxwellPositiveStepNegativeReciprocalTrace U R i)

/-- Bases with a left-step `+infinity` cluster. -/
def maxwellNegativeStepPositiveInfinityBase {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (maxwellNegativeStepPositiveReciprocalTrace U R i)

/-- Bases with a left-step `-infinity` cluster. -/
def maxwellNegativeStepNegativeInfinityBase {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (maxwellNegativeStepNegativeReciprocalTrace U R i)

/-! ## Exact extended fibers -/

/-- The compactified scalar values used in Maxwell's one-sided traces. -/
inductive MaxwellExtendedSlopeValue where
  | finite : ℝ → MaxwellExtendedSlopeValue
  | positiveInfinity : MaxwellExtendedSlopeValue
  | negativeInfinity : MaxwellExtendedSlopeValue
deriving DecidableEq

/-- The exact extended fiber built from a finite scalar relation and its two
reciprocal zero loci. -/
def maxwellExtendedSlopeFiber {p : ℕ}
    (G : MaxwellRelation p 1) (P N : Set (RealEuclidean p))
    (x : RealEuclidean p) : Set MaxwellExtendedSlopeValue :=
  fun s ↦ match s with
    | .finite y =>
        realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G
    | .positiveInfinity => x ∈ P
    | .negativeInfinity => x ∈ N

@[simp]
theorem finite_mem_maxwellExtendedSlopeFiber_iff {p : ℕ}
    (G : MaxwellRelation p 1) (P N : Set (RealEuclidean p))
    (x : RealEuclidean p) (y : ℝ) :
    MaxwellExtendedSlopeValue.finite y ∈
        maxwellExtendedSlopeFiber G P N x ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G :=
  Iff.rfl

@[simp]
theorem positiveInfinity_mem_maxwellExtendedSlopeFiber_iff {p : ℕ}
    (G : MaxwellRelation p 1) (P N : Set (RealEuclidean p))
    (x : RealEuclidean p) :
    MaxwellExtendedSlopeValue.positiveInfinity ∈
        maxwellExtendedSlopeFiber G P N x ↔ x ∈ P :=
  Iff.rfl

@[simp]
theorem negativeInfinity_mem_maxwellExtendedSlopeFiber_iff {p : ℕ}
    (G : MaxwellRelation p 1) (P N : Set (RealEuclidean p))
    (x : RealEuclidean p) :
    MaxwellExtendedSlopeValue.negativeInfinity ∈
        maxwellExtendedSlopeFiber G P N x ↔ x ∈ N :=
  Iff.rfl

/-- Bases at which a one-sided extended fiber contains two different values. -/
def maxwellOneSidedExtendedMultivaluedLocus {p : ℕ}
    (G : MaxwellRelation p 1) (P N : Set (RealEuclidean p)) :
    Set (RealEuclidean p) :=
  {x | ∃ a b : MaxwellExtendedSlopeValue,
    a ∈ maxwellExtendedSlopeFiber G P N x ∧
    b ∈ maxwellExtendedSlopeFiber G P N x ∧ a ≠ b}

/-- The exact finite/infinite case split for an extended multivalued fiber. -/
theorem maxwellOneSidedExtendedMultivaluedLocus_eq {p : ℕ}
    (G : MaxwellRelation p 1) (P N : Set (RealEuclidean p)) :
    maxwellOneSidedExtendedMultivaluedLocus G P N =
      maxwellMultivaluedLocus G ∪
        ((maxwellRelationDomain G ∩ P) ∪
          ((maxwellRelationDomain G ∩ N) ∪ (P ∩ N))) := by
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    cases a with
    | finite y₁ =>
        cases b with
        | finite y₂ =>
            apply Or.inl
            refine ⟨(fun _ : Fin 1 ↦ y₁), (fun _ : Fin 1 ↦ y₂),
              ha, hb, ?_⟩
            intro h
            apply hab
            exact congrArg MaxwellExtendedSlopeValue.finite (congrFun h 0)
        | positiveInfinity =>
            exact Or.inr <| Or.inl ⟨⟨(fun _ : Fin 1 ↦ y₁), ha⟩, hb⟩
        | negativeInfinity =>
            exact Or.inr <| Or.inr <| Or.inl
              ⟨⟨(fun _ : Fin 1 ↦ y₁), ha⟩, hb⟩
    | positiveInfinity =>
        cases b with
        | finite y₂ =>
            exact Or.inr <| Or.inl ⟨⟨(fun _ : Fin 1 ↦ y₂), hb⟩, ha⟩
        | positiveInfinity => exact False.elim (hab rfl)
        | negativeInfinity =>
            exact Or.inr <| Or.inr <| Or.inr ⟨ha, hb⟩
    | negativeInfinity =>
        cases b with
        | finite y₂ =>
            exact Or.inr <| Or.inr <| Or.inl
              ⟨⟨(fun _ : Fin 1 ↦ y₂), hb⟩, ha⟩
        | positiveInfinity =>
            exact Or.inr <| Or.inr <| Or.inr ⟨hb, ha⟩
        | negativeInfinity => exact False.elim (hab rfl)
  · intro hx
    rcases hx with hfinite | hfinitePositive | hfiniteNegative | hinfinities
    · rcases hfinite with ⟨y₁, y₂, hy₁, hy₂, hne⟩
      change realEuclideanAppend x y₁ ∈ G at hy₁
      change realEuclideanAppend x y₂ ∈ G at hy₂
      refine ⟨.finite (y₁ 0), .finite (y₂ 0), ?_, ?_, ?_⟩
      · apply (finite_mem_maxwellExtendedSlopeFiber_iff
          G P N x (y₁ 0)).2
        simpa only [← realEuclidean_one_eq_const y₁] using hy₁
      · apply (finite_mem_maxwellExtendedSlopeFiber_iff
          G P N x (y₂ 0)).2
        simpa only [← realEuclidean_one_eq_const y₂] using hy₂
      · intro h
        apply hne
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        exact MaxwellExtendedSlopeValue.finite.inj h
    · rcases hfinitePositive with ⟨⟨y, hy⟩, hxP⟩
      change realEuclideanAppend x y ∈ G at hy
      refine ⟨.finite (y 0), .positiveInfinity, ?_, hxP, by simp⟩
      apply (finite_mem_maxwellExtendedSlopeFiber_iff G P N x (y 0)).2
      simpa only [← realEuclidean_one_eq_const y] using hy
    · rcases hfiniteNegative with ⟨⟨y, hy⟩, hxN⟩
      change realEuclideanAppend x y ∈ G at hy
      refine ⟨.finite (y 0), .negativeInfinity, ?_, hxN, by simp⟩
      apply (finite_mem_maxwellExtendedSlopeFiber_iff G P N x (y 0)).2
      simpa only [← realEuclidean_one_eq_const y] using hy
    · exact ⟨.positiveInfinity, .negativeInfinity,
        hinfinities.1, hinfinities.2, by simp⟩

/-- The right-hand extended multivalued locus of the directional quotient. -/
def maxwellPositiveStepExtendedMultivaluedLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellOneSidedExtendedMultivaluedLocus
    (maxwellPositiveStepZeroTrace U R i)
    (maxwellPositiveStepPositiveInfinityBase U R i)
    (maxwellPositiveStepNegativeInfinityBase U R i)

/-- The left-hand extended multivalued locus of the directional quotient. -/
def maxwellNegativeStepExtendedMultivaluedLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellOneSidedExtendedMultivaluedLocus
    (maxwellNegativeStepZeroTrace U R i)
    (maxwellNegativeStepPositiveInfinityBase U R i)
    (maxwellNegativeStepNegativeInfinityBase U R i)

/-! ## Membership of the exact one-sided loci -/

theorem maxwellRelationDomain_mem_charbonnelClosure
    {S : EuclideanSetFamily} {p q : ℕ} (hp : 0 < p)
    {G : MaxwellRelation p q}
    (hG : G ∈ charbonnelClosure S (p + q)) :
    maxwellRelationDomain G ∈ charbonnelClosure S p := by
  rw [maxwellRelationDomain_eq_existentialProjection]
  exact charbonnelClosure_projection hp hG

theorem maxwellNegativeZeroTrace_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    {d : ℕ} (hd : 0 < d) {A : Set (RealEuclidean (d + 1))}
    (hA : A ∈ charbonnelClosure S (d + 1)) :
    maxwellNegativeZeroTrace A ∈ charbonnelClosure S d := by
  apply hmem.positiveZeroTrace_mem hd
  exact hC.ws4_linearEquiv (by omega) hA
    (maxwellLastCoordinateReflection d)

theorem maxwellPositiveReciprocalStepLastRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellPositiveReciprocalStepLastRelation U R i ∈
      charbonnelClosure S ((p + 1) + 1) := by
  have hQ := maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    hC i hU hR
  have hreciprocal := maxwellPositiveReciprocalRelation_mem_charbonnelClosure
    hC (by omega) hQ
  exact hC.ws4_linearEquiv (by omega) hreciprocal
    (maxwellMoveStepToLastLinearEquiv p)

theorem maxwellNegativeReciprocalStepLastRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellNegativeReciprocalStepLastRelation U R i ∈
      charbonnelClosure S ((p + 1) + 1) := by
  have hQ := maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    hC i hU hR
  have hreciprocal := maxwellNegativeReciprocalRelation_mem_charbonnelClosure
    hC (by omega) hQ
  exact hC.ws4_linearEquiv (by omega) hreciprocal
    (maxwellMoveStepToLastLinearEquiv p)

/-- Membership data for both one-sided finite traces and all four genuinely
one-sided infinity bases. -/
structure MaxwellOneSidedExtendedSlopeClusterMembership
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  positiveFiniteTrace_mem : maxwellPositiveStepZeroTrace U R i ∈
    charbonnelClosure S (p + 1)
  negativeFiniteTrace_mem : maxwellNegativeStepZeroTrace U R i ∈
    charbonnelClosure S (p + 1)
  positiveStepPositiveInfinity_mem :
    maxwellPositiveStepPositiveInfinityBase U R i ∈
      charbonnelClosure S p
  positiveStepNegativeInfinity_mem :
    maxwellPositiveStepNegativeInfinityBase U R i ∈
      charbonnelClosure S p
  negativeStepPositiveInfinity_mem :
    maxwellNegativeStepPositiveInfinityBase U R i ∈
      charbonnelClosure S p
  negativeStepNegativeInfinity_mem :
    maxwellNegativeStepNegativeInfinityBase U R i ∈
      charbonnelClosure S p
  positiveExtendedMultivalued_mem :
    maxwellPositiveStepExtendedMultivaluedLocus U R i ∈
      charbonnelClosure S p
  negativeExtendedMultivalued_mem :
    maxwellNegativeStepExtendedMultivaluedLocus U R i ∈
      charbonnelClosure S p

theorem maxwellOneSidedExtendedMultivaluedLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    {P N : Set (RealEuclidean p)}
    (hG : G ∈ charbonnelClosure S (p + 1))
    (hP : P ∈ charbonnelClosure S p)
    (hN : N ∈ charbonnelClosure S p) :
    maxwellOneSidedExtendedMultivaluedLocus G P N ∈
      charbonnelClosure S p := by
  rw [maxwellOneSidedExtendedMultivaluedLocus_eq]
  have hmulti := maxwellMultivaluedLocus_mem_charbonnelClosure hC hp hG
  have hdomain := maxwellRelationDomain_mem_charbonnelClosure hp hG
  have hdomainP := hC.ws1_inter hp hdomain hP
  have hdomainN := hC.ws1_inter hp hdomain hN
  have hPN := hC.ws1_inter hp hP hN
  exact charbonnelClosure_union hmulti
    (charbonnelClosure_union hdomainP
      (charbonnelClosure_union hdomainN hPN))

theorem maxwellOneSidedExtendedSlopeClusterMembership
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    MaxwellOneSidedExtendedSlopeClusterMembership S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  have hQ := maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    hC i hU hR
  have hstepLast : maxwellStepLastDifferenceQuotientRelation U R i ∈
      charbonnelClosure S ((p + 1) + 1) :=
    hC.ws4_linearEquiv (by omega) hQ
      (maxwellMoveStepToLastLinearEquiv p)
  have hpositiveFinite : maxwellPositiveStepZeroTrace U R i ∈
      charbonnelClosure S (p + 1) := by
    exact hmem.positiveZeroTrace_mem (by omega) hstepLast
  have hnegativeFinite : maxwellNegativeStepZeroTrace U R i ∈
      charbonnelClosure S (p + 1) := by
    exact maxwellNegativeZeroTrace_mem_charbonnelClosure hC hmem
      (by omega) hstepLast
  have hpositiveReciprocal :=
    maxwellPositiveReciprocalStepLastRelation_mem_charbonnelClosure
      hC i hU hR
  have hnegativeReciprocal :=
    maxwellNegativeReciprocalStepLastRelation_mem_charbonnelClosure
      hC i hU hR
  have hppTrace : maxwellPositiveStepPositiveReciprocalTrace U R i ∈
      charbonnelClosure S (p + 1) :=
    hmem.positiveZeroTrace_mem (by omega) hpositiveReciprocal
  have hpnTrace : maxwellPositiveStepNegativeReciprocalTrace U R i ∈
      charbonnelClosure S (p + 1) :=
    hmem.positiveZeroTrace_mem (by omega) hnegativeReciprocal
  have hnpTrace : maxwellNegativeStepPositiveReciprocalTrace U R i ∈
      charbonnelClosure S (p + 1) :=
    maxwellNegativeZeroTrace_mem_charbonnelClosure hC hmem
      (by omega) hpositiveReciprocal
  have hnnTrace : maxwellNegativeStepNegativeReciprocalTrace U R i ∈
      charbonnelClosure S (p + 1) :=
    maxwellNegativeZeroTrace_mem_charbonnelClosure hC hmem
      (by omega) hnegativeReciprocal
  have hpp := charbonnelZeroSection_mem_charbonnelClosure hp hppTrace
  have hpn := charbonnelZeroSection_mem_charbonnelClosure hp hpnTrace
  have hnp := charbonnelZeroSection_mem_charbonnelClosure hp hnpTrace
  have hnn := charbonnelZeroSection_mem_charbonnelClosure hp hnnTrace
  have hpositiveBad :=
    maxwellOneSidedExtendedMultivaluedLocus_mem_charbonnelClosure
      hC hp hpositiveFinite hpp hpn
  have hnegativeBad :=
    maxwellOneSidedExtendedMultivaluedLocus_mem_charbonnelClosure
      hC hp hnegativeFinite hnp hnn
  exact
    { positiveFiniteTrace_mem := hpositiveFinite
      negativeFiniteTrace_mem := hnegativeFinite
      positiveStepPositiveInfinity_mem := hpp
      positiveStepNegativeInfinity_mem := hpn
      negativeStepPositiveInfinity_mem := hnp
      negativeStepNegativeInfinity_mem := hnn
      positiveExtendedMultivalued_mem := hpositiveBad
      negativeExtendedMultivalued_mem := hnegativeBad }

/-! ## Fubini reduction for Lemma 2.3.3 -/

/-- The exact geometric output of the affine-segment/IVT argument in Lemma
2.3.3.  Every bad extended fiber contains a nondegenerate interval of finite
cluster values.  It contains no measure or empty-interior assertion. -/
def MaxwellExtendedSlopeIntervalFilling {p : ℕ}
    (G : MaxwellRelation p 1) (B : Set (RealEuclidean p)) : Prop :=
  ∀ x ∈ B, ∃ a b : ℝ, a < b ∧
    Set.Icc a b ⊆
      {y : ℝ | realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G}

theorem volume_eq_zero_of_extendedSlopeIntervalFilling
    {p : ℕ} {G : MaxwellRelation p 1}
    {B : Set (RealEuclidean p)}
    (hGclosed : IsClosed G)
    (hGnull : (volume : Measure (RealEuclidean (p + 1))) G = 0)
    (hfilling : MaxwellExtendedSlopeIntervalFilling G B) :
    (volume : Measure (RealEuclidean p)) B = 0 := by
  let T := maxwellScalarRelationProductCoordinates G
  have hTmeasurable : MeasurableSet T := by
    exact (maxwellScalarRelationProductEquiv p).measurableEmbedding
      |>.measurableSet_image' hGclosed.measurableSet
  have hTnull : (volume : Measure (RealEuclidean p × ℝ)) T = 0 :=
    maxwellScalarRelationProductCoordinates_volume_eq_zero hGnull
  apply volume_base_eq_zero_of_prod_eq_zero_of_sections_ne_zero
    hTmeasurable (B := B) _ hTnull
  intro x hx
  rcases hfilling x hx with ⟨a, b, hab, hIcc⟩
  have hIccVolume : (volume : Measure ℝ) (Set.Icc a b) ≠ 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_ne_zero_iff]
    exact sub_pos.mpr hab
  intro hsection
  apply hIccVolume
  apply measure_mono_null hIcc
  have hfiber : Prod.mk x ⁻¹' T =
      {y : ℝ | realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ G} := by
    ext y
    exact mem_maxwellScalarRelationProductCoordinates_iff G x y
  rwa [← hfiber]

/-- Standard membership, nullity, empty-interior, and closure output for a
base exceptional locus. -/
structure MaxwellSlopeBaseLocusSmallness
    (S : EuclideanSetFamily) {p : ℕ}
    (B : Set (RealEuclidean p)) : Prop where
  locus_mem : B ∈ charbonnelClosure S p
  locus_volume_eq_zero : (volume : Measure (RealEuclidean p)) B = 0
  locus_interior_eq_empty : interior B = ∅
  closure_mem : closure B ∈ charbonnelClosure S p
  closure_volume_eq_zero :
    (volume : Measure (RealEuclidean p)) (closure B) = 0
  closure_interior_eq_empty : interior (closure B) = ∅

theorem maxwellSlopeBaseLocusSmallness_of_volume_eq_zero
    {S : EuclideanSetFamily}
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {B : Set (RealEuclidean p)}
    (hBmem : B ∈ charbonnelClosure S p)
    (hBnull : (volume : Measure (RealEuclidean p)) B = 0) :
    MaxwellSlopeBaseLocusSmallness S B := by
  have hBempty := (h21 hp hBmem).1.mpr hBnull
  have hclosureMem := charbonnelClosure_topologicalClosure hBmem
  have hclosureEmpty := (h21 hp hBmem).2.1.mp hBnull
  have hclosureNull := (h21 hp hBmem).2.2.mp hclosureEmpty
  exact
    { locus_mem := hBmem
      locus_volume_eq_zero := hBnull
      locus_interior_eq_empty := hBempty
      closure_mem := hclosureMem
      closure_volume_eq_zero := hclosureNull
      closure_interior_eq_empty := hclosureEmpty }

theorem maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
    {S : EuclideanSetFamily}
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {B : Set (RealEuclidean p)}
    (hBmem : B ∈ charbonnelClosure S p)
    (hBempty : interior B = ∅) :
    MaxwellSlopeBaseLocusSmallness S B := by
  exact maxwellSlopeBaseLocusSmallness_of_volume_eq_zero h21 hp hBmem
    ((h21 hp hBmem).1.mp hBempty)

theorem maxwellExtendedSlopeBadLocusSmallness
    {S : EuclideanSetFamily}
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    {B : Set (RealEuclidean p)}
    (hBmem : B ∈ charbonnelClosure S p)
    (hGclosed : IsClosed G)
    (hGnull : (volume : Measure (RealEuclidean (p + 1))) G = 0)
    (hfilling : MaxwellExtendedSlopeIntervalFilling G B) :
    MaxwellSlopeBaseLocusSmallness S B := by
  exact maxwellSlopeBaseLocusSmallness_of_volume_eq_zero h21 hp hBmem
    (volume_eq_zero_of_extendedSlopeIntervalFilling
      hGclosed hGnull hfilling)

/-- Both one-sided applications of source Lemma 2.3.3, including finite and
infinite pairs of cluster values. -/
structure MaxwellOneSidedExtendedSlopeBadLociSmallness
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  traceSmallness : MaxwellTwoSidedZeroTraceSmallness S
    (maxwellStepLastDifferenceQuotientRelation U R i)
  clusterMembership :
    MaxwellOneSidedExtendedSlopeClusterMembership S U R i
  positiveBadLocus : MaxwellSlopeBaseLocusSmallness S
    (maxwellPositiveStepExtendedMultivaluedLocus U R i)
  negativeBadLocus : MaxwellSlopeBaseLocusSmallness S
    (maxwellNegativeStepExtendedMultivaluedLocus U R i)

theorem maxwellOneSidedExtendedSlopeBadLociSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hquotientEmpty :
      interior (maxwellDifferenceQuotientRelation U R i) = ∅)
    (hpositiveFilling : MaxwellExtendedSlopeIntervalFilling
      (maxwellPositiveStepZeroTrace U R i)
      (maxwellPositiveStepExtendedMultivaluedLocus U R i))
    (hnegativeFilling : MaxwellExtendedSlopeIntervalFilling
      (maxwellNegativeStepZeroTrace U R i)
      (maxwellNegativeStepExtendedMultivaluedLocus U R i)) :
    MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  have htrace := maxwellDifferenceQuotientPositiveZeroTraceSmallness
    hC hmem h21 h22 i hU hR hquotientEmpty
  have hclusters := maxwellOneSidedExtendedSlopeClusterMembership
    hC hmem i hU hR
  have hpositive := maxwellExtendedSlopeBadLocusSmallness h21 hp
    hclusters.positiveExtendedMultivalued_mem
    (isClosed_maxwellPositiveStepZeroTrace U R i)
    htrace.positiveTrace_volume_eq_zero hpositiveFilling
  have hnegative := maxwellExtendedSlopeBadLocusSmallness h21 hp
    hclusters.negativeExtendedMultivalued_mem
    (isClosed_maxwellNegativeStepZeroTrace U R i)
    htrace.negativeTrace_volume_eq_zero hnegativeFilling
  exact
    { traceSmallness := htrace
      clusterMembership := hclusters
      positiveBadLocus := hpositive
      negativeBadLocus := hnegative }

/-! ## Cross-side finite and extended disagreement -/

/-- Two different finite values, one from each of two scalar relations. -/
def maxwellCrossFiniteDisagreementLocus {p : ℕ}
    (G H : MaxwellRelation p 1) : Set (RealEuclidean p) :=
  {x | ∃ a b : ℝ,
    realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈ G ∧
    realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈ H ∧ a ≠ b}

/-- Incidence presentation of cross-side finite disagreement. -/
def maxwellCrossFiniteDisagreementIncidence {p : ℕ}
    (G H : MaxwellRelation p 1) : Set (RealEuclidean (p + 2)) :=
  (maxwellFiberPairFirstLinearMap p ⁻¹' G ∩
    maxwellFiberPairSecondLinearMap p ⁻¹' H) ∩
    maxwellFiberPairDistinctConstraint p

@[simp]
theorem realEuclideanAppend_mem_maxwellCrossFiniteDisagreementIncidence_iff
    {p : ℕ} (G H : MaxwellRelation p 1)
    (x : RealEuclidean p) (y : RealEuclidean 2) :
    realEuclideanAppend x y ∈
        maxwellCrossFiniteDisagreementIncidence G H ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ y 0) ∈ G ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y 1) ∈ H ∧
      y 0 ≠ y 1 := by
  simp only [maxwellCrossFiniteDisagreementIncidence, Set.mem_inter_iff,
    Set.mem_preimage, maxwellFiberPairFirstLinearMap_append,
    maxwellFiberPairSecondLinearMap_append]
  simp only [maxwellFiberPairDistinctConstraint, Set.mem_union,
    Set.mem_setOf_eq, map_sub, MvPolynomial.eval_X,
    maxwellFiberPairFirstValueIndex, maxwellFiberPairSecondValueIndex,
    realEuclideanAppend_natAdd, sub_pos, sub_neg]
  constructor
  · rintro ⟨⟨hy₁, hy₂⟩, hlt | hgt⟩
    · exact ⟨hy₁, hy₂, ne_of_lt hlt⟩
    · exact ⟨hy₁, hy₂, ne_of_gt hgt⟩
  · rintro ⟨hy₁, hy₂, hne⟩
    refine ⟨⟨hy₁, hy₂⟩, ?_⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt

theorem realEuclideanExistentialProjection_crossFiniteDisagreementIncidence
    {p : ℕ} (G H : MaxwellRelation p 1) :
    realEuclideanExistentialProjection
        (maxwellCrossFiniteDisagreementIncidence G H) =
      maxwellCrossFiniteDisagreementLocus G H := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    realEuclideanAppend_mem_maxwellCrossFiniteDisagreementIncidence_iff,
    maxwellCrossFiniteDisagreementLocus]
  constructor
  · rintro ⟨y, hy₁, hy₂, hne⟩
    exact ⟨y 0, y 1, hy₁, hy₂, hne⟩
  · rintro ⟨a, b, ha, hb, hne⟩
    exact ⟨![a, b], ha, hb, hne⟩

theorem maxwellCrossFiniteDisagreementLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G H : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + 1))
    (hH : H ∈ charbonnelClosure S (p + 1)) :
    maxwellCrossFiniteDisagreementLocus G H ∈
      charbonnelClosure S p := by
  have hfirst := hC.linear_preimage_mem (by omega) (by omega) hG
    (maxwellFiberPairFirstLinearMap p)
  have hsecond := hC.linear_preimage_mem (by omega) (by omega) hH
    (maxwellFiberPairSecondLinearMap p)
  have hdistinct : maxwellFiberPairDistinctConstraint p ∈
      charbonnelClosure S (p + 2) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellFiberPairDistinctConstraint p)
  have hincidence : maxwellCrossFiniteDisagreementIncidence G H ∈
      charbonnelClosure S (p + 2) :=
    hC.ws1_inter (by omega)
      (hC.ws1_inter (by omega) hfirst hsecond) hdistinct
  rw [← realEuclideanExistentialProjection_crossFiniteDisagreementIncidence
    G H]
  exact charbonnelClosure_projection hp hincidence

/-- Bases carrying different extended values on the two step sides. -/
def maxwellExtendedSlopeDisagreementLocus {p : ℕ}
    (Gpos : MaxwellRelation p 1) (Ppos Npos : Set (RealEuclidean p))
    (Gneg : MaxwellRelation p 1) (Pneg Nneg : Set (RealEuclidean p)) :
    Set (RealEuclidean p) :=
  {x | ∃ a b : MaxwellExtendedSlopeValue,
    a ∈ maxwellExtendedSlopeFiber Gpos Ppos Npos x ∧
    b ∈ maxwellExtendedSlopeFiber Gneg Pneg Nneg x ∧ a ≠ b}

/-- The finite/infinite decomposition of cross-side disagreement. -/
theorem maxwellExtendedSlopeDisagreementLocus_eq {p : ℕ}
    (Gpos : MaxwellRelation p 1) (Ppos Npos : Set (RealEuclidean p))
    (Gneg : MaxwellRelation p 1) (Pneg Nneg : Set (RealEuclidean p)) :
    maxwellExtendedSlopeDisagreementLocus
        Gpos Ppos Npos Gneg Pneg Nneg =
      maxwellCrossFiniteDisagreementLocus Gpos Gneg ∪
        ((maxwellRelationDomain Gpos ∩ (Pneg ∪ Nneg)) ∪
          (((Ppos ∪ Npos) ∩ maxwellRelationDomain Gneg) ∪
            ((Ppos ∩ Nneg) ∪ (Npos ∩ Pneg)))) := by
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    cases a with
    | finite y₁ =>
        cases b with
        | finite y₂ =>
            apply Or.inl
            refine ⟨y₁, y₂, ha, hb, ?_⟩
            intro h
            exact hab (congrArg MaxwellExtendedSlopeValue.finite h)
        | positiveInfinity =>
            exact Or.inr <| Or.inl
              ⟨⟨(fun _ : Fin 1 ↦ y₁), ha⟩, Or.inl hb⟩
        | negativeInfinity =>
            exact Or.inr <| Or.inl
              ⟨⟨(fun _ : Fin 1 ↦ y₁), ha⟩, Or.inr hb⟩
    | positiveInfinity =>
        cases b with
        | finite y₂ =>
            exact Or.inr <| Or.inr <| Or.inl
              ⟨Or.inl ha, ⟨(fun _ : Fin 1 ↦ y₂), hb⟩⟩
        | positiveInfinity => exact False.elim (hab rfl)
        | negativeInfinity =>
            exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ha, hb⟩
    | negativeInfinity =>
        cases b with
        | finite y₂ =>
            exact Or.inr <| Or.inr <| Or.inl
              ⟨Or.inr ha, ⟨(fun _ : Fin 1 ↦ y₂), hb⟩⟩
        | positiveInfinity =>
            exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨ha, hb⟩
        | negativeInfinity => exact False.elim (hab rfl)
  · intro hx
    rcases hx with hfinite | hfiniteInfinite | hinfiniteFinite |
      hpositiveNegative | hnegativePositive
    · rcases hfinite with ⟨a, b, ha, hb, hab⟩
      exact ⟨.finite a, .finite b, ha, hb, by
        intro h
        exact hab (MaxwellExtendedSlopeValue.finite.inj h)⟩
    · rcases hfiniteInfinite with ⟨⟨y, hy⟩, hxP | hxN⟩
      · refine ⟨.finite (y 0), .positiveInfinity, ?_, hxP, by simp⟩
        change realEuclideanAppend x y ∈ Gpos at hy
        apply (finite_mem_maxwellExtendedSlopeFiber_iff
          Gpos Ppos Npos x (y 0)).2
        simpa only [← realEuclidean_one_eq_const y] using hy
      · refine ⟨.finite (y 0), .negativeInfinity, ?_, hxN, by simp⟩
        change realEuclideanAppend x y ∈ Gpos at hy
        apply (finite_mem_maxwellExtendedSlopeFiber_iff
          Gpos Ppos Npos x (y 0)).2
        simpa only [← realEuclidean_one_eq_const y] using hy
    · rcases hinfiniteFinite with ⟨hxP | hxN, ⟨y, hy⟩⟩
      · refine ⟨.positiveInfinity, .finite (y 0), hxP, ?_, by simp⟩
        change realEuclideanAppend x y ∈ Gneg at hy
        apply (finite_mem_maxwellExtendedSlopeFiber_iff
          Gneg Pneg Nneg x (y 0)).2
        simpa only [← realEuclidean_one_eq_const y] using hy
      · refine ⟨.negativeInfinity, .finite (y 0), hxN, ?_, by simp⟩
        change realEuclideanAppend x y ∈ Gneg at hy
        apply (finite_mem_maxwellExtendedSlopeFiber_iff
          Gneg Pneg Nneg x (y 0)).2
        simpa only [← realEuclidean_one_eq_const y] using hy
    · exact ⟨.positiveInfinity, .negativeInfinity,
        hpositiveNegative.1, hpositiveNegative.2, by simp⟩
    · exact ⟨.negativeInfinity, .positiveInfinity,
        hnegativePositive.1, hnegativePositive.2, by simp⟩

theorem maxwellExtendedSlopeDisagreementLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {Gpos Gneg : MaxwellRelation p 1}
    {Ppos Npos Pneg Nneg : Set (RealEuclidean p)}
    (hGpos : Gpos ∈ charbonnelClosure S (p + 1))
    (hGneg : Gneg ∈ charbonnelClosure S (p + 1))
    (hPpos : Ppos ∈ charbonnelClosure S p)
    (hNpos : Npos ∈ charbonnelClosure S p)
    (hPneg : Pneg ∈ charbonnelClosure S p)
    (hNneg : Nneg ∈ charbonnelClosure S p) :
    maxwellExtendedSlopeDisagreementLocus
        Gpos Ppos Npos Gneg Pneg Nneg ∈
      charbonnelClosure S p := by
  rw [maxwellExtendedSlopeDisagreementLocus_eq]
  have hfinite := maxwellCrossFiniteDisagreementLocus_mem_charbonnelClosure
    hC hp hGpos hGneg
  have hdomainPos := maxwellRelationDomain_mem_charbonnelClosure hp hGpos
  have hdomainNeg := maxwellRelationDomain_mem_charbonnelClosure hp hGneg
  have hPnegNneg := charbonnelClosure_union hPneg hNneg
  have hPposNpos := charbonnelClosure_union hPpos hNpos
  have hfiniteInfinite := hC.ws1_inter hp hdomainPos hPnegNneg
  have hinfiniteFinite := hC.ws1_inter hp hPposNpos hdomainNeg
  have hpositiveNegative := hC.ws1_inter hp hPpos hNneg
  have hnegativePositive := hC.ws1_inter hp hNpos hPneg
  exact charbonnelClosure_union hfinite
    (charbonnelClosure_union hfiniteInfinite
      (charbonnelClosure_union hinfiniteFinite
        (charbonnelClosure_union hpositiveNegative hnegativePositive)))

/-! ## The three residual slope cases -/

/-- Both one-sided extended values are `+infinity`. -/
def maxwellSamePositiveInfinityLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellPositiveStepPositiveInfinityBase U R i ∩
    maxwellNegativeStepPositiveInfinityBase U R i

/-- Both one-sided extended values are `-infinity`. -/
def maxwellSameNegativeInfinityLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellPositiveStepNegativeInfinityBase U R i ∩
    maxwellNegativeStepNegativeInfinityBase U R i

/-- A right-hand cluster value differs from a left-hand cluster value. -/
def maxwellOneSidedSlopeDisagreementLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellExtendedSlopeDisagreementLocus
    (maxwellPositiveStepZeroTrace U R i)
    (maxwellPositiveStepPositiveInfinityBase U R i)
    (maxwellPositiveStepNegativeInfinityBase U R i)
    (maxwellNegativeStepZeroTrace U R i)
    (maxwellNegativeStepPositiveInfinityBase U R i)
    (maxwellNegativeStepNegativeInfinityBase U R i)

/-- Union of the three hard cases in Lemma 2.3.11. -/
def maxwellThreeHardSlopeCasesLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean p) :=
  maxwellSamePositiveInfinityLocus U R i ∪
    maxwellSameNegativeInfinityLocus U R i ∪
    maxwellOneSidedSlopeDisagreementLocus U R i

/-- The remaining pointwise analytic input in Lemmas 2.3.9--2.3.11.
Each side has an extended cluster value, while no finite value occurs on both
sides.  The latter clause is exactly what the mean-value/derivative argument
proves at a point placed in the nondifferentiability locus. -/
def MaxwellNondifferentiableOneSidedClusterData {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (B : Set (RealEuclidean p)) : Prop :=
  ∀ x ∈ B,
    (maxwellExtendedSlopeFiber
      (maxwellPositiveStepZeroTrace U R i)
      (maxwellPositiveStepPositiveInfinityBase U R i)
      (maxwellPositiveStepNegativeInfinityBase U R i) x).Nonempty ∧
    (maxwellExtendedSlopeFiber
      (maxwellNegativeStepZeroTrace U R i)
      (maxwellNegativeStepPositiveInfinityBase U R i)
      (maxwellNegativeStepNegativeInfinityBase U R i) x).Nonempty ∧
    ∀ y : ℝ,
      ¬ (MaxwellExtendedSlopeValue.finite y ∈
          maxwellExtendedSlopeFiber
            (maxwellPositiveStepZeroTrace U R i)
            (maxwellPositiveStepPositiveInfinityBase U R i)
            (maxwellPositiveStepNegativeInfinityBase U R i) x ∧
        MaxwellExtendedSlopeValue.finite y ∈
          maxwellExtendedSlopeFiber
            (maxwellNegativeStepZeroTrace U R i)
            (maxwellNegativeStepPositiveInfinityBase U R i)
            (maxwellNegativeStepNegativeInfinityBase U R i) x)

/-- The pointwise extended-value classification gives exactly the three hard
cases, without a smallness premise. -/
theorem MaxwellNondifferentiableOneSidedClusterData.subset_threeHardCases
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {i : Fin p}
    (h : MaxwellNondifferentiableOneSidedClusterData U R i B) :
    B ⊆ maxwellThreeHardSlopeCasesLocus U R i := by
  intro x hx
  rcases h x hx with ⟨⟨a, ha⟩, ⟨b, hb⟩, hfinite⟩
  simp only [maxwellThreeHardSlopeCasesLocus, Set.mem_union]
  by_cases hab : a = b
  · subst b
    cases a with
    | finite y => exact False.elim (hfinite y ⟨ha, hb⟩)
    | positiveInfinity => exact Or.inl <| Or.inl ⟨ha, hb⟩
    | negativeInfinity => exact Or.inl <| Or.inr ⟨ha, hb⟩
  · exact Or.inr ⟨a, b, ha, hb, hab⟩

structure MaxwellThreeHardSlopeCasesMembership
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  clusters : MaxwellOneSidedExtendedSlopeClusterMembership S U R i
  samePositiveInfinity_mem : maxwellSamePositiveInfinityLocus U R i ∈
    charbonnelClosure S p
  sameNegativeInfinity_mem : maxwellSameNegativeInfinityLocus U R i ∈
    charbonnelClosure S p
  disagreement_mem : maxwellOneSidedSlopeDisagreementLocus U R i ∈
    charbonnelClosure S p
  union_mem : maxwellThreeHardSlopeCasesLocus U R i ∈
    charbonnelClosure S p

theorem maxwellThreeHardSlopeCasesMembership
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    MaxwellThreeHardSlopeCasesMembership S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  have hclusters := maxwellOneSidedExtendedSlopeClusterMembership
    hC hmem i hU hR
  have hpositive := hC.ws1_inter hp
    hclusters.positiveStepPositiveInfinity_mem
    hclusters.negativeStepPositiveInfinity_mem
  have hnegative := hC.ws1_inter hp
    hclusters.positiveStepNegativeInfinity_mem
    hclusters.negativeStepNegativeInfinity_mem
  have hdisagreement :=
    maxwellExtendedSlopeDisagreementLocus_mem_charbonnelClosure hC hp
      hclusters.positiveFiniteTrace_mem
      hclusters.negativeFiniteTrace_mem
      hclusters.positiveStepPositiveInfinity_mem
      hclusters.positiveStepNegativeInfinity_mem
      hclusters.negativeStepPositiveInfinity_mem
      hclusters.negativeStepNegativeInfinity_mem
  have hunion := charbonnelClosure_union
    (charbonnelClosure_union hpositive hnegative) hdisagreement
  exact
    { clusters := hclusters
      samePositiveInfinity_mem := hpositive
      sameNegativeInfinity_mem := hnegative
      disagreement_mem := hdisagreement
      union_mem := hunion }

/-! ## The affine-chord contradiction for equal infinities -/

def maxwellAffineChordPath {p : ℕ}
    (a b : RealEuclidean p) (t : ℝ) : RealEuclidean p :=
  a + t • (b - a)

def maxwellAffineChordValue {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p)
    (t : ℝ) : ℝ :=
  (1 - t) * f a + t * f b

def maxwellAffineChordError {p : ℕ}
    (f : RealEuclidean p → ℝ) (a b : RealEuclidean p)
    (t : ℝ) : ℝ :=
  f (maxwellAffineChordPath a b t) - maxwellAffineChordValue f a b t

inductive MaxwellSameInfinitySign where
  | positiveInfinity
  | negativeInfinity
deriving DecidableEq

/-- Multiplying by this sign puts the two source crossings in the order
`negative` then `positive` along the chord. -/
def maxwellInfinityChordOrientation : MaxwellSameInfinitySign → ℝ
  | .positiveInfinity => -1
  | .negativeInfinity => 1

theorem maxwellInfinityChordOrientation_ne_zero
    (s : MaxwellSameInfinitySign) :
    maxwellInfinityChordOrientation s ≠ 0 := by
  cases s <;> norm_num [maxwellInfinityChordOrientation]

theorem continuousOn_maxwellAffineChordError
    {p : ℕ} {f : RealEuclidean p → ℝ}
    {W : Set (RealEuclidean p)} {a b : RealEuclidean p}
    (hf : ContinuousOn f W)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellAffineChordPath a b t ∈ W)
    {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) :
    ContinuousOn (maxwellAffineChordError f a b) (Set.Icc u v) := by
  have hpath : Continuous (maxwellAffineChordPath a b) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hmaps : MapsTo (maxwellAffineChordPath a b) (Set.Icc u v) W := by
    intro t ht
    exact hsegment t ⟨le_trans hu ht.1, le_trans ht.2 hv⟩
  have hfunction : ContinuousOn
      (fun t ↦ f (maxwellAffineChordPath a b t)) (Set.Icc u v) :=
    hf.comp hpath.continuousOn hmaps
  have hchord : Continuous (maxwellAffineChordValue f a b) := by
    exact ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  exact hfunction.sub hchord.continuousOn

/-- The exact contradiction produced after WS5 isolates an affine chord.
The endpoint relation is a coordinate chord; the two strict inequalities are
the two one-sided infinite limits; `isolated` is the finite-component output.
No smallness conclusion occurs in this witness. -/
structure MaxwellAffineChordCrossingObstruction {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (s : MaxwellSameInfinitySign)
    (W : Set (RealEuclidean p)) where
  a : RealEuclidean p
  b : RealEuclidean p
  step : ℝ
  step_pos : 0 < step
  b_eq : b = a + step • (Pi.single i 1 : RealEuclidean p)
  a_mem : a ∈ W
  b_mem : b ∈ W
  segment_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    maxwellAffineChordPath a b t ∈ W
  u : ℝ
  v : ℝ
  u_pos : 0 < u
  u_lt_v : u < v
  v_lt_one : v < 1
  oriented_left_neg :
    maxwellInfinityChordOrientation s *
      maxwellAffineChordError f a b u < 0
  oriented_right_pos :
    0 < maxwellInfinityChordOrientation s *
      maxwellAffineChordError f a b v
  isolated : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    maxwellAffineChordError f a b t ≠ 0

theorem MaxwellAffineChordCrossingObstruction.false
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign} {W : Set (RealEuclidean p)}
    (hf : ContinuousOn f W)
    (h : MaxwellAffineChordCrossingObstruction f i s W) : False := by
  let F : ℝ → ℝ := fun t ↦
    maxwellInfinityChordOrientation s *
      maxwellAffineChordError f h.a h.b t
  have herror : ContinuousOn
      (maxwellAffineChordError f h.a h.b) (Set.Icc h.u h.v) :=
    continuousOn_maxwellAffineChordError hf h.segment_mem
      (le_of_lt h.u_pos) (le_of_lt h.v_lt_one)
  have hF : ContinuousOn F (Set.Icc h.u h.v) :=
    continuousOn_const.mul herror
  have hzeroBetween : (0 : ℝ) ∈ Set.Icc (F h.u) (F h.v) :=
    ⟨le_of_lt h.oriented_left_neg, le_of_lt h.oriented_right_pos⟩
  obtain ⟨t, ht, hFt⟩ :=
    (intermediate_value_Icc (le_of_lt h.u_lt_v) hF) hzeroBetween
  have htInterior : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le h.u_pos ht.1, lt_of_le_of_lt ht.2 h.v_lt_one⟩
  apply h.isolated t htInterior
  exact (mul_eq_zero.mp hFt).resolve_left
    (maxwellInfinityChordOrientation_ne_zero s)

/-- Source mechanism for the two `+infinity` values and the two `-infinity`
values.  If the locus contained an open set, WS5 and the
two endpoint limits would extract the preceding chord obstruction. -/
def MaxwellWS5AffineChordCrossingMechanism {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (s : MaxwellSameInfinitySign) (A : Set (RealEuclidean p)) : Prop :=
  ∀ V : Set (RealEuclidean p), IsOpen V → V.Nonempty → V ⊆ A →
    Nonempty (MaxwellAffineChordCrossingObstruction f i s V)

theorem interior_eq_empty_of_ws5AffineChordCrossing
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign} {A : Set (RealEuclidean p)}
    (hf : ContinuousOn f A)
    (hextract : MaxwellWS5AffineChordCrossingMechanism f i s A) :
    interior A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hnonempty : (interior A).Nonempty := ⟨x, hx⟩
  rcases hextract (interior A) isOpen_interior hnonempty interior_subset with
    ⟨h⟩
  exact MaxwellAffineChordCrossingObstruction.false
    (hf.mono interior_subset) h

/-! ## The translated one-sided identity for differing slopes -/

def maxwellRightDifferenceQuotient {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (x : RealEuclidean p) (t : ℝ) : ℝ :=
  (f (x + t • (Pi.single i 1 : RealEuclidean p)) - f x) / t

/-- `g⁻(x,t)=g(x,-t)` in the notation of the source. -/
def maxwellReflectedLeftDifferenceQuotient {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (x : RealEuclidean p) (t : ℝ) : ℝ :=
  (f (x - t • (Pi.single i 1 : RealEuclidean p)) - f x) / (-t)

/-- The algebraic identity at the heart of the `U₃` contradiction. -/
theorem maxwellRightDifferenceQuotient_eq_translatedReflectedLeft
    {p : ℕ} (f : RealEuclidean p → ℝ) (i : Fin p)
    (x : RealEuclidean p) (t : ℝ) :
    maxwellRightDifferenceQuotient f i x t =
      maxwellReflectedLeftDifferenceQuotient f i
        (x + t • (Pi.single i 1 : RealEuclidean p)) t := by
  simp only [maxwellRightDifferenceQuotient,
    maxwellReflectedLeftDifferenceQuotient]
  have hcancel :
      x + t • (Pi.single i 1 : RealEuclidean p) -
          t • (Pi.single i 1 : RealEuclidean p) = x := by
    abel
  rw [hcancel]
  ring

inductive MaxwellSlopeSeparationOrientation where
  | rightBelowLeft
  | leftBelowRight
deriving DecidableEq

def MaxwellOrientedSlopeSeparation
    (o : MaxwellSlopeSeparationOrientation) (right left cutoff : ℝ) : Prop :=
  match o with
  | .rightBelowLeft => right < cutoff ∧ cutoff < left
  | .leftBelowRight => left < cutoff ∧ cutoff < right

/-- Uniform separation on an open set, evaluated at a point and its
coordinate translate.  This is precisely the witness contradicted by the
translated identity. -/
structure MaxwellTranslatedSlopeSeparationObstruction {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (V : Set (RealEuclidean p)) where
  x : RealEuclidean p
  step : ℝ
  cutoff : ℝ
  orientation : MaxwellSlopeSeparationOrientation
  step_pos : 0 < step
  x_mem : x ∈ V
  translated_mem :
    x + step • (Pi.single i 1 : RealEuclidean p) ∈ V
  separated : MaxwellOrientedSlopeSeparation orientation
    (maxwellRightDifferenceQuotient f i x step)
    (maxwellReflectedLeftDifferenceQuotient f i
      (x + step • (Pi.single i 1 : RealEuclidean p)) step)
    cutoff

theorem MaxwellTranslatedSlopeSeparationObstruction.false
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {V : Set (RealEuclidean p)}
    (h : MaxwellTranslatedSlopeSeparationObstruction f i V) : False := by
  rcases h with ⟨x, step, cutoff, o, _hstep, _hx,
    _htranslated, hsep⟩
  have heq := maxwellRightDifferenceQuotient_eq_translatedReflectedLeft
    f i x step
  cases o <;>
    simp only [MaxwellOrientedSlopeSeparation] at hsep <;>
    linarith [heq]

/-- If a differing-slope locus had interior, continuity of the two unique
one-sided extended values would give a uniform cutoff and a small translate
remaining in that interior. -/
def MaxwellTranslatedOneSidedSeparationMechanism {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (A : Set (RealEuclidean p)) : Prop :=
  ∀ V : Set (RealEuclidean p), IsOpen V → V.Nonempty → V ⊆ A →
    Nonempty (MaxwellTranslatedSlopeSeparationObstruction f i V)

theorem interior_eq_empty_of_translatedOneSidedSeparation
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {A : Set (RealEuclidean p)}
    (hextract : MaxwellTranslatedOneSidedSeparationMechanism f i A) :
    interior A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hnonempty : (interior A).Nonempty := ⟨x, hx⟩
  rcases hextract (interior A) isOpen_interior hnonempty interior_subset with
    ⟨h⟩
  exact MaxwellTranslatedSlopeSeparationObstruction.false h

/-! ## Smallness package for the three hard cases -/

structure MaxwellThreeHardSlopeCasesSmallness
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  membership : MaxwellThreeHardSlopeCasesMembership S U R i
  samePositiveInfinity : MaxwellSlopeBaseLocusSmallness S
    (maxwellSamePositiveInfinityLocus U R i)
  sameNegativeInfinity : MaxwellSlopeBaseLocusSmallness S
    (maxwellSameNegativeInfinityLocus U R i)
  disagreement : MaxwellSlopeBaseLocusSmallness S
    (maxwellOneSidedSlopeDisagreementLocus U R i)
  unionSmallness : MaxwellSlopeBaseLocusSmallness S
    (maxwellThreeHardSlopeCasesLocus U R i)

/-- Lemma 2.3.11 after exposing its three source mechanisms.  The two chord
hypotheses are the WS5/IVT extraction for equal infinities; the translated
separation hypothesis is the local uniform inequality for unequal one-sided
values. -/
theorem maxwellThreeHardSlopeCasesSmallness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (f : RealEuclidean p → ℝ)
    (hf : ContinuousOn f
      (maxwellSamePositiveInfinityLocus U R i ∪
        maxwellSameNegativeInfinityLocus U R i))
    (hpositiveChord : MaxwellWS5AffineChordCrossingMechanism f i
      .positiveInfinity (maxwellSamePositiveInfinityLocus U R i))
    (hnegativeChord : MaxwellWS5AffineChordCrossingMechanism f i
      .negativeInfinity (maxwellSameNegativeInfinityLocus U R i))
    (hdisagreementTranslate : MaxwellTranslatedOneSidedSeparationMechanism
      f i (maxwellOneSidedSlopeDisagreementLocus U R i)) :
    MaxwellThreeHardSlopeCasesSmallness S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  have hmembership := maxwellThreeHardSlopeCasesMembership
    hC hmem i hU hR
  have hpositiveContinuous : ContinuousOn f
      (maxwellSamePositiveInfinityLocus U R i) :=
    hf.mono (fun _ hx ↦ Or.inl hx)
  have hnegativeContinuous : ContinuousOn f
      (maxwellSameNegativeInfinityLocus U R i) :=
    hf.mono (fun _ hx ↦ Or.inr hx)
  have hpositiveEmpty :
      interior (maxwellSamePositiveInfinityLocus U R i) = ∅ :=
    interior_eq_empty_of_ws5AffineChordCrossing
      hpositiveContinuous hpositiveChord
  have hnegativeEmpty :
      interior (maxwellSameNegativeInfinityLocus U R i) = ∅ :=
    interior_eq_empty_of_ws5AffineChordCrossing
      hnegativeContinuous hnegativeChord
  have hdisagreementEmpty :
      interior (maxwellOneSidedSlopeDisagreementLocus U R i) = ∅ :=
    interior_eq_empty_of_translatedOneSidedSeparation
      hdisagreementTranslate
  have hpositiveSmall := maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
    h21 hp hmembership.samePositiveInfinity_mem hpositiveEmpty
  have hnegativeSmall := maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
    h21 hp hmembership.sameNegativeInfinity_mem hnegativeEmpty
  have hdisagreementSmall :=
    maxwellSlopeBaseLocusSmallness_of_interior_eq_empty h21 hp
      hmembership.disagreement_mem hdisagreementEmpty
  have hunionNull :
      (volume : Measure (RealEuclidean p))
        (maxwellThreeHardSlopeCasesLocus U R i) = 0 := by
    exact measure_union_null
      (measure_union_null hpositiveSmall.locus_volume_eq_zero
        hnegativeSmall.locus_volume_eq_zero)
      hdisagreementSmall.locus_volume_eq_zero
  have hunionSmall := maxwellSlopeBaseLocusSmallness_of_volume_eq_zero
    h21 hp hmembership.union_mem hunionNull
  exact
    { membership := hmembership
      samePositiveInfinity := hpositiveSmall
      sameNegativeInfinity := hnegativeSmall
      disagreement := hdisagreementSmall
      unionSmallness := hunionSmall }

/-- Final set-theoretic reduction of Lemma 2.3.11.  Once the pointwise
one-sided cluster/derivative alternative supplies the preceding data, the
smallness of the three hard cases passes to the nondifferentiability locus. -/
theorem maxwellNondifferentiabilityLocusSmallness_of_clusterData
    {S : EuclideanSetFamily}
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p}
    (hBmem : B ∈ charbonnelClosure S p)
    (hdata : MaxwellNondifferentiableOneSidedClusterData U R i B)
    (hhard : MaxwellThreeHardSlopeCasesSmallness S U R i) :
    MaxwellSlopeBaseLocusSmallness S B := by
  have hBnull : (volume : Measure (RealEuclidean p)) B = 0 :=
    measure_mono_null hdata.subset_threeHardCases
      hhard.unionSmallness.locus_volume_eq_zero
  exact maxwellSlopeBaseLocusSmallness_of_volume_eq_zero
    h21 hp hBmem hBnull

end AbelFormalization
