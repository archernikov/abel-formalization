import AbelFormalization.CharbonnelLinearEquivClosure
import AbelFormalization.CharbonnelAffineSectionRankInduction
import AbelFormalization.CharbonnelClosureNullityWitnesses
import AbelFormalization.CharbonnelSardianApproximationCertificate

/-!
# The literal-zero Charbonnel complement pipeline

This file assembles the proved structural parts of the Charbonnel--Wilkie
route over

`charbonnelClosure (literalZeroSetFamily G)`.

There are two set families in the source argument, with different jobs.  The
all-orders DC hypothesis belongs to the projected-zero base family.  It is
already supplied here by `projectedZeroPositiveArityComplementInput`.  The
literal-zero Charbonnel closure is the auxiliary family on which the
description-rank, approximation, boundary, and complement inductions run; it
does not need a separately assumed closure-level DC statement.

For a globally smooth geometric family with uniform fiber finiteness, the
linear-equivalence theorem supplies WS1--WS4 for the Charbonnel closure, the
numeric rank induction supplies WS5, and the closed-description-base induction
supplies WS6.  The proved section 5 results reduce approximation-trace tameness
to the explicit higher-dimensional analytic step and a closure-regularity
input.  The finite locally closed decomposition used below is a sufficient
strengthening of that regularity input; it is not claimed to be the literal
hypothesis proved in the source.

The two final unproved steps are represented by propositions, not asserted as
theorems: construction of Sardian approximation certificates at every positive
order by description rank, and Wilkie's cell-decomposition passage from closed
boundary carriers to complements.  Once the latter gives positive-arity
complement closure, this file constructs the actual
`ProjectedZeroComplementEnvelope`, including its arity-zero entry, without
assuming `ProjectedZeroComplementPrinciple`.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## WS1--WS6 and the correctly located DC input -/

/-- A globally smooth geometric family with UFF makes its literal-zero
Charbonnel closure a positive-arity o-minimal weak set structure. -/
theorem literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) := by
  refine
    { toPositiveArityWeakSetStructure :=
        literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
          hG hsmooth
      ws5_affineSections := ?_
      ws6_closedLift := ?_ }
  · exact literalZeroSet_charbonnelClosure_ws5_affineSections
      hG hsmooth hUFF
  · intro n _hn A hA
    exact literalZeroSet_charbonnelClosure_semiClosed hG hsmooth hA

/-! ## Approximation-trace input -/

/-- The proved WS1--WS6 package discharges the one-dimensional section 5
base case.  Together with the two remaining geometric section 5 inputs, this
gives the complete trace-tameness interface used by Wilkie's descent.

`hdecomp` is the currently formalized sufficient strengthening of the
source-shaped empty-interior/closure regularity step. -/
theorem literalZeroSet_charbonnelClosure_approximationTraceTameness_of_section5Inputs
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) n) :
    CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)) :=
  literalZeroSet_charbonnelClosure_traceTameness hG hsmooth
    (literalZeroSet_charbonnelClosure_approximationTraceSmallness_of_section5Inputs
      hG hsmooth
      (literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
        hG hsmooth hUFF)
      hanalytic hdecomp)

/-- The strongest already-proved source input package.  DC is attached to the
projected-zero base family, while WS1--WS6 and approximation traces are
attached to the literal-zero Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_complementPipelineInputs
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) n) :
    PositiveArityComplementTheoremInput (projectedZeroSetFamily G) ∧
      PositiveArityOMinimalWeakSetStructure
        (charbonnelClosure (literalZeroSetFamily G)) ∧
      CharbonnelApproximationTraceTameness
        (charbonnelClosure (literalZeroSetFamily G)) :=
  ⟨projectedZeroPositiveArityComplementInput hG hsmooth hUFF,
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF,
    literalZeroSet_charbonnelClosure_approximationTraceTameness_of_section5Inputs
      hG hsmooth hUFF hanalytic hdecomp⟩

/-! ## Sardian approximation certificates by numeric description rank -/

namespace CharbonnelDescription

/-- The output required from Wilkie's approximation construction for one
description: at every positive differentiability order there is a finite,
common-depth Sardian approximation certificate satisfying condition 3.6. -/
def HasSardianApproximations
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) : Prop :=
  ∀ order : ℕ, 0 < order →
    Nonempty (CharbonnelSardianApproximationCertificate
      G order n description.carrier)

end CharbonnelDescription

/-- The exact strong-induction step still needed to construct Sardian
approximation certificates for arbitrary descriptions.  Its lower-rank
hypothesis ranges over all arities because replacement descriptions arising in
the proof need not be structural subterms of the current description.

This proposition records the missing step; no inhabitant is asserted here. -/
def CharbonnelSardianApproximationRankStep
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ r : ℕ,
    (∀ {m : ℕ}
      (lower : CharbonnelDescription (literalZeroSetFamily G) m),
        lower.rank < r → lower.HasSardianApproximations G) →
    ∀ {n : ℕ}
      (description : CharbonnelDescription (literalZeroSetFamily G) n),
        description.rank = r → description.HasSardianApproximations G

/-- A proof of the rank step yields Sardian approximation certificates for
every literal-zero Charbonnel description.  This is only the well-founded
induction skeleton; all analytic and constructor-specific content remains in
the explicit `hstep` premise. -/
theorem CharbonnelDescription.hasSardianApproximations_of_rankStep
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hstep : CharbonnelSardianApproximationRankStep G)
    {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) :
    description.HasSardianApproximations G := by
  have inductionStatement :
      ∀ r : ℕ, ∀ {m : ℕ}
        (d : CharbonnelDescription (literalZeroSetFamily G) m),
        d.rank = r → d.HasSardianApproximations G := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro m d hrank
        apply hstep r
        · intro k lower hlowerRank
          exact ih lower.rank hlowerRank lower rfl
        · exact hrank
  exact inductionStatement description.rank description rfl

/-! ## Boundary carriers supplied by the missing approximation rank step -/

/-- Once the two section 5 inputs are supplied, every already constructed
Sardian approximation certificate yields the closed, empty-interior boundary
carrier used by the complement induction. -/
theorem CharbonnelSardianApproximationCertificate.exists_closed_emptyInterior_boundaryCarrier_of_section5Inputs
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {d : ℕ}, 0 < d →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) d)
    {order n : ℕ} {A : Set (RealEuclidean n)}
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧
        B ∈ charbonnelClosure (literalZeroSetFamily G) n ∧
        interior B = ∅ ∧ frontier (closure A) ⊆ B :=
  certificate.exists_closed_emptyInterior_boundaryCarrier hG
    (literalZeroSet_charbonnelClosure_approximationTraceTameness_of_section5Inputs
      hG hsmooth hUFF hanalytic hdecomp)

/-- The approximation rank step and trace tameness give the boundary carrier
for one arbitrary description.  Order one is enough at this endpoint because
the Sardian empty-interior theorem only needs one derivative. -/
theorem CharbonnelDescription.exists_closed_emptyInterior_boundaryCarrier_of_rankStep
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (htrace : CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)))
    (hstep : CharbonnelSardianApproximationRankStep G)
    {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧
        B ∈ charbonnelClosure (literalZeroSetFamily G) n ∧
        interior B = ∅ ∧
          frontier (closure description.carrier) ⊆ B := by
  obtain ⟨certificate⟩ :=
    (description.hasSardianApproximations_of_rankStep hstep) 1 (by omega)
  exact certificate.exists_closed_emptyInterior_boundaryCarrier hG htrace

/-- Family-level boundary conclusion conditional on the missing Sardian
approximation rank step and the two explicit section 5 inputs. -/
theorem literalZeroSet_charbonnelClosure_exists_closed_emptyInterior_boundaryCarrier
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {d : ℕ}, 0 < d →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) d)
    (hstep : CharbonnelSardianApproximationRankStep G)
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure (literalZeroSetFamily G) n) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧
        B ∈ charbonnelClosure (literalZeroSetFamily G) n ∧
        interior B = ∅ ∧ frontier (closure A) ⊆ B := by
  obtain ⟨description, hdescription⟩ := hA
  rw [← hdescription]
  exact description.exists_closed_emptyInterior_boundaryCarrier_of_rankStep
    hG
    (literalZeroSet_charbonnelClosure_approximationTraceTameness_of_section5Inputs
      hG hsmooth hUFF hanalytic hdecomp)
    hstep

/-! ## The remaining cell-decomposition complement assembly -/

/-- The boundary conclusion used by Wilkie's final cell-decomposition
argument, stated only for closed positive-arity members as in the source. -/
def CharbonnelClosedBoundaryCarrierProperty
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {A : Set (RealEuclidean n)},
    IsClosed A →
    A ∈ charbonnelClosure (literalZeroSetFamily G) n →
      ∃ B : Set (RealEuclidean n),
        IsClosed B ∧
          B ∈ charbonnelClosure (literalZeroSetFamily G) n ∧
          interior B = ∅ ∧ frontier A ⊆ B

/-- Sardian certificate construction and trace tameness establish the exact
closed-boundary-carrier property consumed by the final cell argument. -/
theorem literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (htrace : CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)))
    (hsardian : CharbonnelSardianApproximationRankStep G) :
    CharbonnelClosedBoundaryCarrierProperty G := by
  intro n _hn A hAclosed hA
  obtain ⟨description, hdescription⟩ := hA
  have hboundary :=
    description.exists_closed_emptyInterior_boundaryCarrier_of_rankStep
      hG htrace hsardian
  simpa only [hdescription, hAclosed.closure_eq] using hboundary

/-- The source's final cell-decomposition assembly: closed boundary carriers
in every positive arity imply complement closure of the Charbonnel family.
Wilkie proves this by simultaneous induction on ambient dimension for cells
and compatible cell decompositions.  That induction is not yet formalized, so
this proposition is kept as an explicit premise. -/
def CharbonnelClosedBoundaryComplementAssembly
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  CharbonnelClosedBoundaryCarrierProperty G →
    ∀ {n : ℕ}, 0 < n → ∀ {A : Set (RealEuclidean n)},
      A ∈ charbonnelClosure (literalZeroSetFamily G) n →
        Aᶜ ∈ charbonnelClosure (literalZeroSetFamily G) n

/-! ## Constructing the ambient complement envelope -/

/-- Complete a family used only in positive arities by admitting every set in
arity zero.  Since `RealEuclidean 0` is a singleton, this harmless completion
is enough to state the all-arity first-order envelope while preserving the
source's positive-arity Charbonnel construction verbatim. -/
def positiveArityEuclideanSetFamilyCompletion
    (C : EuclideanSetFamily) : EuclideanSetFamily :=
  fun n => if 0 < n then C n else Set.univ

@[simp]
theorem positiveArityEuclideanSetFamilyCompletion_of_pos
    (C : EuclideanSetFamily) {n : ℕ} (hn : 0 < n) :
    positiveArityEuclideanSetFamilyCompletion C n = C n := by
  simp [positiveArityEuclideanSetFamilyCompletion, hn]

@[simp]
theorem positiveArityEuclideanSetFamilyCompletion_zero
    (C : EuclideanSetFamily) :
    positiveArityEuclideanSetFamilyCompletion C 0 = Set.univ := by
  simp [positiveArityEuclideanSetFamilyCompletion]

/-- Positive-arity complement closure of the literal-zero Charbonnel family
constructs the ambient complement envelope required by the first-order
endpoint.  The arity-zero entry is supplied by
`positiveArityEuclideanSetFamilyCompletion`; every positive-arity field is an
already-proved Charbonnel operation, apart from the explicit `hcompl` premise.
-/
noncomputable def projectedZeroComplementEnvelope_of_literalZeroSet_charbonnelClosure_compl
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hcompl : ∀ {n : ℕ}, 0 < n →
      ∀ {A : Set (RealEuclidean n)},
        A ∈ charbonnelClosure (literalZeroSetFamily G) n →
          Aᶜ ∈ charbonnelClosure (literalZeroSetFamily G) n) :
    ProjectedZeroComplementEnvelope G := by
  have hC :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  refine
    { sets := positiveArityEuclideanSetFamilyCompletion
        (charbonnelClosure (literalZeroSetFamily G))
      projectedZero_mem := ?_
      empty_mem := ?_
      union_mem := ?_
      compl_mem := ?_
      linearEquiv_image_mem := ?_
      existentialProjection_mem := ?_
      unary_component_bound := ?_ }
  · intro n A hA
    by_cases hn : 0 < n
    · simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hn]
      exact hA.mem_literalZeroSet_charbonnelClosure hn
    · simp [positiveArityEuclideanSetFamilyCompletion, hn]
  · intro n
    by_cases hn : 0 < n
    · simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hn]
      exact hC.ws2_polynomialSign hn
        (polynomialSignConstructible_empty n)
    · simp [positiveArityEuclideanSetFamilyCompletion, hn]
  · intro n A B hA hB
    by_cases hn : 0 < n
    · simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hn] at hA hB ⊢
      exact charbonnelClosure_union hA hB
    · simp [positiveArityEuclideanSetFamilyCompletion, hn]
  · intro n A hA
    by_cases hn : 0 < n
    · simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hn] at hA ⊢
      exact hcompl hn hA
    · simp [positiveArityEuclideanSetFamilyCompletion, hn]
  · intro n A hA e
    by_cases hn : 0 < n
    · simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hn] at hA ⊢
      exact literalZeroSet_charbonnelClosure_linearEquiv_image
        hG hsmooth hA e
    · simp [positiveArityEuclideanSetFamilyCompletion, hn]
  · intro n m A hA
    by_cases hn : 0 < n
    · have hnm : 0 < n + m := by omega
      simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hnm] at hA
      simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hn]
      exact charbonnelClosure_projection hn hA
    · simp [positiveArityEuclideanSetFamilyCompletion, hn]
  · intro A hA
    have hone : 0 < (1 : ℕ) := by omega
    simp only [positiveArityEuclideanSetFamilyCompletion_of_pos _ hone] at hA
    obtain ⟨N, hN⟩ := hC.ws5_affineSections (n := 1) hone hA
    refine ⟨N, ?_⟩
    have htop := hN (⊤ : AffineSubspace ℝ (RealEuclidean 1))
    rw [AffineSubspace.top_coe, inter_univ] at htop
    exact htop

/-- The strongest source-shaped endpoint staged here.  The analytic and
closure-regularity inputs produce trace tameness, the unproved Sardian rank
step produces closed boundary carriers, and the explicit cell-decomposition
assembly produces positive-arity complement closure.  The preceding
constructor then returns the concrete ambient envelope.  No closure-level DC
or external `ProjectedZeroComplementPrinciple` premise appears. -/
noncomputable def projectedZeroComplementEnvelope_of_charbonnelApproximation_and_cellAssembly
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {d : ℕ}, 0 < d →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) d)
    (hsardian : CharbonnelSardianApproximationRankStep G)
    (hcell : CharbonnelClosedBoundaryComplementAssembly G) :
    ProjectedZeroComplementEnvelope G := by
  have htrace :=
    literalZeroSet_charbonnelClosure_approximationTraceTameness_of_section5Inputs
      hG hsmooth hUFF hanalytic hdecomp
  apply
    projectedZeroComplementEnvelope_of_literalZeroSet_charbonnelClosure_compl
      hG hsmooth hUFF
  exact hcell
    (literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty
      hG htrace hsardian)

end AbelFormalization
