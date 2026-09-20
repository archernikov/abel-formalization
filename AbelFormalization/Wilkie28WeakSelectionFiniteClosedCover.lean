import AbelFormalization.MaxwellImplicitSelectorSmoothness

/-!
# Finite closed graph covers in Maxwell weak selection

After compact-component localization, it is enough to cover the selected
component by finitely many closed polynomial-sign sets on each of which the
visible projection is injective.  Compactness makes the projections of the
pieces closed.  Since their finite union is the full projected component, one
piece has projected interior and the polynomial-cut graph theorem applies.

This removes the need to identify the large piece in advance.  The remaining
Maxwell input may now produce any finite closed single-valued semialgebraic
cover of each large compact component.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite closed polynomial-sign cover of a compact relation by
single-valued pieces contains one piece whose visible projection has
interior. -/
theorem exists_polynomialSign_injectiveCut_with_projection_interior_of_finite_closed_cover
    {n q : ℕ} {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hPInterior :
      (interior (realEuclideanExistentialProjection P)).Nonempty)
    (D : Fin q → Set (RealEuclidean (1 + n)))
    (hDconstructible : ∀ i, PolynomialSignConstructible (1 + n) (D i))
    (hDclosed : ∀ i, IsClosed (D i))
    (hcover : P ⊆ ⋃ i, D i)
    (hinjective : ∀ i, Set.InjOn realEuclideanTakeLeft (P ∩ D i)) :
    ∃ i : Fin q,
      PolynomialSignConstructible (1 + n) (D i) ∧
      (interior (realEuclideanExistentialProjection (P ∩ D i))).Nonempty ∧
      Set.InjOn realEuclideanTakeLeft (P ∩ D i) := by
  have hcutsUnion : (⋃ i, P ∩ D i) = P := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i ↦ inter_subset_left
    · intro z hzP
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hcover hzP)
      exact Set.mem_iUnion.mpr ⟨i, hzP, hzi⟩
  have hprojectionUnion :
      (⋃ i, realEuclideanExistentialProjection (P ∩ D i)) =
        realEuclideanExistentialProjection P := by
    simp_rw [maxwell_realEuclideanExistentialProjection_eq_takeLeft_image]
    rw [← Set.image_iUnion, hcutsUnion]
  have hprojectionClosed : ∀ i : Fin q,
      IsClosed (realEuclideanExistentialProjection (P ∩ D i)) := by
    intro i
    rw [maxwell_realEuclideanExistentialProjection_eq_takeLeft_image]
    exact ((hPcompact.inter_right (hDclosed i)).image
      (realEuclideanTakeLeftContinuousLinearMap 1 n).continuous).isClosed
  have hprojectionInteriorUnion :
      (interior
        (⋃ i, realEuclideanExistentialProjection (P ∩ D i))).Nonempty := by
    rw [hprojectionUnion]
    exact hPInterior
  obtain ⟨i, hiInterior⟩ :=
    exists_nonempty_interior_iUnion_of_finite_closed
      (fun i : Fin q ↦ realEuclideanExistentialProjection (P ∩ D i))
      hprojectionClosed hprojectionInteriorUnion
  exact ⟨i, hDconstructible i, hiInterior, hinjective i⟩

/-- The same finite-cover argument produces an actual local graph with a
continuous selector.  Continuity is automatic from compactness of the chosen
closed piece and injectivity of its visible projection. -/
theorem exists_local_continuous_graph_of_finite_closed_polynomial_injective_cover
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n q : ℕ} (hn : 0 < n)
    {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hPMem : P ∈ C (1 + n))
    (hPInterior :
      (interior (realEuclideanExistentialProjection P)).Nonempty)
    (D : Fin q → Set (RealEuclidean (1 + n)))
    (hDconstructible : ∀ i, PolynomialSignConstructible (1 + n) (D i))
    (hDclosed : ∀ i, IsClosed (D i))
    (hcover : P ⊆ ⋃ i, D i)
    (hinjective : ∀ i, Set.InjOn realEuclideanTakeLeft (P ∩ D i)) :
    ∃ (U : Set ℝ) (phi : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧ ContinuousOn phi U ∧
      wilkie28SelectedWitnessGraph U phi ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U phi ⊆ P := by
  obtain ⟨i, hiConstructible, hiInterior, hiInjective⟩ :=
    exists_polynomialSign_injectiveCut_with_projection_interior_of_finite_closed_cover
      hPcompact hPInterior D hDconstructible hDclosed hcover hinjective
  let Q : Set (RealEuclidean (1 + n)) := P ∩ D i
  have hQcompact : IsCompact Q := hPcompact.inter_right (hDclosed i)
  have hQmem : Q ∈ C (1 + n) :=
    hC.ws1_inter (by omega) hPMem
      (hC.ws2_polynomialSign (by omega) hiConstructible)
  obtain ⟨U, phi, hUopen, hUnonempty, hgraphMem, hgraphSubset⟩ :=
    exists_local_graph_of_projection_injective
      hC hn hQmem hiInterior hiInjective
  have hphiContinuous : ContinuousOn phi U :=
    continuousOn_of_selectedWitnessGraph_subset_compact_injective
      hQcompact hiInjective hgraphSubset
  exact ⟨U, phi, hUopen, hUnonempty, hphiContinuous,
    hgraphMem, hgraphSubset.trans inter_subset_left⟩

/-- If every piece of the finite closed cover also carries a regular smooth
square implicit system, the selected graph is differentiable everywhere on
its open domain.  This combines the finite Baire choice, compact inverse
continuity, and mathlib's implicit-function theorem. -/
theorem exists_local_differentiable_graph_of_finite_closed_regularImplicit_cover
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n q : ℕ} (hn : 0 < n)
    {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hPMem : P ∈ C (1 + n))
    (hPInterior :
      (interior (realEuclideanExistentialProjection P)).Nonempty)
    (D : Fin q → Set (RealEuclidean (1 + n)))
    (hDconstructible : ∀ i, PolynomialSignConstructible (1 + n) (D i))
    (hDclosed : ∀ i, IsClosed (D i))
    (hcover : P ⊆ ⋃ i, D i)
    (hinjective : ∀ i, Set.InjOn realEuclideanTakeLeft (P ∩ D i))
    (Phi : Fin q → ℝ × RealEuclidean n → RealEuclidean n)
    (hPhiSmooth : ∀ i, ContDiff ℝ 1 (Phi i))
    (hPhiZero : ∀ i z, z ∈ P ∩ D i →
      Phi i (realEuclideanTakeLeft z 0, realEuclideanTakeRight z) = 0)
    (hPhiVertical : ∀ i z, z ∈ P ∩ D i →
      (fderiv ℝ (Phi i)
          (realEuclideanTakeLeft z 0, realEuclideanTakeRight z) ∘L
        ContinuousLinearMap.inr ℝ ℝ (RealEuclidean n)).IsInvertible) :
    ∃ (U : Set ℝ) (phi : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      (∀ t ∈ U, DifferentiableAt ℝ phi t) ∧
      wilkie28SelectedWitnessGraph U phi ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U phi ⊆ P := by
  obtain ⟨i, hiConstructible, hiInterior, hiInjective⟩ :=
    exists_polynomialSign_injectiveCut_with_projection_interior_of_finite_closed_cover
      hPcompact hPInterior D hDconstructible hDclosed hcover hinjective
  let Q : Set (RealEuclidean (1 + n)) := P ∩ D i
  have hQcompact : IsCompact Q := hPcompact.inter_right (hDclosed i)
  have hQmem : Q ∈ C (1 + n) :=
    hC.ws1_inter (by omega) hPMem
      (hC.ws2_polynomialSign (by omega) hiConstructible)
  obtain ⟨U, phi, hUopen, hUnonempty, hgraphMem, hgraphSubset⟩ :=
    exists_local_graph_of_projection_injective
      hC hn hQmem hiInterior hiInjective
  have hPhiGraph : ∀ t ∈ U, Phi i (t, phi t) = 0 := by
    intro t ht
    have hz := hgraphSubset ⟨t, ht, rfl⟩
    simpa only [realEuclideanTakeLeft_append,
      realEuclideanTakeRight_append] using
        hPhiZero i
          (realEuclideanAppend (fun _ : Fin 1 ↦ t) (phi t)) hz
  have hvertical : ∀ t ∈ U,
      (fderiv ℝ (Phi i) (t, phi t) ∘L
        ContinuousLinearMap.inr ℝ ℝ (RealEuclidean n)).IsInvertible := by
    intro t ht
    have hz := hgraphSubset ⟨t, ht, rfl⟩
    simpa only [realEuclideanTakeLeft_append,
      realEuclideanTakeRight_append] using
        hPhiVertical i
          (realEuclideanAppend (fun _ : Fin 1 ↦ t) (phi t)) hz
  have hphiDifferentiable : ∀ t ∈ U, DifferentiableAt ℝ phi t :=
    differentiableOn_selectedWitness_of_compact_injective_of_regularImplicit
      hQcompact hiInjective hUopen hgraphSubset (Phi i)
        (hPhiSmooth i) hPhiGraph hvertical
  exact ⟨U, phi, hUopen, hUnonempty, hphiDifferentiable,
    hgraphMem, hgraphSubset.trans inter_subset_left⟩

/-- A source-shaped sufficient condition for Maxwell graph extraction: every
large compact component admits a finite closed semialgebraic cover whose
pieces are single-valued over the visible coordinate. -/
def Wilkie28LargeComponentFiniteClosedPolynomialGraphCover
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ (m : ℕ)
      (c : ConnectedComponents
        (charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m)),
    (interior (maxwellConnectedComponentProjection c)).Nonempty →
    ∃ (q : ℕ) (D : Fin q → Set (RealEuclidean (1 + n))),
      (∀ i, PolynomialSignConstructible (1 + n) (D i)) ∧
      (∀ i, IsClosed (D i)) ∧
      maxwellConnectedComponentCarrier c ⊆ ⋃ i, D i ∧
      ∀ i, Set.InjOn realEuclideanTakeLeft
        (maxwellConnectedComponentCarrier c ∩ D i)

/-- A finite closed polynomial graph cover automatically supplies the
previous polynomial-cut branch.  Compactness of a connected-component
carrier follows directly from compactness of the truncation; no finiteness
of the component space is needed for this step. -/
theorem wilkie28_largeComponentPolynomialGraphBranch_of_finiteClosedCover
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hcover : Wilkie28LargeComponentFiniteClosedPolynomialGraphCover F f a) :
    Wilkie28LargeComponentPolynomialGraphBranch F f a := by
  intro m c hcInterior
  obtain ⟨q, D, hDconstructible, hDclosed, hcomponentCover, hinjective⟩ :=
    hcover m c hcInterior
  have htruncationCompact : IsCompact
      (charbonnelCompactTruncation
        (wilkie28WeakSelectionIncidence F f a) m) :=
    charbonnelCompactTruncation_isCompact hincidenceClosed m
  have hcomponentCompact :
      IsCompact (maxwellConnectedComponentCarrier c) :=
    maxwell_connectedComponentCarrier_isCompact_of_isCompact
      htruncationCompact c
  obtain ⟨i, hiConstructible, hiInterior, hiInjective⟩ :=
    exists_polynomialSign_injectiveCut_with_projection_interior_of_finite_closed_cover
      hcomponentCompact hcInterior D hDconstructible hDclosed
        hcomponentCover hinjective
  exact ⟨D i, hiConstructible, hiInterior, hiInjective⟩

/-- The finite closed-cover condition therefore discharges compact component
graph extraction in every positive-dimensional hidden space. -/
theorem wilkie28_componentGraphExtraction_of_largeComponentFiniteClosedCover
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hcover : Wilkie28LargeComponentFiniteClosedPolynomialGraphCover F f a) :
    Wilkie28CompactComponentGraphExtraction C F f a :=
  wilkie28_componentGraphExtraction_of_largeComponentPolynomialGraphBranch
    hC hn F f a
      (wilkie28_largeComponentPolynomialGraphBranch_of_finiteClosedCover
        F f a hincidenceClosed hcover)

/-- After the WS5 component localization, a finite closed single-valued
polynomial cover of every large component gives the original compact
incidence graph-extraction property. -/
theorem wilkie28_compactIncidenceGraphExtraction_of_largeComponentFiniteClosedCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hincidenceMem : wilkie28WeakSelectionIncidence F f a ∈
      charbonnelClosure S (1 + n))
    (hcover : Wilkie28LargeComponentFiniteClosedPolynomialGraphCover F f a) :
    Wilkie28CompactIncidenceGraphExtraction
      (charbonnelClosure S) F f a :=
  wilkie28_compactIncidenceGraphExtraction_of_componentGraphExtraction
    hC F f a hincidenceClosed hincidenceMem
      (wilkie28_componentGraphExtraction_of_largeComponentFiniteClosedCover
        hC.toPositiveArityWeakSetStructure hn F f a hincidenceClosed hcover)

/-! ## Simultaneous weak selection and differentiability -/

/-- The compact/Baire extraction interface strengthened with differentiability
of the graph selected from the compact incidence truncation. -/
def Wilkie28CompactIncidenceDifferentiableGraphExtraction
    (C : EuclideanSetFamily) {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ m : ℕ,
    (interior (maxwellClosedLiftProjectionTruncation
      (wilkie28WeakSelectionIncidence F f a) m)).Nonempty →
    maxwellClosedLiftProjectionTruncation
        (wilkie28WeakSelectionIncidence F f a) m ∈ C 1 →
    ∃ (U : Set ℝ) (phi : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      (∀ t ∈ U, DifferentiableAt ℝ phi t) ∧
      wilkie28SelectedWitnessGraph U phi ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U phi ⊆
        charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m

/-- A differentiable compact incidence graph supplies the combined smooth
singular-witness selection used in Wilkie 2.8, without a separate application
of the general almost-everywhere smoothness theorem. -/
theorem wilkie28_smoothSingularWitnessSelection_of_compactIncidenceDifferentiableGraphExtraction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hextract : Wilkie28CompactIncidenceDifferentiableGraphExtraction
      (charbonnelClosure (literalZeroSetFamily G)) F f a) :
    Wilkie28MathlibOnly.SmoothSingularWitnessSelection F f a := by
  intro hinterior
  have hsliceEq := wilkie28FlatExceptionalSlice_eq_exceptionalParameterSet
    hsmooth F f a hF hf
  have hinteriorSlice :
      (interior (wilkie28FlatExceptionalSlice F f a)).Nonempty := by
    rw [hsliceEq]
    exact realEuclideanOne_coordinatePreimage_interior_nonempty hinterior
  obtain ⟨m, _hcompact, hprojMem, hprojInterior, _hprojSubset⟩ :=
    wilkie28_exists_compact_incidence_projection_with_interior
      hG hsmooth hderiv F f a hF hf hinteriorSlice
  obtain ⟨U, phi, hUopen, hUnonempty, hphiDiff,
      hgraphMem, hgraphTrunc⟩ :=
    hextract m hprojInterior hprojMem
  have hgraphIncidence : wilkie28SelectedWitnessGraph U phi ⊆
      wilkie28WeakSelectionIncidence F f a :=
    hgraphTrunc.trans
      (charbonnelCompactTruncation_subset
        (wilkie28WeakSelectionIncidence F f a) m)
  let s : Wilkie28WeakSelectedWitness
      (charbonnelClosure (literalZeroSetFamily G)) F f a :=
    wilkie28WeakSelectedWitness_of_graph_subset_incidence
      hsmooth F f a hF hf
      (charbonnelClosure (literalZeroSetFamily G)) U phi
      hUopen hUnonempty hgraphMem hgraphIncidence
  exact ⟨U, phi, hUopen, hUnonempty,
    s.F_eq, s.f_eq, s.singular, hphiDiff⟩

/-- A source-shaped strengthening of the finite closed graph cover: every
piece additionally carries a smooth square implicit system, vanishing on the
piece, whose hidden derivative is invertible there. -/
def Wilkie28LargeComponentFiniteClosedRegularImplicitCover
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ (m : ℕ)
      (c : ConnectedComponents
        (charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m)),
    (interior (maxwellConnectedComponentProjection c)).Nonempty →
    ∃ (q : ℕ) (D : Fin q → Set (RealEuclidean (1 + n)))
        (Phi : Fin q → ℝ × RealEuclidean n → RealEuclidean n),
      (∀ i, PolynomialSignConstructible (1 + n) (D i)) ∧
      (∀ i, IsClosed (D i)) ∧
      maxwellConnectedComponentCarrier c ⊆ ⋃ i, D i ∧
      (∀ i, Set.InjOn realEuclideanTakeLeft
        (maxwellConnectedComponentCarrier c ∩ D i)) ∧
      (∀ i, ContDiff ℝ 1 (Phi i)) ∧
      (∀ i z, z ∈ maxwellConnectedComponentCarrier c ∩ D i →
        Phi i (realEuclideanTakeLeft z 0,
          realEuclideanTakeRight z) = 0) ∧
      ∀ i z, z ∈ maxwellConnectedComponentCarrier c ∩ D i →
        (fderiv ℝ (Phi i)
            (realEuclideanTakeLeft z 0, realEuclideanTakeRight z) ∘L
          ContinuousLinearMap.inr ℝ ℝ (RealEuclidean n)).IsInvertible

/-- WS5 component localization followed by a finite closed regular implicit
cover gives a differentiable compact incidence graph. -/
theorem wilkie28_compactIncidenceDifferentiableGraphExtraction_of_largeComponentFiniteClosedRegularImplicitCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hincidenceMem : wilkie28WeakSelectionIncidence F f a ∈
      charbonnelClosure S (1 + n))
    (hcover : Wilkie28LargeComponentFiniteClosedRegularImplicitCover F f a) :
    Wilkie28CompactIncidenceDifferentiableGraphExtraction
      (charbonnelClosure S) F f a := by
  intro m hprojectionInterior _hprojectionMem
  let K := charbonnelCompactTruncation
    (wilkie28WeakSelectionIncidence F f a) m
  have hKcompact : IsCompact K :=
    charbonnelCompactTruncation_isCompact hincidenceClosed m
  have hKmem : K ∈ charbonnelClosure S (1 + n) := by
    exact hC.ws1_inter (by omega) hincidenceMem
      (hC.ws2_polynomialSign (by omega)
        (polynomialSignConstructible_closedBall_zero (1 + n) m))
  obtain ⟨c, hcCompact, hcMem, _hcProjectionMem, hcInterior⟩ :=
    exists_compact_component_with_projection_interior
      hC hKcompact hKmem hprojectionInterior
  obtain ⟨q, D, Phi, hDconstructible, hDclosed, hcomponentCover,
      hinjective, hPhiSmooth, hPhiZero, hPhiVertical⟩ :=
    hcover m c hcInterior
  obtain ⟨U, phi, hUopen, hUnonempty, hphiDiff,
      hgraphMem, hgraphComponent⟩ :=
    exists_local_differentiable_graph_of_finite_closed_regularImplicit_cover
      hC.toPositiveArityWeakSetStructure hn hcCompact hcMem hcInterior
        D hDconstructible hDclosed hcomponentCover hinjective
        Phi hPhiSmooth hPhiZero hPhiVertical
  exact ⟨U, phi, hUopen, hUnonempty, hphiDiff, hgraphMem,
    hgraphComponent.trans (maxwell_connectedComponentCarrier_subset c)⟩

end AbelFormalization
