import AbelFormalization.MaxwellCompactComponentMembership
import AbelFormalization.Wilkie28WeakSelectionCompactExtraction

/-!
# Reducing weak selection to one compact connected component

The compact/Baire reduction produces a compact incidence relation whose
visible projection has interior.  WS5 makes its connected-component type
finite.  Compact components are closed, their visible projections are closed,
and Baire therefore puts nonempty interior in the projection of one component.
The component itself remains in the weak family by
`MaxwellCompactComponentMembership`.

Thus the unresolved graph-extraction step may be restricted to compact
connected family members with large visible projection.  The injective
projection branch, the constant hidden-section branch, and the more flexible
polynomial-sign injective-cut branch are discharged explicitly below.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite union of closed empty-interior sets has empty interior. -/
theorem interior_iUnion_fin_eq_empty_of_closed
    {X : Type*} [TopologicalSpace X]
    {k : ℕ} (F : Fin k → Set X)
    (hclosed : ∀ i, IsClosed (F i))
    (hempty : ∀ i, interior (F i) = ∅) :
    interior (⋃ i, F i) = ∅ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
      rw [interior_union_isClosed_of_interior_empty (hclosed 0)]
      · exact hempty 0
      · simpa [Function.comp_def] using
          ih (fun j ↦ F j.succ) (fun j ↦ hclosed j.succ)
            (fun j ↦ hempty j.succ)

/-- If a finite union of closed sets has interior, one member has interior. -/
theorem exists_nonempty_interior_iUnion_of_finite_closed
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hinterior : (interior (⋃ i, F i)).Nonempty) :
    ∃ i, (interior (F i)).Nonempty := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  by_contra hnone
  have hempty : ∀ i, interior (F i) = ∅ := by
    intro i
    apply not_nonempty_iff_eq_empty.mp
    intro hi
    exact hnone ⟨i, hi⟩
  have hfin : interior (⋃ j : Fin (Fintype.card ι), F (e.symm j)) = ∅ :=
    interior_iUnion_fin_eq_empty_of_closed
      (fun j ↦ F (e.symm j))
      (fun j ↦ hclosed (e.symm j))
      (fun j ↦ hempty (e.symm j))
  have hunion : (⋃ j : Fin (Fintype.card ι), F (e.symm j)) =
      ⋃ i : ι, F i := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e.symm j, hj⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa using hi⟩
  rw [hunion] at hfin
  rw [hfin] at hinterior
  exact hinterior.ne_empty rfl

/-- The visible projection of one connected component of a relation in
`RealEuclidean (1 + n)`. -/
def maxwellConnectedComponentProjection
    {n : ℕ} {K : Set (RealEuclidean (1 + n))}
    (c : ConnectedComponents K) : Set (RealEuclidean 1) :=
  realEuclideanExistentialProjection
    (maxwellConnectedComponentCarrier c)

/-- Existential projection is the image of the visible-coordinate map. -/
theorem maxwell_realEuclideanExistentialProjection_eq_takeLeft_image
    {p q : ℕ} (A : Set (RealEuclidean (p + q))) :
    realEuclideanExistentialProjection A = realEuclideanTakeLeft '' A := by
  ext x
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨realEuclideanAppend x y, hxy,
      realEuclideanTakeLeft_append x y⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨realEuclideanTakeRight v, ?_⟩
    simpa only [realEuclideanAppend_take] using hv

/-- The visible projections of all connected components cover exactly the
visible projection of the original relation. -/
theorem iUnion_maxwellConnectedComponentProjection
    {n : ℕ} (K : Set (RealEuclidean (1 + n))) :
    ⋃ c : ConnectedComponents K,
        maxwellConnectedComponentProjection c =
      realEuclideanExistentialProjection K := by
  ext x
  simp only [maxwellConnectedComponentProjection,
    realEuclideanExistentialProjection, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨c, y, hy⟩
    exact ⟨y, maxwell_connectedComponentCarrier_subset c hy⟩
  · rintro ⟨y, hy⟩
    let z : K := ⟨realEuclideanAppend x y, hy⟩
    let c : ConnectedComponents K := ConnectedComponents.mk z
    refine ⟨c, y, ?_⟩
    exact ⟨z, rfl, rfl⟩

/-- One connected component of a compact relation with large visible
projection still has a large visible projection and remains a member of the
Charbonnel closure. -/
theorem exists_compact_component_with_projection_interior
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n : ℕ} {K : Set (RealEuclidean (1 + n))}
    (hKcompact : IsCompact K)
    (hKmem : K ∈ charbonnelClosure S (1 + n))
    (hprojectionInterior :
      (interior (realEuclideanExistentialProjection K)).Nonempty) :
    ∃ c : ConnectedComponents K,
      IsCompact (maxwellConnectedComponentCarrier c) ∧
      maxwellConnectedComponentCarrier c ∈
        charbonnelClosure S (1 + n) ∧
      maxwellConnectedComponentProjection c ∈
        charbonnelClosure S 1 ∧
      (interior (maxwellConnectedComponentProjection c)).Nonempty := by
  obtain ⟨N, hN⟩ := hC.ws5_affineSections (n := 1 + n) (by omega) hKmem
  have hcard := hN (⊤ : AffineSubspace ℝ (RealEuclidean (1 + n)))
  rw [AffineSubspace.top_coe, inter_univ] at hcard
  let hfinite : Finite (ConnectedComponents K) := by
    rw [← ENat.card_lt_top]
    exact hcard.trans_lt (WithTop.coe_lt_top N)
  letI : Finite (ConnectedComponents K) := hfinite
  have hcomponentCompact : ∀ c : ConnectedComponents K,
      IsCompact (maxwellConnectedComponentCarrier c) := by
    intro c
    exact (maxwell_componentCarriers_isCompact hKcompact hfinite c).1
  have hprojectionClosed : ∀ c : ConnectedComponents K,
      IsClosed (maxwellConnectedComponentProjection c) := by
    intro c
    rw [maxwellConnectedComponentProjection,
      maxwell_realEuclideanExistentialProjection_eq_takeLeft_image]
    change IsClosed
      ((realEuclideanTakeLeftContinuousLinearMap 1 n) ''
        maxwellConnectedComponentCarrier c)
    exact ((hcomponentCompact c).image
      (realEuclideanTakeLeftContinuousLinearMap 1 n).continuous).isClosed
  have hinteriorUnion :
      (interior (⋃ c : ConnectedComponents K,
        maxwellConnectedComponentProjection c)).Nonempty := by
    rw [iUnion_maxwellConnectedComponentProjection K]
    exact hprojectionInterior
  obtain ⟨c, hcInterior⟩ :=
    exists_nonempty_interior_iUnion_of_finite_closed
      (fun c : ConnectedComponents K ↦
        maxwellConnectedComponentProjection c)
      hprojectionClosed hinteriorUnion
  have hcMem : maxwellConnectedComponentCarrier c ∈
      charbonnelClosure S (1 + n) :=
    hC.compact_connectedComponentCarrier_mem
      (by omega) hKcompact hKmem c
  exact ⟨c, hcomponentCompact c, hcMem,
    charbonnelClosure_projection (by omega) hcMem, hcInterior⟩

/-- The remaining connected-component version of compact graph extraction.
It asks for a graph only after WS5 has localized the compact incidence to one
connected family member whose visible projection has interior. -/
def Wilkie28CompactComponentGraphExtraction
    (C : EuclideanSetFamily) {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ (m : ℕ)
      (c : ConnectedComponents
        (charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m)),
    (interior (maxwellConnectedComponentProjection c)).Nonempty →
    maxwellConnectedComponentCarrier c ∈ C (1 + n) →
    ∃ (U : Set ℝ) (φ : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      wilkie28SelectedWitnessGraph U φ ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U φ ⊆
        maxwellConnectedComponentCarrier c

/-- For an o-minimal Charbonnel weak structure, connected-component graph
extraction implies the earlier compact-incidence graph-extraction interface. -/
theorem wilkie28_compactIncidenceGraphExtraction_of_componentGraphExtraction
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hincidenceMem : wilkie28WeakSelectionIncidence F f a ∈
      charbonnelClosure S (1 + n))
    (hextract : Wilkie28CompactComponentGraphExtraction
      (charbonnelClosure S) F f a) :
    Wilkie28CompactIncidenceGraphExtraction
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
  obtain ⟨c, _hcCompact, hcMem, _hcProjectionMem, hcInterior⟩ :=
    exists_compact_component_with_projection_interior
      hC hKcompact hKmem hprojectionInterior
  obtain ⟨U, φ, hUopen, hUnonempty, hgraphMem, hgraphComponent⟩ :=
    hextract m c hcInterior hcMem
  exact ⟨U, φ, hUopen, hUnonempty, hgraphMem,
    hgraphComponent.trans
      (maxwell_connectedComponentCarrier_subset c)⟩

/-! ## The single-valued component branch -/

/-- Choose the hidden coordinate over a visible real parameter whenever the
fiber is nonempty. -/
def maxwellOneParameterSelector
    {n : ℕ} (P : Set (RealEuclidean (1 + n)))
    (t : ℝ) : RealEuclidean n := by
  classical
  exact
    if h : (fun _ : Fin 1 ↦ t) ∈ realEuclideanExistentialProjection P then
      Classical.choose h
    else 0

theorem maxwell_append_oneParameterSelector_mem
    {n : ℕ} {P : Set (RealEuclidean (1 + n))} {t : ℝ}
    (ht : (fun _ : Fin 1 ↦ t) ∈
      realEuclideanExistentialProjection P) :
    realEuclideanAppend (fun _ : Fin 1 ↦ t)
      (maxwellOneParameterSelector P t) ∈ P := by
  simp only [maxwellOneParameterSelector, dif_pos ht]
  exact Classical.choose_spec ht

/-- Any family member with injective visible projection and projected
interior supplies a weak-family graph on a nonempty open interval.  The graph
is cut out by a semialgebraic visible cylinder. -/
theorem exists_local_graph_of_projection_injective
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {P : Set (RealEuclidean (1 + n))}
    (hPMem : P ∈ C (1 + n))
    (hPInterior :
      (interior (realEuclideanExistentialProjection P)).Nonempty)
    (hinjective : Set.InjOn realEuclideanTakeLeft P) :
    ∃ (U : Set ℝ) (φ : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      wilkie28SelectedWitnessGraph U φ ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U φ ⊆ P := by
  classical
  let Q : Set (RealEuclidean 1) :=
    realEuclideanExistentialProjection P
  obtain ⟨x0, hx0⟩ := hPInterior
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior x0 hx0
  let V : Set (RealEuclidean 1) := Metric.ball x0 ε
  let U : Set ℝ := {t | (fun _ : Fin 1 ↦ t) ∈ V}
  let φ : ℝ → RealEuclidean n := maxwellOneParameterSelector P
  have hUopen : IsOpen U := by
    exact Metric.isOpen_ball.preimage (continuous_pi fun _ ↦ continuous_id)
  have hUnonempty : U.Nonempty := by
    refine ⟨x0 0, ?_⟩
    change (fun _ : Fin 1 ↦ x0 0) ∈ Metric.ball x0 ε
    have heq : (fun _ : Fin 1 ↦ x0 0) = x0 := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    rw [heq]
    exact Metric.mem_ball_self hε
  have hVsubsetQ : V ⊆ Q := by
    exact hball.trans interior_subset
  have hselector (t : ℝ) (ht : t ∈ U) :
      realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t) ∈ P := by
    apply maxwell_append_oneParameterSelector_mem
    exact hVsubsetQ ht
  have hgraphEq : wilkie28SelectedWitnessGraph U φ =
      P ∩ realEuclideanSetProduct V Set.univ := by
    ext z
    constructor
    · rintro ⟨t, htU, rfl⟩
      have htV : (fun _ : Fin 1 ↦ t) ∈ V := by
        change (fun _ : Fin 1 ↦ t) ∈ V at htU
        exact htU
      exact ⟨hselector t htU, by
        exact ⟨by simpa only [realEuclideanTakeLeft_append] using htV,
          Set.mem_univ _⟩⟩
    · rintro ⟨hzP, hzV, _hzright⟩
      let t : ℝ := realEuclideanTakeLeft z 0
      have hvis : (fun _ : Fin 1 ↦ t) = realEuclideanTakeLeft z := by
        funext i
        exact Fin.eq_zero i ▸ rfl
      have htU : t ∈ U := by
        change (fun _ : Fin 1 ↦ t) ∈ V
        rwa [hvis]
      have hselectedP :
          realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t) ∈ P :=
        hselector t htU
      have hsameVisible : realEuclideanTakeLeft
          (realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t)) =
          realEuclideanTakeLeft z := by
        simpa only [realEuclideanTakeLeft_append] using hvis
      have heq :
          realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t) = z :=
        hinjective hselectedP hzP hsameVisible
      exact ⟨t, htU, heq.symm⟩
  have hVmem : V ∈ C 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_ball x0 hε)
  have hunivMem : (Set.univ : Set (RealEuclidean n)) ∈ C n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
  have hcylinderMem : realEuclideanSetProduct V Set.univ ∈ C (1 + n) :=
    hC.ws3_prod (by omega) hn hVmem hunivMem
  refine ⟨U, φ, hUopen, hUnonempty, ?_, ?_⟩
  · rw [hgraphEq]
    exact hC.ws1_inter (by omega) hPMem hcylinderMem
  · rw [hgraphEq]
    exact inter_subset_left

/-- If the visible projection is injective on one component, that component
supplies the preceding general graph construction. -/
theorem exists_local_graph_of_componentProjection_injective
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {K : Set (RealEuclidean (1 + n))}
    (c : ConnectedComponents K)
    (hcMem : maxwellConnectedComponentCarrier c ∈ C (1 + n))
    (hcInterior :
      (interior (maxwellConnectedComponentProjection c)).Nonempty)
    (hinjective : Set.InjOn realEuclideanTakeLeft
      (maxwellConnectedComponentCarrier c)) :
    ∃ (U : Set ℝ) (φ : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      wilkie28SelectedWitnessGraph U φ ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U φ ⊆
        maxwellConnectedComponentCarrier c := by
  exact exists_local_graph_of_projection_injective
    hC hn hcMem hcInterior hinjective

/-- A polynomial-sign cut that makes the visible projection single-valued
produces a local graph contained in the original family member. -/
theorem exists_local_graph_of_polynomialSign_injectiveCut
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {P D : Set (RealEuclidean (1 + n))}
    (hPMem : P ∈ C (1 + n))
    (hD : PolynomialSignConstructible (1 + n) D)
    (hcutInterior :
      (interior (realEuclideanExistentialProjection (P ∩ D))).Nonempty)
    (hinjective : Set.InjOn realEuclideanTakeLeft (P ∩ D)) :
    ∃ (U : Set ℝ) (φ : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      wilkie28SelectedWitnessGraph U φ ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U φ ⊆ P := by
  have hcutMem : P ∩ D ∈ C (1 + n) :=
    hC.ws1_inter (by omega) hPMem
      (hC.ws2_polynomialSign (by omega) hD)
  obtain ⟨U, φ, hUopen, hUnonempty, hgraphMem, hgraphCut⟩ :=
    exists_local_graph_of_projection_injective
      hC hn hcutMem hcutInterior hinjective
  exact ⟨U, φ, hUopen, hUnonempty, hgraphMem,
    hgraphCut.trans inter_subset_left⟩

/-- The visible section of a relation at one fixed hidden witness. -/
def maxwellFixedHiddenSection
    {n : ℕ} (P : Set (RealEuclidean (1 + n)))
    (y : RealEuclidean n) : Set (RealEuclidean 1) :=
  {x | realEuclideanAppend x y ∈ P}

/-- If one fixed hidden witness works over a visible set with interior, then
it gives a constant local graph in the weak family. -/
theorem exists_local_graph_of_fixedHiddenSection_interior
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {K : Set (RealEuclidean (1 + n))}
    (c : ConnectedComponents K)
    (hcMem : maxwellConnectedComponentCarrier c ∈ C (1 + n))
    (y : RealEuclidean n)
    (hsectionInterior :
      (interior (maxwellFixedHiddenSection
        (maxwellConnectedComponentCarrier c) y)).Nonempty) :
    ∃ (U : Set ℝ) (φ : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      wilkie28SelectedWitnessGraph U φ ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U φ ⊆
        maxwellConnectedComponentCarrier c := by
  classical
  let P : Set (RealEuclidean (1 + n)) :=
    maxwellConnectedComponentCarrier c
  let Q : Set (RealEuclidean 1) := maxwellFixedHiddenSection P y
  obtain ⟨x0, hx0⟩ := hsectionInterior
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior x0 hx0
  let V : Set (RealEuclidean 1) := Metric.ball x0 ε
  let U : Set ℝ := {t | (fun _ : Fin 1 ↦ t) ∈ V}
  let φ : ℝ → RealEuclidean n := fun _ ↦ y
  have hUopen : IsOpen U := by
    exact Metric.isOpen_ball.preimage (continuous_pi fun _ ↦ continuous_id)
  have hUnonempty : U.Nonempty := by
    refine ⟨x0 0, ?_⟩
    change (fun _ : Fin 1 ↦ x0 0) ∈ Metric.ball x0 ε
    have heq : (fun _ : Fin 1 ↦ x0 0) = x0 := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    rw [heq]
    exact Metric.mem_ball_self hε
  have hVsubsetQ : V ⊆ Q := hball.trans interior_subset
  have hgraphEq : wilkie28SelectedWitnessGraph U φ =
      P ∩ realEuclideanSetProduct V ({y} : Set (RealEuclidean n)) := by
    ext z
    constructor
    · rintro ⟨t, htU, rfl⟩
      have htV : (fun _ : Fin 1 ↦ t) ∈ V := by
        change (fun _ : Fin 1 ↦ t) ∈ V at htU
        exact htU
      have htQ : (fun _ : Fin 1 ↦ t) ∈ Q := hVsubsetQ htV
      exact ⟨htQ, by
        exact ⟨by simpa only [realEuclideanTakeLeft_append] using htV,
          by simp [φ]⟩⟩
    · rintro ⟨hzP, hzV, hzY⟩
      let t : ℝ := realEuclideanTakeLeft z 0
      have hvis : (fun _ : Fin 1 ↦ t) = realEuclideanTakeLeft z := by
        funext i
        exact Fin.eq_zero i ▸ rfl
      have htU : t ∈ U := by
        change (fun _ : Fin 1 ↦ t) ∈ V
        rwa [hvis]
      have hyright : realEuclideanTakeRight z = y := by
        simpa only [mem_singleton_iff] using hzY
      have hdecomp :
          realEuclideanAppend (fun _ : Fin 1 ↦ t) y = z := by
        rw [hvis, ← hyright]
        exact realEuclideanAppend_takeLeft_takeRight z
      exact ⟨t, htU, hdecomp.symm⟩
  have hVmem : V ∈ C 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_ball x0 hε)
  have hyMem : ({y} : Set (RealEuclidean n)) ∈ C n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_singleton y)
  have hcylinderMem :
      realEuclideanSetProduct V ({y} : Set (RealEuclidean n)) ∈ C (1 + n) :=
    hC.ws3_prod (by omega) hn hVmem hyMem
  refine ⟨U, φ, hUopen, hUnonempty, ?_, ?_⟩
  · rw [hgraphEq]
    exact hC.ws1_inter (by omega) hcMem hcylinderMem
  · rw [hgraphEq]
    exact inter_subset_left

/-- A sufficient single-valued branch condition after the compact-component
reduction: every component whose visible projection has interior is
single-valued over the visible coordinate. -/
def Wilkie28LargeComponentProjectionInjective
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ (m : ℕ)
      (c : ConnectedComponents
        (charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m)),
    (interior (maxwellConnectedComponentProjection c)).Nonempty →
    Set.InjOn realEuclideanTakeLeft
      (maxwellConnectedComponentCarrier c)

/-- The two elementary graph branches proved in this file: a large component
is either single-valued, or one fixed hidden witness persists over a visible
set with interior. -/
def Wilkie28LargeComponentEasyGraphBranch
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ (m : ℕ)
      (c : ConnectedComponents
        (charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m)),
    (interior (maxwellConnectedComponentProjection c)).Nonempty →
    Set.InjOn realEuclideanTakeLeft
        (maxwellConnectedComponentCarrier c) ∨
      ∃ y : RealEuclidean n,
        (interior (maxwellFixedHiddenSection
          (maxwellConnectedComponentCarrier c) y)).Nonempty

/-- A more flexible branch condition: a finite polynomial-sign cut of each
large component makes its visible projection single-valued while retaining
interior. -/
def Wilkie28LargeComponentPolynomialGraphBranch
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ (m : ℕ)
      (c : ConnectedComponents
        (charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m)),
    (interior (maxwellConnectedComponentProjection c)).Nonempty →
    ∃ D : Set (RealEuclidean (1 + n)),
      PolynomialSignConstructible (1 + n) D ∧
      (interior (realEuclideanExistentialProjection
        (maxwellConnectedComponentCarrier c ∩ D))).Nonempty ∧
      Set.InjOn realEuclideanTakeLeft
        (maxwellConnectedComponentCarrier c ∩ D)

/-- Single-valuedness of every large compact component discharges the
component graph-extraction interface by the explicit selector above. -/
theorem wilkie28_componentGraphExtraction_of_largeComponentProjectionInjective
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hinjective : Wilkie28LargeComponentProjectionInjective F f a) :
    Wilkie28CompactComponentGraphExtraction C F f a := by
  intro m c hcInterior hcMem
  exact exists_local_graph_of_componentProjection_injective
    hC hn c hcMem hcInterior (hinjective m c hcInterior)

/-- Either elementary branch on every large component discharges compact
component graph extraction. -/
theorem wilkie28_componentGraphExtraction_of_largeComponentEasyGraphBranch
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (heasy : Wilkie28LargeComponentEasyGraphBranch F f a) :
    Wilkie28CompactComponentGraphExtraction C F f a := by
  intro m c hcInterior hcMem
  rcases heasy m c hcInterior with hinjective | ⟨y, hy⟩
  · exact exists_local_graph_of_componentProjection_injective
      hC hn c hcMem hcInterior hinjective
  · exact exists_local_graph_of_fixedHiddenSection_interior
      hC hn c hcMem y hy

/-- A polynomial-sign single-valued cut on every large component discharges
component graph extraction. -/
theorem wilkie28_componentGraphExtraction_of_largeComponentPolynomialGraphBranch
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hbranch : Wilkie28LargeComponentPolynomialGraphBranch F f a) :
    Wilkie28CompactComponentGraphExtraction C F f a := by
  intro m c hcInterior hcMem
  obtain ⟨D, hD, hcutInterior, hinjective⟩ :=
    hbranch m c hcInterior
  exact exists_local_graph_of_polynomialSign_injectiveCut
    hC hn hcMem hD hcutInterior hinjective

/-- The single-valued component branch supplies the original compact
incidence extraction property after WS5 localization. -/
theorem wilkie28_compactIncidenceGraphExtraction_of_largeComponentProjectionInjective
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hincidenceMem : wilkie28WeakSelectionIncidence F f a ∈
      charbonnelClosure S (1 + n))
    (hinjective : Wilkie28LargeComponentProjectionInjective F f a) :
    Wilkie28CompactIncidenceGraphExtraction
      (charbonnelClosure S) F f a :=
  wilkie28_compactIncidenceGraphExtraction_of_componentGraphExtraction
    hC F f a hincidenceClosed hincidenceMem
      (wilkie28_componentGraphExtraction_of_largeComponentProjectionInjective
        hC.toPositiveArityWeakSetStructure hn F f a hinjective)

/-- The combined injective/constant-section branch supplies the original
compact incidence extraction property after WS5 localization. -/
theorem wilkie28_compactIncidenceGraphExtraction_of_largeComponentEasyGraphBranch
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hincidenceMem : wilkie28WeakSelectionIncidence F f a ∈
      charbonnelClosure S (1 + n))
    (heasy : Wilkie28LargeComponentEasyGraphBranch F f a) :
    Wilkie28CompactIncidenceGraphExtraction
      (charbonnelClosure S) F f a :=
  wilkie28_compactIncidenceGraphExtraction_of_componentGraphExtraction
    hC F f a hincidenceClosed hincidenceMem
      (wilkie28_componentGraphExtraction_of_largeComponentEasyGraphBranch
        hC.toPositiveArityWeakSetStructure hn F f a heasy)

/-- The polynomial-cut branch supplies the original compact incidence
extraction property after WS5 localization. -/
theorem wilkie28_compactIncidenceGraphExtraction_of_largeComponentPolynomialGraphBranch
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hincidenceClosed : IsClosed (wilkie28WeakSelectionIncidence F f a))
    (hincidenceMem : wilkie28WeakSelectionIncidence F f a ∈
      charbonnelClosure S (1 + n))
    (hbranch : Wilkie28LargeComponentPolynomialGraphBranch F f a) :
    Wilkie28CompactIncidenceGraphExtraction
      (charbonnelClosure S) F f a :=
  wilkie28_compactIncidenceGraphExtraction_of_componentGraphExtraction
    hC F f a hincidenceClosed hincidenceMem
      (wilkie28_componentGraphExtraction_of_largeComponentPolynomialGraphBranch
        hC.toPositiveArityWeakSetStructure hn F f a hbranch)

end AbelFormalization
