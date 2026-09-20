import AbelFormalization.CharbonnelSection5AnalyticReduction
import AbelFormalization.MaxwellLocalFiberCardinality

/-!
# The infinite-fibre locus in Charbonnel 5.4--5.6

The compact part of the Section 5 analytic reduction previously asked for an
exceptional base together with a separate proof that every fibre outside that
base is finite.  The source's canonical exceptional base is the locus where
the vertical fibre is infinite, so that finiteness statement is logical rather
than geometric.

This file records the canonical locus, proves its family membership from WS5,
and proves that interior of the locus forces interior of the original compact
set.  The source's further claim that this locus is locally closed is false in
general, even for compact semialgebraic sets.  The downstream repair in
`CharbonnelSection56InfiniteFiberLocalClosedness` uses the closure of the locus
as the closed exceptional base and obtains the needed interior lift from the
closure-interior regularity already required by the main pipeline.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Base points whose vertical fibre is infinite. -/
def charbonnelInfiniteVerticalFiberLocus {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Set (RealEuclidean n) :=
  {x | (charbonnelVerticalFiber S x).Infinite}

@[simp]
theorem mem_charbonnelInfiniteVerticalFiberLocus_iff
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {x : RealEuclidean n} :
    x ∈ charbonnelInfiniteVerticalFiberLocus S ↔
      (charbonnelVerticalFiber S x).Infinite :=
  Iff.rfl

/-- Outside the canonical exceptional locus, the vertical fibre is finite. -/
theorem charbonnelVerticalFiber_finite_of_not_mem_infiniteLocus
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {x : RealEuclidean n}
    (hx : x ∉ charbonnelInfiniteVerticalFiberLocus S) :
    (charbonnelVerticalFiber S x).Finite := by
  change ¬ ¬ (charbonnelVerticalFiber S x).Finite at hx
  exact Classical.not_not.mp hx

/-! ## A Baire slab lemma -/

/-- Appending any fixed final coordinate is continuous. -/
theorem continuous_charbonnelAppendLastCoordinate_const
    {n : ℕ} (t : ℝ) :
    Continuous
      (fun x : RealEuclidean n ↦ charbonnelAppendLastCoordinate x t) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [charbonnelAppendLastCoordinate_last] using
      (continuous_const : Continuous (fun _ : RealEuclidean n ↦ t))
  · simpa only [charbonnelAppendLastCoordinate_castSucc] using (continuous_apply j :
      Continuous (fun x : RealEuclidean n ↦ x j))

/-- Base points above which `S` contains the whole closed vertical interval
`[a,b]`. -/
def charbonnelVerticalClosedSlabBase {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (a b : ℝ) :
    Set (RealEuclidean n) :=
  {x | Set.Icc a b ⊆ charbonnelVerticalFiber S x}

@[simp]
theorem mem_charbonnelVerticalClosedSlabBase_iff
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {a b : ℝ} {x : RealEuclidean n} :
    x ∈ charbonnelVerticalClosedSlabBase S a b ↔
      Set.Icc a b ⊆ charbonnelVerticalFiber S x :=
  Iff.rfl

/-- Closedness of `S` makes every fixed closed-slab base closed. -/
theorem isClosed_charbonnelVerticalClosedSlabBase
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : IsClosed S) (a b : ℝ) :
    IsClosed (charbonnelVerticalClosedSlabBase S a b) := by
  rw [show charbonnelVerticalClosedSlabBase S a b =
      ⋂ t : ℝ, {x : RealEuclidean n |
        t ∈ Set.Icc a b → charbonnelAppendLastCoordinate x t ∈ S} by
    ext x
    simp only [charbonnelVerticalClosedSlabBase, charbonnelVerticalFiber,
      Set.mem_ofPred_eq, Set.mem_iInter]
    rfl]
  apply isClosed_iInter
  intro t
  by_cases ht : t ∈ Set.Icc a b
  · simp only [ht, true_implies]
    change IsClosed
      ((fun x : RealEuclidean n ↦
        charbonnelAppendLastCoordinate x t) ⁻¹' S)
    exact hS.preimage (continuous_charbonnelAppendLastCoordinate_const t)
  · simp only [ht, false_implies, Set.ofPred_true, isClosed_univ]

/-- The countable type of nondegenerate rational closed intervals. -/
abbrev CharbonnelRationalInterval :=
  {q : ℚ × ℚ // q.1 < q.2}

instance : Nonempty CharbonnelRationalInterval :=
  ⟨⟨(0, 1), by norm_num⟩⟩

/-- A fixed enumeration of all nondegenerate rational intervals. -/
noncomputable def charbonnelRationalIntervalEnumeration :
    ℕ → CharbonnelRationalInterval :=
  Classical.choose (exists_surjective_nat CharbonnelRationalInterval)

theorem charbonnelRationalIntervalEnumeration_surjective :
    Function.Surjective charbonnelRationalIntervalEnumeration :=
  Classical.choose_spec (exists_surjective_nat CharbonnelRationalInterval)

/-- The closed-slab base corresponding to the `m`th rational interval. -/
def charbonnelRationalClosedSlabBase {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (m : ℕ) :
    Set (RealEuclidean n) :=
  charbonnelVerticalClosedSlabBase S
    (charbonnelRationalIntervalEnumeration m).1.1
    (charbonnelRationalIntervalEnumeration m).1.2

theorem isClosed_charbonnelRationalClosedSlabBase
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : IsClosed S) (m : ℕ) :
    IsClosed (charbonnelRationalClosedSlabBase S m) :=
  isClosed_charbonnelVerticalClosedSlabBase hS _ _

/-- If every infinite vertical fibre has interior, the infinite-fibre locus
is covered by the countable family of rational closed-slab bases. -/
theorem charbonnelInfiniteVerticalFiberLocus_subset_iUnion_rationalClosedSlabBase
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hfiber : ∀ x : RealEuclidean n,
      (charbonnelVerticalFiber S x).Infinite →
        (interior (charbonnelVerticalFiber S x)).Nonempty) :
    charbonnelInfiniteVerticalFiberLocus S ⊆
      ⋃ m : ℕ, charbonnelRationalClosedSlabBase S m := by
  intro x hx
  obtain ⟨t, ht⟩ := hfiber x hx
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) t ht
  obtain ⟨a, haLeft, haRight⟩ :=
    exists_rat_btwn (sub_lt_self t hε)
  obtain ⟨b, hbLeft, hbRight⟩ :=
    exists_rat_btwn (lt_add_of_pos_right t hε)
  let q : CharbonnelRationalInterval :=
    ⟨(a, b), by exact_mod_cast haRight.trans hbLeft⟩
  obtain ⟨m, hm⟩ :=
    charbonnelRationalIntervalEnumeration_surjective q
  apply Set.mem_iUnion.mpr
  refine ⟨m, ?_⟩
  rw [charbonnelRationalClosedSlabBase, hm]
  intro u hu
  apply interior_subset
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> change _ at hu
  · linarith [hu.1]
  · linarith [hu.2]

/-- Baire category selects one rational vertical slab above a base set with
interior. -/
theorem exists_rationalClosedSlabBase_interior_of_infiniteLocus_interior
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : IsClosed S)
    (hfiber : ∀ x : RealEuclidean n,
      (charbonnelVerticalFiber S x).Infinite →
        (interior (charbonnelVerticalFiber S x)).Nonempty)
    (hlocus : (interior
      (charbonnelInfiniteVerticalFiberLocus S)).Nonempty) :
    ∃ m : ℕ,
      (interior (charbonnelRationalClosedSlabBase S m)).Nonempty := by
  have hcover :=
    charbonnelInfiniteVerticalFiberLocus_subset_iUnion_rationalClosedSlabBase
      hfiber
  have hunionInterior :
      (interior (⋃ m : ℕ,
        charbonnelRationalClosedSlabBase S m)).Nonempty :=
    hlocus.mono (interior_mono hcover)
  by_contra hnone
  have hempty : ∀ m : ℕ,
      interior (charbonnelRationalClosedSlabBase S m) = ∅ := by
    intro m
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hm
    exact hnone ⟨m, hm⟩
  rw [interior_iUnion_eq_empty_of_closed
    (fun m ↦ isClosed_charbonnelRationalClosedSlabBase hS m)
    hempty] at hunionInterior
  exact hunionInterior.ne_empty rfl

/-- A nondegenerate closed vertical slab above a base with interior gives
interior of the ambient set. -/
theorem interior_nonempty_of_verticalClosedSlabBase_interior
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    {a b : ℝ} (hab : a < b)
    (hbase : (interior
      (charbonnelVerticalClosedSlabBase S a b)).Nonempty) :
    (interior S).Nonempty := by
  obtain ⟨x, hx⟩ := hbase
  let t : ℝ := (a + b) / 2
  let z : RealEuclidean (n + 1) :=
    charbonnelAppendLastCoordinate x t
  let O : Set (RealEuclidean (n + 1)) :=
    charbonnelVerticalBaseCoordinate ⁻¹'
        interior (charbonnelVerticalClosedSlabBase S a b) ∩
      charbonnelVerticalLastCoordinate ⁻¹' Set.Ioo a b
  have hOopen : IsOpen O :=
    (isOpen_interior.preimage
      continuous_charbonnelVerticalBaseCoordinate).inter
      (isOpen_Ioo.preimage continuous_charbonnelVerticalLastCoordinate)
  have hzO : z ∈ O := by
    refine ⟨?_, ?_⟩
    · simpa [z, charbonnelVerticalBaseCoordinate,
        charbonnelAppendLastCoordinate] using hx
    · change charbonnelVerticalLastCoordinate z ∈ Set.Ioo a b
      simp only [z, charbonnelVerticalLastCoordinate,
        charbonnelAppendLastCoordinate_last, Set.mem_Ioo]
      change a < t ∧ t < b
      dsimp only [t]
      constructor <;> linarith
  have hOS : O ⊆ S := by
    intro w hw
    have hbaseMem : charbonnelVerticalBaseCoordinate w ∈
        charbonnelVerticalClosedSlabBase S a b :=
      interior_subset hw.1
    have hlastMem : charbonnelVerticalLastCoordinate w ∈ Set.Icc a b :=
      ⟨hw.2.1.le, hw.2.2.le⟩
    have hwS := hbaseMem hlastMem
    change charbonnelAppendLastCoordinate
      (charbonnelVerticalBaseCoordinate w)
      (charbonnelVerticalLastCoordinate w) ∈ S at hwS
    simpa only [charbonnelVerticalBaseCoordinate,
      charbonnelVerticalLastCoordinate,
      charbonnelAppendLastCoordinate_takeLeft_last] using hwS
  exact ⟨z, (hOopen.subset_interior_iff.mpr hOS) hzO⟩

/-- WS5 implies that every infinite scalar vertical fibre has nonempty
interior: a uniform component bound gives a finite unary-piece
decomposition, whose empty-interior case is finite. -/
theorem charbonnelVerticalFiber_interior_nonempty_of_infinite_of_ws5
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + 1))} (hSmem : S ∈ C (n + 1))
    (x : RealEuclidean n)
    (hinfinite : (charbonnelVerticalFiber S x).Infinite) :
    (interior (charbonnelVerticalFiber S x)).Nonempty := by
  obtain ⟨N, hN⟩ :=
    exists_maxwellScalarFiber_component_bound_of_ws5 hC hn hSmem
  have hcomponents :
      ENat.card (ConnectedComponents (charbonnelVerticalFiber S x)) ≤ N := by
    change ENat.card (ConnectedComponents (maxwellScalarFiber S x)) ≤ N
    exact hN x
  have hdecomposition :
      UnaryPieceDecomposable (charbonnelVerticalFiber S x) :=
    unaryPieceDecomposable_of_enatCard_connectedComponents_le
      (charbonnelVerticalFiber S x) N hcomponents
  by_contra hempty
  exact hinfinite (hdecomposition.finite_of_interior_eq_empty
    (Set.not_nonempty_iff_eq_empty.mp hempty))

/-- For a closed family member in positive base dimension, WS5 supplies the
interior-lift field of the infinite-fibre-locus data automatically. -/
theorem charbonnelInfiniteVerticalFiberLocus_interior_lift_of_ws5
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + 1))}
    (hSclosed : IsClosed S) (hSmem : S ∈ C (n + 1))
    (hlocus : (interior
      (charbonnelInfiniteVerticalFiberLocus S)).Nonempty) :
    (interior S).Nonempty := by
  obtain ⟨m, hm⟩ :=
    exists_rationalClosedSlabBase_interior_of_infiniteLocus_interior
      hSclosed
      (fun x hx ↦
        charbonnelVerticalFiber_interior_nonempty_of_infinite_of_ws5
          hC hn hSmem x hx)
      hlocus
  exact interior_nonempty_of_verticalClosedSlabBase_interior
    (show ((charbonnelRationalIntervalEnumeration m).1.1 : ℝ) <
        (charbonnelRationalIntervalEnumeration m).1.2 by
      exact_mod_cast (charbonnelRationalIntervalEnumeration m).2)
    hm

/-! ## Finite-cardinality presentation of the infinite-fibre locus -/

/-- If a scalar fibre has at most `N` connected components, it is infinite
exactly when it contains at least `N + 1` points.  The reverse implication is
the one-dimensional component collision: `N + 1` ordered points force a
nondegenerate interval in the fibre. -/
theorem infinite_maxwellScalarFiber_iff_encard_ge_succ_of_component_bound
    {p N : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hcomponents :
      ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N) :
    (maxwellScalarFiber R x).Infinite ↔
      (N + 1 : ℕ∞) ≤ (maxwellScalarFiber R x).encard := by
  constructor
  · intro hinfinite
    rw [hinfinite.encard_eq]
    exact le_top
  · intro hcard
    have hx : x ∈
        maxwellScalarFiberCardinalityAtLeast Set.univ R (N + 1) :=
      (mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
        Set.univ R x).mpr ⟨Set.mem_univ x, hcard⟩
    obtain ⟨_hxuniv, y, hy⟩ :=
      (mem_maxwellScalarFiberCardinalityAtLeast_succ_iff
        Set.univ R x).mp hx
    obtain ⟨a, b, hab, hIcc⟩ :=
      exists_interval_subset_maxwellScalarFiber_of_orderedWitness
        hcomponents hy
    exact (Set.Icc_infinite hab).mono hIcc

/-- Under a uniform component bound, the infinite-fibre locus is one of the
finite-cardinality loci already constructed by ordered projection. -/
theorem infiniteVerticalFiberLocus_eq_cardinalityAtLeast_succ_of_component_bound
    {n N : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hcomponents : ∀ x : RealEuclidean n,
      ENat.card (ConnectedComponents (maxwellScalarFiber S x)) ≤ N) :
    charbonnelInfiniteVerticalFiberLocus S =
      maxwellScalarFiberCardinalityAtLeast Set.univ S (N + 1) := by
  ext x
  rw [mem_charbonnelInfiniteVerticalFiberLocus_iff,
    mem_maxwellScalarFiberCardinalityAtLeast_iff_encard]
  simp only [Set.mem_univ, true_and]
  change (maxwellScalarFiber S x).Infinite ↔ _
  exact
    infinite_maxwellScalarFiber_iff_encard_ge_succ_of_component_bound
      (hcomponents x)

/-- WS5 makes membership of the infinite-fibre locus automatic in a
Charbonnel closure: the preceding equality presents it by a finite ordered
selection followed by projection. -/
theorem charbonnelInfiniteVerticalFiberLocus_mem_charbonnelClosure_of_ws5
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + 1))}
    (hSmem : S ∈ charbonnelClosure S0 (n + 1)) :
    charbonnelInfiniteVerticalFiberLocus S ∈ charbonnelClosure S0 n := by
  obtain ⟨N, hcomponents⟩ :=
    exists_maxwellScalarFiber_component_bound_of_ws5 hC hn hSmem
  rw [infiniteVerticalFiberLocus_eq_cardinalityAtLeast_succ_of_component_bound
    hcomponents]
  exact maxwellScalarFiberCardinalityAtLeast_mem_charbonnelClosure
    hC.toPositiveArityWeakSetStructure hn
    (hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n))
    hSmem

/-- Legacy conditional output for choosing the exceptional base to be the
infinite-fibre locus itself.  Its local-closedness field is too strong in
general; the downstream repair instead closes the locus. -/
structure CharbonnelCompactInfiniteFiberLocusData
    (C : EuclideanSetFamily) {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop where
  locus_mem : charbonnelInfiniteVerticalFiberLocus S ∈ C n
  locus_locallyClosed : IsLocallyClosed
    (charbonnelInfiniteVerticalFiberLocus S)
  interior_lift :
    (interior (charbonnelInfiniteVerticalFiberLocus S)).Nonempty →
      (interior S).Nonempty

/-- Family-wide availability of the canonical infinite-fibre-locus data for
compact members. -/
def CharbonnelSection56InfiniteFiberLocusReduction
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ S : Set (RealEuclidean (n + 1)),
    IsCompact S → S ∈ C (n + 1) →
      CharbonnelCompactInfiniteFiberLocusData C S

/-- Legacy regularity package retained for compatibility with earlier
conditional reductions.  Membership is automatic, while the local-closedness
field is false for general compact semialgebraic relations. -/
structure CharbonnelCompactInfiniteFiberLocusRegularity
    (C : EuclideanSetFamily) {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop where
  locus_mem : charbonnelInfiniteVerticalFiberLocus S ∈ C n
  locus_locallyClosed : IsLocallyClosed
    (charbonnelInfiniteVerticalFiberLocus S)

/-- Family-wide regularity of the infinite-fibre locus for compact members. -/
def CharbonnelSection56InfiniteFiberLocusRegularity
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ S : Set (RealEuclidean (n + 1)),
    IsCompact S → S ∈ C (n + 1) →
      CharbonnelCompactInfiniteFiberLocusRegularity C S

/-- A historical, too-strong hypothesis saying the infinite-fibre locus
itself is locally closed.  This is not used by the final pipeline; see
`CharbonnelSection56InfiniteFiberLocalClosedness` for the valid closed-locus
replacement. -/
def CharbonnelSection56InfiniteFiberLocusLocallyClosed
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ S : Set (RealEuclidean (n + 1)),
    IsCompact S → S ∈ C (n + 1) →
      IsLocallyClosed (charbonnelInfiniteVerticalFiberLocus S)

/-- Conditional adapter from the historical local-closedness hypothesis. -/
theorem charbonnelSection56InfiniteFiberLocusRegularity_of_locallyClosed
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hlocallyClosed : CharbonnelSection56InfiniteFiberLocusLocallyClosed
      (charbonnelClosure S0)) :
    CharbonnelSection56InfiniteFiberLocusRegularity
      (charbonnelClosure S0) := by
  intro n hn S hScompact hSmem
  exact
    { locus_mem :=
        charbonnelInfiniteVerticalFiberLocus_mem_charbonnelClosure_of_ws5
          hC hn hSmem
      locus_locallyClosed := hlocallyClosed hn S hScompact hSmem }

/-- WS5 upgrades locus regularity to the full canonical exceptional-base
data. -/
theorem CharbonnelCompactInfiniteFiberLocusRegularity.toData
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {n : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + 1))}
    (hScompact : IsCompact S) (hSmem : S ∈ C (n + 1))
    (regularity : CharbonnelCompactInfiniteFiberLocusRegularity C S) :
    CharbonnelCompactInfiniteFiberLocusData C S where
  locus_mem := regularity.locus_mem
  locus_locallyClosed := regularity.locus_locallyClosed
  interior_lift :=
    charbonnelInfiniteVerticalFiberLocus_interior_lift_of_ws5
      hC hn hScompact.isClosed hSmem

/-- Thus the compact reduction follows from locus membership and local
closedness alone once WS5 is available. -/
theorem charbonnelSection56InfiniteFiberLocusReduction_of_regularity
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hregularity : CharbonnelSection56InfiniteFiberLocusRegularity C) :
    CharbonnelSection56InfiniteFiberLocusReduction C := by
  intro n hn S hScompact hSmem
  exact (hregularity hn S hScompact hSmem).toData
    hC hn hScompact hSmem

/-- Conditional legacy reduction under the too-strong local-closedness
hypothesis. -/
theorem charbonnelSection56InfiniteFiberLocusReduction_of_locallyClosed
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hlocallyClosed : CharbonnelSection56InfiniteFiberLocusLocallyClosed
      (charbonnelClosure S0)) :
    CharbonnelSection56InfiniteFiberLocusReduction
      (charbonnelClosure S0) :=
  charbonnelSection56InfiniteFiberLocusReduction_of_regularity hC
    (charbonnelSection56InfiniteFiberLocusRegularity_of_locallyClosed
      hC hlocallyClosed)

/-- Canonical infinite-fibre-locus data supplies the exceptional-base witness
used by the measure-theoretic reduction. -/
def CharbonnelCompactInfiniteFiberLocusData.toExceptionalFiberBase
    {C : EuclideanSetFamily} {n : ℕ}
    {S : Set (RealEuclidean (n + 1))}
    (data : CharbonnelCompactInfiniteFiberLocusData C S) :
    CharbonnelCompactExceptionalFiberBase C S where
  base := charbonnelInfiniteVerticalFiberLocus S
  base_mem := data.locus_mem
  base_locallyClosed := data.locus_locallyClosed
  fiber_finite_off := fun _ hx ↦
    charbonnelVerticalFiber_finite_of_not_mem_infiniteLocus hx
  interior_lift := data.interior_lift

/-- The canonical locus reduction implies the earlier compact-fibre
reduction, without an independent finiteness premise. -/
theorem charbonnelSection56CompactFiberReduction_of_infiniteFiberLocus
    {C : EuclideanSetFamily}
    (hreduction : CharbonnelSection56InfiniteFiberLocusReduction C) :
    CharbonnelSection56CompactFiberReduction C := by
  intro n hn S hScompact hSmem
  exact ⟨(hreduction hn S hScompact hSmem).toExceptionalFiberBase⟩

/-- Hence the canonical source data proves the compact positive-volume
conclusion after `P'_n`; all Fubini and measure transport remain internal. -/
theorem charbonnelCompactPositiveVolumeInterior_of_infiniteFiberLocusReduction
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hreduction : CharbonnelSection56InfiniteFiberLocusReduction C) :
    ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
      CharbonnelCompactPositiveVolumeInterior C (n + 1) :=
  charbonnelCompactPositiveVolumeInterior_of_section56FiberReduction hmem
    (charbonnelSection56CompactFiberReduction_of_infiniteFiberLocus
      hreduction)

/-- Conditional source-facing compact conclusion using the legacy regularity
package. -/
theorem charbonnelCompactPositiveVolumeInterior_of_infiniteFiberLocusRegularity
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hmem : CharbonnelSection5TraceMembership C)
    (hregularity : CharbonnelSection56InfiniteFiberLocusRegularity C) :
    ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
      CharbonnelCompactPositiveVolumeInterior C (n + 1) :=
  charbonnelCompactPositiveVolumeInterior_of_infiniteFiberLocusReduction
    hmem
    (charbonnelSection56InfiniteFiberLocusReduction_of_regularity
      hC hregularity)

/-- Conditional Charbonnel-closure specialization under the historical
local-closedness hypothesis. -/
theorem charbonnelCompactPositiveVolumeInterior_of_infiniteFiberLocusLocallyClosed
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0))
    (hlocallyClosed : CharbonnelSection56InfiniteFiberLocusLocallyClosed
      (charbonnelClosure S0)) :
    ∀ {n : ℕ}, 0 < n → CharbonnelPPrime (charbonnelClosure S0) n →
      CharbonnelCompactPositiveVolumeInterior
        (charbonnelClosure S0) (n + 1) :=
  charbonnelCompactPositiveVolumeInterior_of_infiniteFiberLocusReduction
    hmem
    (charbonnelSection56InfiniteFiberLocusReduction_of_locallyClosed
      hC hlocallyClosed)

/-- Together with the bounded graph extraction from 5.7, the canonical
infinite-fibre locus reconstructs the complete Section 5 analytic step. -/
theorem charbonnelSection5AnalyticStep_of_infiniteFiberLocus_and_graphReduction
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (hcompact : CharbonnelSection56InfiniteFiberLocusReduction C)
    (hbounded : CharbonnelSection57BoundedGraphReduction C) :
    CharbonnelSection5AnalyticStep C :=
  charbonnelSection5AnalyticStep_of_fiberAndGraphReductions hmem
    (charbonnelSection56CompactFiberReduction_of_infiniteFiberLocus hcompact)
    hbounded

/-- Conditional reassembly from the legacy locus-regularity package. -/
theorem charbonnelSection5AnalyticStep_of_infiniteFiberLocusRegularity_and_graphReduction
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hmem : CharbonnelSection5TraceMembership C)
    (hcompact : CharbonnelSection56InfiniteFiberLocusRegularity C)
    (hbounded : CharbonnelSection57BoundedGraphReduction C) :
    CharbonnelSection5AnalyticStep C :=
  charbonnelSection5AnalyticStep_of_infiniteFiberLocus_and_graphReduction
    hmem
    (charbonnelSection56InfiniteFiberLocusReduction_of_regularity
      hC hcompact)
    hbounded

/-- Conditional Charbonnel-closure reassembly under the historical
local-closedness hypothesis. -/
theorem charbonnelSection5AnalyticStep_of_infiniteFiberLocusLocallyClosed_and_graphReduction
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0))
    (hcompact : CharbonnelSection56InfiniteFiberLocusLocallyClosed
      (charbonnelClosure S0))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure S0)) :
    CharbonnelSection5AnalyticStep (charbonnelClosure S0) :=
  charbonnelSection5AnalyticStep_of_infiniteFiberLocus_and_graphReduction
    hmem
    (charbonnelSection56InfiniteFiberLocusReduction_of_locallyClosed
      hC hcompact)
    hbounded

/-- Literal-zero specialization with the compact residual stated only in
terms of the canonical infinite-fibre locus. -/
theorem
    literalZeroSet_charbonnelClosure_section5AnalyticStep_of_infiniteFiberLocus_and_graphReduction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hcompact : CharbonnelSection56InfiniteFiberLocusReduction
      (charbonnelClosure (literalZeroSetFamily G)))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)) :=
  charbonnelSection5AnalyticStep_of_infiniteFiberLocus_and_graphReduction
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
    hcompact hbounded

/-- Literal-zero specialization of the legacy locus-regularity route. -/
theorem
    literalZeroSet_charbonnelClosure_section5AnalyticStep_of_infiniteFiberLocusRegularity_and_graphReduction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hcompact : CharbonnelSection56InfiniteFiberLocusRegularity
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
    charbonnelSection5AnalyticStep_of_infiniteFiberLocusRegularity_and_graphReduction
      hC
      (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
      hcompact hbounded

/-- Literal-zero specialization under the historical local-closedness
hypothesis. -/
theorem
    literalZeroSet_charbonnelClosure_section5AnalyticStep_of_infiniteFiberLocusLocallyClosed_and_graphReduction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hcompact : CharbonnelSection56InfiniteFiberLocusLocallyClosed
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
    charbonnelSection5AnalyticStep_of_infiniteFiberLocusLocallyClosed_and_graphReduction
      hC
      (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
      hcompact hbounded

/-- Pointwise Abel endpoint whose compact Section 5 premise is the canonical
infinite-fibre-locus statement. -/
theorem
    IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers_and_infiniteFiberLocus
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcompact : CharbonnelSection56InfiniteFiberLocusReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
      hUFF hselection
      (literalZeroSet_charbonnelClosure_section5AnalyticStep_of_infiniteFiberLocus_and_graphReduction
        hG hsmooth hcompact hbounded)
      hcells

/-- Stronger pointwise Abel endpoint with the compact Section 5 residual
narrowed to regularity of the canonical infinite-fibre locus. -/
theorem
    IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers_and_infiniteFiberLocusRegularity
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcompact : CharbonnelSection56InfiniteFiberLocusRegularity
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
      hUFF hselection
      (literalZeroSet_charbonnelClosure_section5AnalyticStep_of_infiniteFiberLocusRegularity_and_graphReduction
        hG hsmooth hUFF hcompact hbounded)
      hcells

/-- Historical conditional Abel endpoint under the too-strong
local-closedness hypothesis. -/
theorem
    IsAbel.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers_and_infiniteFiberLocusLocallyClosed
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcompact : CharbonnelSection56InfiniteFiberLocusLocallyClosed
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hbounded : CharbonnelSection57BoundedGraphReduction
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hcells : CharbonnelBoundedClosedBoundaryCellCoverAssembly
      (abelGeometricFamily A)) :
    OMinimal A := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    hA.oMinimal_of_charbonnelSourceSteps_automaticProjection_and_boundedCellCovers
      hUFF hselection
      (literalZeroSet_charbonnelClosure_section5AnalyticStep_of_infiniteFiberLocusLocallyClosed_and_graphReduction
        hG hsmooth hUFF hcompact hbounded)
      hcells

end AbelFormalization
