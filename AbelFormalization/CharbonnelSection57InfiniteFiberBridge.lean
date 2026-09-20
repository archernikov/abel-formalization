import AbelFormalization.CharbonnelSection56InfiniteFiberLocalClosedness
import AbelFormalization.CharbonnelSection57GraphExtraction

/-!
# The infinite-fibre bridge for Charbonnel section 5.7

The stable vertical intervals of section 5.3 meet every limiting point
fibre, but `CharbonnelSection57GraphExtraction` previously retained the
opposite cardinal inequality as an independent field.  Compactness closes
that gap away from the infinite-fibre locus.

Indeed, two distinct points of one point fibre which lie in the same stable
interval remain in the same connected component over every shrinking base
ball.  Every height between them therefore occurs over every such ball, and
compactness puts the whole interval in the limiting point fibre.  A finite
point fibre consequently contains at most one point in each stable interval.

The closed exceptional base from section 5.6 supplies precisely that
finiteness.  The family-level theorem below therefore reduces the remaining
section 5.7 witness to stable-component localization inside an arbitrary
nonempty open part of the trace interior; no separate fibre-cardinality
hypothesis remains.
-/

noncomputable section

open Set Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Stable intervals have finite limiting slices -/

private theorem mem_realConnectedComponentCarrier_iff_mk_eq'
    (s : Set ℝ) (c : ConnectedComponents s) {t : ℝ} (ht : t ∈ s) :
    t ∈ realConnectedComponentCarrier s c ↔
      ConnectedComponents.mk (⟨t, ht⟩ : s) = c := by
  constructor
  · rintro ⟨p, hp, hpt⟩
    have hpComponent : ConnectedComponents.mk p = c :=
      (ConnectedComponents.coe_eq_coe'.mpr hp).trans
        (connectedComponentRepresentative_mk s c)
    have hpeq : p = (⟨t, ht⟩ : s) := by
      apply Subtype.ext
      exact hpt
    simpa only [← hpeq] using hpComponent
  · intro hcomponent
    refine ⟨(⟨t, ht⟩ : s), ?_, rfl⟩
    apply ConnectedComponents.coe_eq_coe'.mp
    exact hcomponent.trans (connectedComponentRepresentative_mk s c).symm

/-- Two limiting fibre points in one stable interval force the entire real
interval between them to lie in the limiting fibre. -/
theorem
    CharbonnelStableLocalVerticalIntervalWitness.Icc_subset_fiber_of_mem_interval
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    {y : RealEuclidean n} (hy : y ∈ w.innerBall)
    {i : Fin w.count} {a b : ℝ}
    (haFiber : a ∈ charbonnelVerticalFiber S y)
    (haInterval : a ∈ w.interval i)
    (hbFiber : b ∈ charbonnelVerticalFiber S y)
    (hbInterval : b ∈ w.interval i) :
    Set.Icc a b ⊆ charbonnelVerticalFiber S y := by
  intro t ht
  let Radius := {s : ℝ // 0 < s ∧ s ≤ w.radius / 2}
  let halfRadius : Radius :=
    ⟨w.radius / 2, by constructor <;> linarith [w.radius_pos]⟩
  let _ : Nonempty Radius := ⟨halfRadius⟩
  have hsub (s : Radius) :
      Metric.closedBall y (s : ℝ) ⊆
        Metric.closedBall w.center w.radius := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    have hy' : dist y w.center ≤ w.radius / 2 :=
      Metric.mem_closedBall.mp hy
    calc
      dist z w.center ≤ dist z y + dist y w.center := dist_triangle _ _ _
      _ ≤ (s : ℝ) + w.radius / 2 := add_le_add hz hy'
      _ ≤ w.radius / 2 + w.radius / 2 := by linarith [s.property.2]
      _ = w.radius := by ring
  have htImage : ∀ s : Radius,
      t ∈ charbonnelVerticalImageOver S (Metric.closedBall y (s : ℝ)) := by
    intro s
    let smallImage : Set ℝ :=
      charbonnelVerticalImageOver S (Metric.closedBall y (s : ℝ))
    let largeImage : Set ℝ :=
      charbonnelVerticalImageOver S
        (Metric.closedBall w.center w.radius)
    have hySmall : y ∈ Metric.closedBall y (s : ℝ) :=
      Metric.mem_closedBall_self s.property.1.le
    let pa : smallImage := ⟨a, y, hySmall, haFiber⟩
    let pb : smallImage := ⟨b, y, hySmall, hbFiber⟩
    have haLarge : a ∈ largeImage :=
      charbonnelVerticalImageOver_mono S (hsub s) pa.property
    have hbLarge : b ∈ largeImage :=
      charbonnelVerticalImageOver_mono S (hsub s) pb.property
    have hpaMap :
        charbonnelVerticalComponentInclusionMap S (hsub s)
            (ConnectedComponents.mk pa) = w.label i := by
      rw [charbonnelVerticalComponentInclusionMap_mk]
      exact (mem_realConnectedComponentCarrier_iff_mk_eq'
        largeImage (w.label i) haLarge).mp haInterval
    have hpbMap :
        charbonnelVerticalComponentInclusionMap S (hsub s)
            (ConnectedComponents.mk pb) = w.label i := by
      rw [charbonnelVerticalComponentInclusionMap_mk]
      exact (mem_realConnectedComponentCarrier_iff_mk_eq'
        largeImage (w.label i) hbLarge).mp hbInterval
    have hcomponent : ConnectedComponents.mk pa =
        ConnectedComponents.mk pb :=
      (w.stable y s s.property.1 (hsub s)).2.1
        (hpaMap.trans hpbMap.symm)
    let K : Set ℝ := Subtype.val '' connectedComponent pa
    have hKpreconnected : IsPreconnected K :=
      isPreconnected_connectedComponent.image _
        continuous_subtype_val.continuousOn
    have haK : a ∈ K := ⟨pa, mem_connectedComponent, rfl⟩
    have hpbConnected : pb ∈ connectedComponent pa := by
      apply ConnectedComponents.coe_eq_coe'.mp
      exact hcomponent.symm
    have hbK : b ∈ K := ⟨pb, hpbConnected, rfl⟩
    obtain ⟨q, _hq, hqt⟩ := hKpreconnected.Icc_subset haK hbK ht
    have hqSmall : (q : ℝ) ∈ smallImage := q.property
    simpa only [hqt] using hqSmall
  let K : Radius → Set (RealEuclidean (n + 1)) := fun s ↦
    S ∩ (charbonnelVerticalBaseCoordinate ⁻¹'
      Metric.closedBall y (s : ℝ) ∩
        charbonnelVerticalLastCoordinate ⁻¹' ({t} : Set ℝ))
  have hKnonempty : ∀ s, (K s).Nonempty := by
    intro s
    obtain ⟨x, hxBall, hxt⟩ := htImage s
    let z : RealEuclidean (n + 1) :=
      charbonnelAppendLastCoordinate x t
    refine ⟨z, hxt, ?_, ?_⟩
    · change charbonnelVerticalBaseCoordinate z ∈
        Metric.closedBall y (s : ℝ)
      simpa [z, charbonnelVerticalBaseCoordinate,
        charbonnelAppendLastCoordinate] using hxBall
    · change charbonnelVerticalLastCoordinate z ∈ ({t} : Set ℝ)
      simp [z, charbonnelVerticalLastCoordinate]
  have hKcompact : ∀ s, IsCompact (K s) := by
    intro s
    exact hScompact.inter_right
      ((Metric.isClosed_closedBall.preimage
          continuous_charbonnelVerticalBaseCoordinate).inter
        (isClosed_singleton.preimage
          continuous_charbonnelVerticalLastCoordinate))
  have hKclosed : ∀ s, IsClosed (K s) := fun s ↦ (hKcompact s).isClosed
  have hKdirected : Directed (· ⊇ ·) K := by
    intro r s
    let u : Radius :=
      ⟨min (r : ℝ) (s : ℝ),
        lt_min r.property.1 s.property.1,
        (min_le_left (r : ℝ) (s : ℝ)).trans r.property.2⟩
    refine ⟨u, ?_, ?_⟩
    · intro z hz
      refine ⟨hz.1, ?_, hz.2.2⟩
      exact Metric.mem_closedBall.mpr
        ((Metric.mem_closedBall.mp hz.2.1).trans
          (min_le_left (r : ℝ) (s : ℝ)))
    · intro z hz
      refine ⟨hz.1, ?_, hz.2.2⟩
      exact Metric.mem_closedBall.mpr
        ((Metric.mem_closedBall.mp hz.2.1).trans
          (min_le_right (r : ℝ) (s : ℝ)))
  obtain ⟨z, hz⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      K hKdirected hKnonempty hKcompact hKclosed
  have hzK : ∀ s, z ∈ K s := Set.mem_iInter.mp hz
  have hbase : charbonnelVerticalBaseCoordinate z = y := by
    by_contra hne
    have hdistPos : 0 < dist (charbonnelVerticalBaseCoordinate z) y :=
      dist_pos.mpr hne
    let s : Radius :=
      ⟨min (dist (charbonnelVerticalBaseCoordinate z) y / 2)
          (w.radius / 2),
        lt_min (half_pos hdistPos) (half_pos w.radius_pos),
        min_le_right _ _⟩
    have hzBall := (hzK s).2.1
    have hle : dist (charbonnelVerticalBaseCoordinate z) y ≤ (s : ℝ) :=
      Metric.mem_closedBall.mp hzBall
    have hlt : (s : ℝ) < dist (charbonnelVerticalBaseCoordinate z) y :=
      (min_le_left _ _).trans_lt (half_lt_self hdistPos)
    exact (not_lt_of_ge hle) hlt
  have hlast : charbonnelVerticalLastCoordinate z = t := by
    have hlastMem := (hzK halfRadius).2.2
    change charbonnelVerticalLastCoordinate z ∈ ({t} : Set ℝ) at hlastMem
    simpa only [Set.mem_singleton_iff] using hlastMem
  change charbonnelAppendLastCoordinate y t ∈ S
  rw [← hbase, ← hlast]
  simpa only [charbonnelVerticalBaseCoordinate,
    charbonnelVerticalLastCoordinate,
    charbonnelAppendLastCoordinate_takeLeft_last] using
      (hzK halfRadius).1

/-- A finite limiting fibre has at most one point in every stable interval,
and hence at most as many points as there are stable intervals. -/
theorem
    CharbonnelStableLocalVerticalIntervalWitness.fiber_encard_le_of_finite
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    {y : RealEuclidean n} (hy : y ∈ w.innerBall)
    (hfinite : (charbonnelVerticalFiber S y).Finite) :
    (charbonnelVerticalFiber S y).encard ≤ (w.count : ℕ∞) := by
  classical
  let index : charbonnelVerticalFiber S y → Fin w.count := fun t ↦
    Classical.choose (w.fiber_subset_iUnion_intervals hy t.property)
  have hindexSpec (t : charbonnelVerticalFiber S y) :
      (t : ℝ) ∈ w.interval (index t) :=
    Classical.choose_spec (w.fiber_subset_iUnion_intervals hy t.property)
  have hindexInjective : Function.Injective index := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hIcc : Set.Icc (a : ℝ) (b : ℝ) ⊆
          charbonnelVerticalFiber S y :=
        w.Icc_subset_fiber_of_mem_interval hScompact hy
          a.property (hindexSpec a) b.property (by simpa [hab] using hindexSpec b)
      exact hfinite.not_infinite ((Set.Icc_infinite hlt).mono hIcc)
    · have hIcc : Set.Icc (b : ℝ) (a : ℝ) ⊆
          charbonnelVerticalFiber S y :=
        w.Icc_subset_fiber_of_mem_interval hScompact hy
          b.property (by simpa [hab] using hindexSpec b) a.property (hindexSpec a)
      exact hfinite.not_infinite ((Set.Icc_infinite hgt).mono hIcc)
  have hcard := ENat.card_le_card_of_injective hindexInjective
  simpa only [ENat.card_coe_set_eq, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin] using hcard

/-! ## The closed infinite-fibre exceptional base -/

/-- Once a stable inner ball avoids the closed infinite-fibre locus, the
section 5.7 cardinal bound is automatic. -/
noncomputable def
    charbonnelSection57StableClosureFiberBoundWitness_of_stable_off_infiniteFiberLocusClosure
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hcompact : IsCompact (closure S))
    (w : CharbonnelStableLocalVerticalIntervalWitness (closure S))
    (htrace : w.innerBall ⊆
      interior (charbonnelPositiveZeroTrace S))
    (hoff : w.innerBall ⊆
      (closure (charbonnelInfiniteVerticalFiberLocus (closure S)))ᶜ) :
    CharbonnelSection57StableClosureFiberBoundWitness S where
  stable := w
  innerBall_subset_traceInterior := htrace
  fiber_encard_le := by
    intro y hy
    apply w.fiber_encard_le_of_finite hcompact hy
    apply charbonnelVerticalFiber_finite_of_not_mem_infiniteLocus
    intro hyInfinite
    exact hoff hy (subset_closure hyInfinite)

/-- The remaining geometric input after the infinite-fibre bridge: stable
intervals can be localized inside any prescribed nonempty open part of the
hypothetical trace interior. -/
def CharbonnelSection57StableClosureOpenLocalization
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
    ∀ S : Set (RealEuclidean (n + 1)), S ∈ C (n + 1) →
      CharbonnelRelativelyClosedInPositiveLast S →
      Bornology.IsBounded S → interior S = ∅ →
      ∀ U : Set (RealEuclidean n), IsOpen U → U.Nonempty →
        U ⊆ interior (charbonnelPositiveZeroTrace S) →
        ∃ w : CharbonnelStableLocalVerticalIntervalWitness (closure S),
          w.innerBall ⊆ U

/-- Closure-interior regularity makes the closed infinite-fibre base
interiorless.  Stable localization into its open complement therefore
supplies the complete stable closure-fibre-bound reduction. -/
theorem
    charbonnelSection57StableClosureFiberBoundReduction_of_openLocalization
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    (hlocalize : CharbonnelSection57StableClosureOpenLocalization
      (charbonnelClosure S0)) :
    CharbonnelSection57StableClosureFiberBoundReduction
      (charbonnelClosure S0) := by
  intro n hn hPPrime S hSmem hrelative hbounded hSempty htrace
  let T : Set (RealEuclidean (n + 1)) := closure S
  let E : Set (RealEuclidean n) :=
    closure (charbonnelInfiniteVerticalFiberLocus T)
  have hTmem : T ∈ charbonnelClosure S0 (n + 1) :=
    charbonnelClosure_topologicalClosure hSmem
  have hTempty : interior T = ∅ :=
    hregularity (by omega) hSmem hSempty
  have hEempty : interior E = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hEnonempty
    have hTnonempty : (interior T).Nonempty :=
      charbonnelInfiniteVerticalFiberLocus_closure_interior_lift_of_ws5_and_regular
        hC hregularity hn isClosed_closure hTmem hEnonempty
    rw [hTempty] at hTnonempty
    exact hTnonempty.ne_empty rfl
  obtain ⟨x, ε, hε, hball⟩ :=
    exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
      isOpen_interior htrace isClosed_closure hEempty
  let U : Set (RealEuclidean n) := Metric.ball x ε
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUnonempty : U.Nonempty := ⟨x, Metric.mem_ball_self hε⟩
  have hUtrace : U ⊆ interior (charbonnelPositiveZeroTrace S) :=
    fun y hy ↦ (hball hy).1
  obtain ⟨w, hw⟩ := hlocalize hn hPPrime S hSmem hrelative
    hbounded hSempty U hUopen hUnonempty hUtrace
  refine ⟨
    charbonnelSection57StableClosureFiberBoundWitness_of_stable_off_infiniteFiberLocusClosure
      hbounded.isCompact_closure w (hw.trans hUtrace) ?_⟩
  intro y hy
  exact (hball (hw hy)).2

/-- Maxwell's meagre-selection premise supplies the closure-interior
regularity used by the bridge. -/
theorem
    charbonnelSection57StableClosureFiberBoundReduction_of_maxwellMeagreSelection_and_openLocalization
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure S0))
    (hlocalize : CharbonnelSection57StableClosureOpenLocalization
      (charbonnelClosure S0)) :
    CharbonnelSection57StableClosureFiberBoundReduction
      (charbonnelClosure S0) :=
  charbonnelSection57StableClosureFiberBoundReduction_of_openLocalization
    hC
    ((hasMaxwellMeagreClosureComponentSelection_iff_closureInteriorRegularity
      hC).mp hselection)
    hlocalize

/-- The localized stable-component statement now also yields the existing
bounded graph reduction. -/
theorem
    charbonnelSection57BoundedGraphReduction_of_openLocalization
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    (hlocalize : CharbonnelSection57StableClosureOpenLocalization
      (charbonnelClosure S0)) :
    CharbonnelSection57BoundedGraphReduction (charbonnelClosure S0) :=
  charbonnelSection57BoundedGraphReduction_of_stableClosureFiberBoundReduction
    (charbonnelSection57StableClosureFiberBoundReduction_of_openLocalization
      hC hregularity hlocalize)

end AbelFormalization
