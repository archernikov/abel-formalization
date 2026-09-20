import AbelFormalization.WilkieSection4FiberCardinalityLoci
import AbelFormalization.WilkieSection4CollisionLocus

/-!
# Wilkie Section 4: stability of finite fibre cardinality

The compactness paragraph on page 419 of Wilkie's paper proves that scalar
fibre cardinality cannot increase near a fixed base point once collisions and
escape through the boundary of the ambient band have been excluded.

Here this is isolated as a direct metric statement.  `MaxwellScalarFiberNoEscape`
assigns every point of a nearby fibre to a nearby point of the limiting fibre.
`MaxwellScalarFiberNoCollision` makes that assignment injective after shrinking
the base neighbourhood.  Consequently the extended cardinality of nearby
fibres is at most the cardinality of the limiting fibre.

It follows that Wilkie's locus `A_i` is relatively closed on every open region
where those two hypotheses hold.  Hence a region contained in `closure A_i`
and disjoint from `closure A_(i+1)` has exact fibre cardinality `i`.  This is
the source step needed before constructing the continuous ordered selectors.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Under no escape and no collision, scalar-fibre extended cardinality is
upper semicontinuous in the order-theoretic sense: after shrinking around a
base point, every nearby fibre injects into the limiting fibre. -/
theorem exists_local_encard_maxwellScalarFiber_le
    {p : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hescape : MaxwellScalarFiberNoEscape B R)
    (hcollision : MaxwellScalarFiberNoCollision B R)
    {x : RealEuclidean p} (hx : x ∈ B) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x' ∈ B, dist x' x < δ →
        (maxwellScalarFiber R x').encard ≤
          (maxwellScalarFiber R x).encard := by
  obtain ⟨rho, hrho, deltaCollision, hdeltaCollision, hseparated⟩ :=
    hcollision x hx
  obtain ⟨deltaEscape, hdeltaEscape, hmatched⟩ :=
    hescape x hx (rho / 3) (by positivity)
  refine ⟨min deltaCollision deltaEscape,
    lt_min hdeltaCollision hdeltaEscape, ?_⟩
  intro x' hx' hdist
  have hdistCollision : dist x' x < deltaCollision :=
    hdist.trans_le (min_le_left _ _)
  have hdistEscape : dist x' x < deltaEscape :=
    hdist.trans_le (min_le_right _ _)
  have hchoice : ∀ y : maxwellScalarFiber R x',
      ∃ z : maxwellScalarFiber R x, dist (y : ℝ) (z : ℝ) < rho / 3 := by
    intro y
    obtain ⟨z, hz, hdistYZ⟩ :=
      hmatched x' hx' hdistEscape y y.property
    exact ⟨⟨z, hz⟩, hdistYZ⟩
  choose assign hassign using hchoice
  have hassignInjective : Function.Injective assign := by
    intro y z hyz
    apply Subtype.ext
    by_contra hyzVal
    have hsep : rho ≤ dist (y : ℝ) (z : ℝ) :=
      hseparated x' hx' hdistCollision y y.property z z.property hyzVal
    have htriangle : dist (y : ℝ) (z : ℝ) ≤
        dist (y : ℝ) (assign y : ℝ) +
          dist (assign y : ℝ) (z : ℝ) :=
      dist_triangle _ _ _
    have hsecond : dist (assign y : ℝ) (z : ℝ) < rho / 3 := by
      rw [hyz, dist_comm]
      exact hassign z
    linarith [hassign y]
  have hcard := ENat.card_le_card_of_injective hassignInjective
  simpa only [ENat.card_coe_set_eq] using hcard

/-- On an open base region where escape and collision are excluded, every
Wilkie cardinality locus is closed relative to that region. -/
theorem inter_closure_wilkieSection4FiberCardinalityLocus_subset
    {p i : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBC : B ⊆ C)
    (hescape : MaxwellScalarFiberNoEscape B A)
    (hcollision : MaxwellScalarFiberNoCollision B A) :
    B ∩ closure (wilkieSection4FiberCardinalityLocus C A i) ⊆
      wilkieSection4FiberCardinalityLocus C A i := by
  rintro x ⟨hxB, hxClosure⟩
  obtain ⟨deltaCard, hdeltaCard, hcardUpper⟩ :=
    exists_local_encard_maxwellScalarFiber_le hescape hcollision hxB
  obtain ⟨deltaB, hdeltaB, hballB⟩ :=
    Metric.isOpen_iff.mp hBopen x hxB
  let delta := min deltaCard deltaB
  have hdelta : 0 < delta := lt_min hdeltaCard hdeltaB
  obtain ⟨x', hx'Locus, hdist⟩ :=
    (Metric.mem_closure_iff.mp hxClosure) delta hdelta
  have hx'B : x' ∈ B :=
    hballB (Metric.mem_ball.mpr
      (by simpa [dist_comm] using
        hdist.trans_le (min_le_right _ _)))
  have hnearUpper := hcardUpper x' hx'B
    (by simpa [dist_comm] using hdist.trans_le (min_le_left _ _))
  rw [mem_wilkieSection4FiberCardinalityLocus_iff_encard] at hx'Locus ⊢
  exact ⟨hBC hxB, hx'Locus.2.trans hnearUpper⟩

/-- If an open region lies in `closure A_i` and avoids `closure A_(i+1)`,
then every fibre over that region is finite and has exactly `i` points. -/
theorem exact_maxwellScalarFiber_cardinality_of_open_between_loci
    {p i : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBC : B ⊆ C)
    (hinside : B ⊆
      closure (wilkieSection4FiberCardinalityLocus C A i))
    (houtside : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A (i + 1))))
    (hescape : MaxwellScalarFiberNoEscape B A)
    (hcollision : MaxwellScalarFiberNoCollision B A) :
    ∀ x ∈ B,
      (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = i := by
  intro x hxB
  have hxCurrent :
      x ∈ wilkieSection4FiberCardinalityLocus C A i :=
    inter_closure_wilkieSection4FiberCardinalityLocus_subset
      hBopen hBC hescape hcollision ⟨hxB, hinside hxB⟩
  have hxNotNext :
      x ∉ wilkieSection4FiberCardinalityLocus C A (i + 1) := by
    intro hxNext
    exact Set.disjoint_left.mp houtside hxB (subset_closure hxNext)
  exact
    ((mem_wilkieSection4FiberCardinalityLocus_and_not_succ_iff
      C A x).mp ⟨hxCurrent, hxNotNext⟩).2

/-- Source-facing version in which the no-collision hypothesis is discharged
by avoiding Wilkie's closed gap-zero locus `H̃`. -/
theorem exact_maxwellScalarFiber_cardinality_of_open_between_loci_of_disjoint_collisionLocus
    {p i : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBC : B ⊆ C)
    (hinside : B ⊆
      closure (wilkieSection4FiberCardinalityLocus C A i))
    (houtside : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A (i + 1))))
    (hescape : MaxwellScalarFiberNoEscape B A)
    (hcollisionLocus : Disjoint B
      (wilkieSection4CollisionLocus C A)) :
    ∀ x ∈ B,
      (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = i :=
  exact_maxwellScalarFiber_cardinality_of_open_between_loci
    hBopen hBC hinside houtside hescape
      (maxwellScalarFiberNoCollision_of_disjoint_collisionLocus
        hBC hcollisionLocus)

/-- The complete full-dimensional selector-cylinder step over one open base
cell.  Compatibility with two consecutive closed cardinality loci gives exact
fibre size, avoidance of `H̃` gives no collision, and the ordered-tuple
incidences supply all selector-graph membership obligations. -/
noncomputable def
    charbonnelFiniteSelectorRelativeCellCover_of_section4_loci
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p i : ℕ} (hp : 0 < p)
    {C B : Set (RealEuclidean p)}
    (hBshape : CharbonnelCellShape p B)
    (hBopen : IsOpen B)
    (hBmem : B ∈ charbonnelClosure S p)
    (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hinside : B ⊆
      closure (wilkieSection4FiberCardinalityLocus C A i))
    (houtside : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A (i + 1))))
    (hescape : MaxwellScalarFiberNoEscape B A)
    (hcollisionLocus : Disjoint B
      (wilkieSection4CollisionLocus C A)) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell B) A := by
  have hfiber : ∀ x ∈ B,
      (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = i :=
    exact_maxwellScalarFiber_cardinality_of_open_between_loci_of_disjoint_collisionLocus
      hBopen hBC hinside houtside hescape hcollisionLocus
  have hcollision : MaxwellScalarFiberNoCollision B A :=
    maxwellScalarFiberNoCollision_of_disjoint_collisionLocus
      hBC hcollisionLocus
  exact charbonnelFiniteSelectorRelativeCellCover_of_noEscape_noCollision
    hC hp hBshape hBmem hAmem hfiber hescape hcollision

/-- WS5 and the maintained Theorem 2.1 package supply Wilkie's finite cutoff:
for some positive `N`, the closure of `A_N` has empty interior.  The Fubini
argument itself is proved in `MaxwellLocalFiberCardinality`; this theorem only
identifies its locus with Wilkie's source notation and applies the closure
part of Theorem 2.1. -/
theorem exists_wilkieSection4_cardinalityCutoff
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAempty : interior A = ∅) :
    ∃ N : ℕ, 0 < N ∧
      interior
        (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅ := by
  obtain ⟨K, _hcomponents, hKempty⟩ :=
    exists_component_bound_and_interior_atLeast_succ_eq_empty
      hC h21 hp (B := C) hAmem hAempty
  let N := K + 1
  have hNmem : wilkieSection4FiberCardinalityLocus C A N ∈
      charbonnelClosure S p :=
    wilkieSection4FiberCardinalityLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hCmem hAmem
  have hNempty : interior
      (wilkieSection4FiberCardinalityLocus C A N) = ∅ := by
    simpa [N, wilkieSection4FiberCardinalityLocus_eq_maxwell] using hKempty
  have hdata := h21 hp hNmem
  exact ⟨N, by simp [N], hdata.2.1.mp (hdata.1.mp hNempty)⟩

/-- Wilkie's maximal-cardinality argument without making a separate maximal
choice.  Pick one fibre, call its cardinality `r`, and use simultaneous
compatibility with all `closure A_j`.  Relative closedness of the loci forces
the whole open region to lie in `closure A_r` and to avoid
`closure A_(r+1)`, so every fibre has cardinality `r`. -/
theorem exists_exact_maxwellScalarFiber_cardinality_of_open_compatible_loci
    {p N : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1}
    (hN : 0 < N)
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty) (hBC : B ⊆ C)
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hcompatible : ∀ j, j ≤ N →
      B ⊆ closure (wilkieSection4FiberCardinalityLocus C A j) ∨
        Disjoint B
          (closure (wilkieSection4FiberCardinalityLocus C A j)))
    (hescape : MaxwellScalarFiberNoEscape B A)
    (hcollision : MaxwellScalarFiberNoCollision B A) :
    ∃ r : ℕ, r < N ∧
      ∀ x ∈ B,
        (maxwellScalarFiber A x).Finite ∧
          (maxwellScalarFiber A x).ncard = r := by
  have hNdisjoint : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A N)) := by
    rcases hcompatible N le_rfl with hsubset | hdisjoint
    · have hBInterior : B ⊆ interior
          (closure (wilkieSection4FiberCardinalityLocus C A N)) :=
        interior_maximal hsubset hBopen
      obtain ⟨x, hxB⟩ := hBnonempty
      have : x ∈ (∅ : Set (RealEuclidean p)) := by
        rw [← hNempty]
        exact hBInterior hxB
      exact this.elim
    · exact hdisjoint
  obtain ⟨x₀, hx₀B⟩ := hBnonempty
  have hx₀NotN :
      x₀ ∉ wilkieSection4FiberCardinalityLocus C A N := by
    intro hxN
    exact Set.disjoint_left.mp hNdisjoint hx₀B (subset_closure hxN)
  have hnotNLe : ¬ (N : ℕ∞) ≤ (maxwellScalarFiber A x₀).encard := by
    intro hNLe
    exact hx₀NotN
      ((mem_wilkieSection4FiberCardinalityLocus_iff_encard C A x₀).mpr
        ⟨hBC hx₀B, hNLe⟩)
  let k := N - 1
  have hNk : N = k + 1 := by
    dsimp [k]
    omega
  have hencardUpper : (maxwellScalarFiber A x₀).encard ≤ (k : ℕ∞) := by
    by_contra hnotUpper
    have hlt : (k : ℕ∞) < (maxwellScalarFiber A x₀).encard :=
      lt_of_not_ge hnotUpper
    apply hnotNLe
    rw [hNk]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.natCast_add_one_le_iff.mpr hlt)
  have hx₀Finite : (maxwellScalarFiber A x₀).Finite :=
    (Set.encard_le_coe_iff_finite_ncard_le.mp hencardUpper).1
  let r := (maxwellScalarFiber A x₀).ncard
  have hrk : r ≤ k := by
    exact (Set.encard_le_coe_iff_finite_ncard_le.mp hencardUpper).2
  have hrN : r < N := by
    rw [hNk]
    omega
  have hencardEq : (maxwellScalarFiber A x₀).encard = (r : ℕ∞) := by
    rw [← hx₀Finite.cast_ncard_eq]
  have hx₀Current :
      x₀ ∈ wilkieSection4FiberCardinalityLocus C A r := by
    rw [mem_wilkieSection4FiberCardinalityLocus_iff_encard]
    exact ⟨hBC hx₀B, hencardEq.ge⟩
  have hx₀NotNext :
      x₀ ∉ wilkieSection4FiberCardinalityLocus C A (r + 1) := by
    intro hxNext
    have hle :=
      (mem_wilkieSection4FiberCardinalityLocus_iff_encard C A x₀).mp
        hxNext |>.2
    rw [hencardEq] at hle
    have : r + 1 ≤ r := ENat.natCast_le_natCast.mp hle
    omega
  have hinside : B ⊆
      closure (wilkieSection4FiberCardinalityLocus C A r) := by
    rcases hcompatible r hrN.le with hsubset | hdisjoint
    · exact hsubset
    · exact False.elim
        (Set.disjoint_left.mp hdisjoint hx₀B (subset_closure hx₀Current))
  have houtside : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A (r + 1))) := by
    rcases hcompatible (r + 1) hrN with hsubset | hdisjoint
    · have hx₀Closure := hsubset hx₀B
      have hx₀Next :
          x₀ ∈ wilkieSection4FiberCardinalityLocus C A (r + 1) :=
        inter_closure_wilkieSection4FiberCardinalityLocus_subset
          hBopen hBC hescape hcollision ⟨hx₀B, hx₀Closure⟩
      exact (hx₀NotNext hx₀Next).elim
    · exact hdisjoint
  exact ⟨r, hrN,
    exact_maxwellScalarFiber_cardinality_of_open_between_loci
      hBopen hBC hinside houtside hescape hcollision⟩

/-- Complete one-open-cell version of Wilkie's simultaneous-cardinality
refinement.  A finite cutoff locus with empty interior and compatibility with
all its predecessors determine the exact fibre size automatically; avoiding
the collision locus supplies the remaining separation premise. -/
noncomputable def
    charbonnelFiniteSelectorRelativeCellCover_of_section4_compatible_loci
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {C B : Set (RealEuclidean p)}
    (hBshape : CharbonnelCellShape p B)
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p)
    (hBC : B ⊆ C)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hcompatible : ∀ j, j ≤ N →
      B ⊆ closure (wilkieSection4FiberCardinalityLocus C A j) ∨
        Disjoint B
          (closure (wilkieSection4FiberCardinalityLocus C A j)))
    (hescape : MaxwellScalarFiberNoEscape B A)
    (hcollisionLocus : Disjoint B
      (wilkieSection4CollisionLocus C A)) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell B) A := by
  have hcollision : MaxwellScalarFiberNoCollision B A :=
    maxwellScalarFiberNoCollision_of_disjoint_collisionLocus
      hBC hcollisionLocus
  have hexact :=
    exists_exact_maxwellScalarFiber_cardinality_of_open_compatible_loci
      hN hBopen hBnonempty hBC hNempty hcompatible hescape hcollision
  let data : {r : ℕ // r < N ∧
      ∀ x ∈ B, (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = r} :=
    Classical.choice (show Nonempty {r : ℕ // r < N ∧
        ∀ x ∈ B, (maxwellScalarFiber A x).Finite ∧
          (maxwellScalarFiber A x).ncard = r} from by
      rcases hexact with ⟨r, hrN, hfiber⟩
      exact ⟨⟨r, hrN, hfiber⟩⟩)
  exact charbonnelFiniteSelectorRelativeCellCover_of_noEscape_noCollision
    hC hp hBshape hBmem hAmem data.property.2 hescape hcollision

end AbelFormalization
