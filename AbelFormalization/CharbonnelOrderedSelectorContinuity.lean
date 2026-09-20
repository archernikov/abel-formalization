import AbelFormalization.CharbonnelOrderedSelectorMembership
import AbelFormalization.MaxwellScalarFiberExtrema
import AbelFormalization.ReciprocalConstraintGraph

/-!
# Continuous ordered selectors for finite scalar fibres

This module supplies the analytic input used by the open-cell branch of
Wilkie's section 4 argument.  A finite scalar fibre has a canonical increasing
enumeration.  If nearby fibre points cannot escape from the limiting fibre and
distinct nearby points stay uniformly separated, those enumerations are
continuous.

The two local hypotheses are deliberately separated.  `MaxwellScalarFiberNoEscape`
is upper semicontinuity of the finite-valued relation; it is the exact local
consequence of closedness together with exclusion of escape through the two
band endpoints.  `MaxwellScalarFiberNoCollision` is the exact consequence of
excluding zero from the closure of the positive pairwise-difference relation.
Neither hypothesis contains a selector or assumes its continuity.

For convenience, the final section proves the no-escape hypothesis directly
when the relation is globally closed and lies in a continuous open band.  In
that common special case endpoint escape is already impossible, so no separate
endpoint premise is needed.
-/

noncomputable section

open Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Canonical increasing enumeration -/

/-- A strictly increasing enumeration of the whole scalar fibre. -/
def MaxwellOrderedScalarFiberEnumerationWitness {p r : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p)
    (values : Fin r → ℝ) : Prop :=
  StrictMono values ∧ Set.range values = maxwellScalarFiber R x

/-- Every finite scalar fibre of cardinality `r` has an increasing
enumeration. -/
theorem exists_maxwellOrderedScalarFiberEnumerationWitness
    {p r : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = r) :
    ∃ values : Fin r → ℝ,
      MaxwellOrderedScalarFiberEnumerationWitness R x values := by
  let s : Finset ℝ := hfinite.toFinset
  have hsCard : s.card = r := by
    change hfinite.toFinset.card = r
    rw [← Set.ncard_eq_toFinset_card (maxwellScalarFiber R x) hfinite]
    exact hcard
  let values : Fin r → ℝ := s.orderEmbOfFin hsCard
  refine ⟨values, (s.orderEmbOfFin hsCard).strictMono, ?_⟩
  rw [Finset.range_orderEmbOfFin]
  ext y
  simp [s]

/-- The canonical increasing enumeration, totalized by the zero function away
from the exact finite-cardinality locus. -/
noncomputable def maxwellOrderedScalarFiberEnumeration {p r : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) : Fin r → ℝ := by
  classical
  exact if h : ∃ values : Fin r → ℝ,
      MaxwellOrderedScalarFiberEnumerationWitness R x values then
    Classical.choose h
  else fun _ ↦ 0

theorem maxwellOrderedScalarFiberEnumeration_spec
    {p r : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = r) :
    MaxwellOrderedScalarFiberEnumerationWitness (r := r) R x
      (maxwellOrderedScalarFiberEnumeration (r := r) R x) := by
  have h := exists_maxwellOrderedScalarFiberEnumerationWitness hfinite hcard
  simpa [maxwellOrderedScalarFiberEnumeration, h] using
    (Classical.choose_spec h)

theorem maxwellOrderedScalarFiberEnumeration_mem
    {p r : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = r)
    (i : Fin r) :
    maxwellOrderedScalarFiberEnumeration R x i ∈ maxwellScalarFiber R x := by
  have hspec := maxwellOrderedScalarFiberEnumeration_spec hfinite hcard
  rw [← hspec.2]
  exact ⟨i, rfl⟩

theorem maxwellOrderedScalarFiberEnumeration_range
    {p r : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = r) :
    Set.range (maxwellOrderedScalarFiberEnumeration (r := r) R x) =
      maxwellScalarFiber R x :=
  (maxwellOrderedScalarFiberEnumeration_spec hfinite hcard).2

theorem maxwellOrderedScalarFiberEnumeration_strictMono
    {p r : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = r) :
    StrictMono (maxwellOrderedScalarFiberEnumeration (r := r) R x) :=
  (maxwellOrderedScalarFiberEnumeration_spec hfinite hcard).1

/-- The first canonical selector is the minimum selector already used in the
Maxwell weak-selection development. -/
theorem maxwellOrderedScalarFiberEnumeration_zero_eq_minimum
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellOrderedScalarFiberEnumeration (r := k + 1) R x 0 =
      maxwellOrderedScalarValue R k x := by
  let values : Fin (k + 1) → ℝ :=
    maxwellOrderedScalarFiberEnumeration R x
  have hmono : StrictMono values :=
    maxwellOrderedScalarFiberEnumeration_strictMono hfinite hcard
  have hminimumMem := maxwellOrderedScalarValue_mem hfinite hcard
  rw [← maxwellOrderedScalarFiberEnumeration_range hfinite hcard] at hminimumMem
  obtain ⟨j, hj⟩ := hminimumMem
  have henumLe : values 0 ≤ maxwellOrderedScalarValue R k x := by
    rw [← hj]
    exact hmono.monotone (Fin.zero_le j)
  have hminimumLe : maxwellOrderedScalarValue R k x ≤ values 0 :=
    maxwellOrderedScalarValue_le_of_mem hfinite hcard
      (maxwellOrderedScalarFiberEnumeration_mem hfinite hcard 0)
  exact le_antisymm henumLe hminimumLe

/-- The last canonical selector is the reflected maximum selector already
used in the Maxwell discontinuity argument. -/
theorem maxwellOrderedScalarFiberEnumeration_last_eq_maximum
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1) :
    maxwellOrderedScalarFiberEnumeration (r := k + 1) R x (Fin.last k) =
      maxwellOrderedScalarMaximumValue R k x := by
  let values : Fin (k + 1) → ℝ :=
    maxwellOrderedScalarFiberEnumeration R x
  have hmono : StrictMono values :=
    maxwellOrderedScalarFiberEnumeration_strictMono hfinite hcard
  have hmaximumMem := maxwellOrderedScalarMaximumValue_mem hfinite hcard
  rw [← maxwellOrderedScalarFiberEnumeration_range hfinite hcard] at hmaximumMem
  obtain ⟨j, hj⟩ := hmaximumMem
  have hmaximumLe : maxwellOrderedScalarMaximumValue R k x ≤
      values (Fin.last k) := by
    rw [← hj]
    exact hmono.monotone (Fin.le_last j)
  have henumLe : values (Fin.last k) ≤
      maxwellOrderedScalarMaximumValue R k x :=
    le_maxwellOrderedScalarMaximumValue_of_mem hfinite hcard
      (maxwellOrderedScalarFiberEnumeration_mem hfinite hcard (Fin.last k))
  exact le_antisymm henumLe hmaximumLe

/-! ## The two local geometric hypotheses -/

/-- No nearby fibre point can escape from all neighbourhoods of the limiting
fibre.  This is upper semicontinuity of the set-valued scalar relation, written
in the metric form used below. -/
def MaxwellScalarFiberNoEscape {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) : Prop :=
  ∀ x ∈ B, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x' ∈ B, dist x' x < δ →
        ∀ y ∈ maxwellScalarFiber R x',
          ∃ z ∈ maxwellScalarFiber R x, dist y z < ε

/-- Distinct points in nearby fibres stay a uniformly positive distance apart.
This is precisely the local no-collision condition needed to retain
multiplicity when the fibres are viewed as sets. -/
def MaxwellScalarFiberNoCollision {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) : Prop :=
  ∀ x ∈ B,
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ x' ∈ B, dist x' x < δ →
          ∀ y ∈ maxwellScalarFiber R x',
            ∀ z ∈ maxwellScalarFiber R x', y ≠ z →
              ρ ≤ dist y z

/-- No new scalar point appears in a vertical fibre after taking closure.
For a relation closed only relative to an open band, this is exactly the
combined effect of relative closedness and excluding escape through either
band endpoint. -/
def MaxwellScalarFiberClosureStableOver {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) : Prop :=
  ∀ x ∈ B, ∀ y : ℝ,
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ closure R →
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ R

/-! ## A finite ordered matching lemma -/

/-- If two increasing `r`-tuples are close after some reindexing and both
tuples are separated at a scale larger than twice the error, then the
reindexing is the identity. -/
theorem dist_ordered_eq_index_of_separated_matching
    {r : ℕ} {a b : Fin r → ℝ} {eta rho : ℝ}
    (ha : StrictMono a) (hb : StrictMono b)
    (hscale : 2 * eta < rho)
    (hasep : ∀ i j, i ≠ j → rho ≤ dist (a i) (a j))
    (hbsep : ∀ i j, i ≠ j → rho ≤ dist (b i) (b j))
    (hmatch : ∀ j, ∃ i, dist (b j) (a i) < eta) :
    ∀ i, dist (b i) (a i) < eta := by
  classical
  choose k hk using hmatch
  have hkinjective : Function.Injective k := by
    intro i j hij
    by_contra hne
    have hsep := hbsep i j hne
    have htri : dist (b i) (b j) ≤
        dist (b i) (a (k i)) + dist (a (k i)) (b j) :=
      dist_triangle _ _ _
    have hkj : dist (a (k i)) (b j) < eta := by
      rw [dist_comm]
      simpa [hij] using hk j
    linarith [hk i]
  have hkmono : StrictMono k := by
    intro i j hij
    have hkne : k i ≠ k j := hkinjective.ne hij.ne
    rcases lt_or_gt_of_ne hkne with hlt | hgt
    · exact hlt
    · exfalso
      have hsep := hasep (k j) (k i) hgt.ne
      have hak : a (k j) < a (k i) := ha hgt
      have hbi : a (k i) - eta < b i := by
        have hki := hk i
        rw [Real.dist_eq] at hki
        have := (abs_lt.mp hki).1
        linarith
      have hbj : b j < a (k j) + eta := by
        have hkj := hk j
        rw [Real.dist_eq] at hkj
        have := (abs_lt.mp hkj).2
        linarith
      have hdist : dist (a (k j)) (a (k i)) =
          a (k i) - a (k j) := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hak.le)]
        ring
      rw [hdist] at hsep
      exact (not_lt_of_ge (hb.monotone hij.le)) (by linarith)
  let e : Fin r ↪o Fin r := OrderEmbedding.ofStrictMono k hkmono
  have heq : e = OrderEmbedding.id (Fin r) := by
    let hcard : (Finset.univ : Finset (Fin r)).card = r := by simp
    calc
      e = (Finset.univ : Finset (Fin r)).orderEmbOfFin hcard :=
        Finset.orderEmbOfFin_unique' hcard (fun i ↦ Finset.mem_univ (e i))
      _ = OrderEmbedding.id (Fin r) :=
        (Finset.orderEmbOfFin_unique' hcard
          (f := OrderEmbedding.id (Fin r))
          (fun i ↦ Finset.mem_univ i)).symm
  intro i
  have hki : k i = i := by
    have := DFunLike.congr_fun heq i
    exact this
  simpa [hki] using hk i

/-! ## Continuity of the canonical selectors -/

/-- Exact finite fibres, no escape, and no collision make every coordinate of
the canonical increasing enumeration continuous on the base. -/
theorem continuousOn_maxwellOrderedScalarFiberEnumeration
    {p r : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (hescape : MaxwellScalarFiberNoEscape B R)
    (hcollision : MaxwellScalarFiberNoCollision B R) :
    ∀ i : Fin r,
      ContinuousOn (fun x ↦ maxwellOrderedScalarFiberEnumeration R x i) B := by
  intro i x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨rho, hrho, deltaCollision, hdeltaCollision,
      hseparated⟩ := hcollision x hx
  let eta : ℝ := min (ε / 2) (rho / 4)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaEpsilon : eta < ε := by
    calc
      eta ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  have hscale : 2 * eta < rho := by
    calc
      2 * eta ≤ 2 * (rho / 4) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ < rho := by linarith
  obtain ⟨deltaEscape, hdeltaEscape, htrapped⟩ :=
    hescape x hx eta heta
  refine ⟨min deltaCollision deltaEscape,
    lt_min hdeltaCollision hdeltaEscape, ?_⟩
  intro x' hx' hdist
  have hdistCollision : dist x' x < deltaCollision :=
    hdist.trans_le (min_le_left _ _)
  have hdistEscape : dist x' x < deltaEscape :=
    hdist.trans_le (min_le_right _ _)
  let a : Fin r → ℝ := maxwellOrderedScalarFiberEnumeration R x
  let b : Fin r → ℝ := maxwellOrderedScalarFiberEnumeration R x'
  have ha : StrictMono a :=
    maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber x hx).1 (hfiber x hx).2
  have hb : StrictMono b :=
    maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber x' hx').1 (hfiber x' hx').2
  have hasep : ∀ j k, j ≠ k → rho ≤ dist (a j) (a k) := by
    intro j k hjk
    exact hseparated x hx (by simpa using hdeltaCollision) (a j)
      (maxwellOrderedScalarFiberEnumeration_mem
        (hfiber x hx).1 (hfiber x hx).2 j)
      (a k)
      (maxwellOrderedScalarFiberEnumeration_mem
        (hfiber x hx).1 (hfiber x hx).2 k)
      (ha.injective.ne hjk)
  have hbsep : ∀ j k, j ≠ k → rho ≤ dist (b j) (b k) := by
    intro j k hjk
    exact hseparated x' hx' hdistCollision (b j)
      (maxwellOrderedScalarFiberEnumeration_mem
        (hfiber x' hx').1 (hfiber x' hx').2 j)
      (b k)
      (maxwellOrderedScalarFiberEnumeration_mem
        (hfiber x' hx').1 (hfiber x' hx').2 k)
      (hb.injective.ne hjk)
  have hmatch : ∀ j, ∃ k, dist (b j) (a k) < eta := by
    intro j
    obtain ⟨z, hz, hzdist⟩ := htrapped x' hx' hdistEscape (b j)
      (maxwellOrderedScalarFiberEnumeration_mem
        (hfiber x' hx').1 (hfiber x' hx').2 j)
    rw [← maxwellOrderedScalarFiberEnumeration_range
      (hfiber x hx).1 (hfiber x hx).2] at hz
    obtain ⟨k, rfl⟩ := hz
    exact ⟨k, hzdist⟩
  have hindex := dist_ordered_eq_index_of_separated_matching
    ha hb hscale hasep hbsep hmatch i
  change dist (b i) (a i) < ε
  exact hindex.trans hetaEpsilon

/-- Package the ordered selectors in the form consumed by
`charbonnelOrderedSelectorRelativeCellCover`. -/
theorem exists_continuous_strictOrdered_exactFiber_selectors
    {p r : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (hescape : MaxwellScalarFiberNoEscape B R)
    (hcollision : MaxwellScalarFiberNoCollision B R) :
    ∃ f : Fin r → RealEuclidean p → ℝ,
      (∀ i, ContinuousOn (f i) B) ∧
      (∀ x ∈ B, StrictMono (fun i ↦ f i x)) ∧
      (∀ x ∈ B, Set.range (fun i ↦ f i x) =
        maxwellScalarFiber R x) := by
  let f : Fin r → RealEuclidean p → ℝ :=
    fun i x ↦ maxwellOrderedScalarFiberEnumeration R x i
  refine ⟨f, continuousOn_maxwellOrderedScalarFiberEnumeration
      hfiber hescape hcollision, ?_, ?_⟩
  · intro x hx
    exact maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber x hx).1 (hfiber x hx).2
  · intro x hx
    exact maxwellOrderedScalarFiberEnumeration_range
      (hfiber x hx).1 (hfiber x hx).2

/-- Flat-coordinate form of the exact-fibre statement.  This is the premise
expected by the ordered-selector cell constructor. -/
theorem mem_iff_exists_maxwellOrderedScalarFiberEnumeration
    {p r : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (z : RealEuclidean (p + 1))
    (hzBase : realEuclideanTakeLeft z ∈ B) :
    z ∈ R ↔
      ∃ i : Fin r, realEuclideanTakeRight z 0 =
        maxwellOrderedScalarFiberEnumeration R
          (realEuclideanTakeLeft z) i := by
  have hrightConst :
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) =
        realEuclideanTakeRight z := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  have hcanonical : realEuclideanAppend (realEuclideanTakeLeft z)
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) = z := by
    rw [hrightConst, realEuclideanAppend_takeLeft_takeRight]
  let x := realEuclideanTakeLeft z
  have hrange := maxwellOrderedScalarFiberEnumeration_range
    (hfiber x hzBase).1 (hfiber x hzBase).2
  constructor
  · intro hz
    have hy : realEuclideanTakeRight z 0 ∈ maxwellScalarFiber R x := by
      change realEuclideanAppend x
        (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) ∈ R
      simpa [x, hcanonical] using hz
    rw [← hrange] at hy
    obtain ⟨i, hi⟩ := hy
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩
    have hy := maxwellOrderedScalarFiberEnumeration_mem
      (hfiber x hzBase).1 (hfiber x hzBase).2 i
    change realEuclideanAppend x
      (fun _ : Fin 1 ↦ maxwellOrderedScalarFiberEnumeration R x i) ∈ R at hy
    rw [← hi] at hy
    simpa [x, hcanonical] using hy

/-- The no-escape/no-collision theorem plugged directly into the existing
graph/band/ray cylinder constructor. -/
noncomputable def charbonnelOrderedSelectorRelativeCellCover_of_noEscape_noCollision
    {C : EuclideanSetFamily} {p r : ℕ} (hp : 0 < p)
    {base : Set (RealEuclidean p)}
    (hbase : CharbonnelCellShape p base)
    {R : MaxwellRelation p 1} (hr : 0 < r)
    (hfiber : ∀ x ∈ base,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (hescape : MaxwellScalarFiberNoEscape base R)
    (hcollision : MaxwellScalarFiberNoCollision base R)
    (hmem : ∀ region,
      charbonnelOrderedSelectorRegionCarrier base
        (fun i x ↦ maxwellOrderedScalarFiberEnumeration R x i)
        hr region ∈ C (p + 1)) :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell base) R := by
  apply charbonnelOrderedSelectorRelativeCellCover hp hbase
    (fun i x ↦ maxwellOrderedScalarFiberEnumeration R x i) hr
  · exact continuousOn_maxwellOrderedScalarFiberEnumeration
      hfiber hescape hcollision
  · intro x hx
    exact maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber x hx).1 (hfiber x hx).2
  · intro z hz
    exact mem_iff_exists_maxwellOrderedScalarFiberEnumeration hfiber z hz
  · exact hmem

/-- Membership-complete local cylinder theorem.  Once the canonical selector
graphs belong to the Charbonnel closure, WS1--WS4 construct every intervening
band and outer ray automatically. -/
noncomputable def
    charbonnelFiniteSelectorRelativeCellCover_of_noEscape_noCollision_graph_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p r : ℕ} (hp : 0 < p)
    {base : Set (RealEuclidean p)}
    (hbaseShape : CharbonnelCellShape p base)
    (hbaseMem : base ∈ charbonnelClosure S p)
    {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ base,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (hescape : MaxwellScalarFiberNoEscape base R)
    (hcollision : MaxwellScalarFiberNoCollision base R)
    (hgraph : ∀ i : Fin r,
      charbonnelRestrictedGraph base
        (fun x ↦ maxwellOrderedScalarFiberEnumeration R x i) ∈
          charbonnelClosure S (p + 1)) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell base) R := by
  apply charbonnelFiniteSelectorRelativeCellCover_of_graph_mem hC hp
    hbaseShape hbaseMem
    (fun i x ↦ maxwellOrderedScalarFiberEnumeration R x i)
  · exact continuousOn_maxwellOrderedScalarFiberEnumeration
      hfiber hescape hcollision
  · intro x hx
    exact maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber x hx).1 (hfiber x hx).2
  · intro z hz
    exact mem_iff_exists_maxwellOrderedScalarFiberEnumeration hfiber z hz
  · exact hgraph

/-- Global mixed-cardinality form over a finite recursive base-cell cover.
Continuity, ordering, exact-fibre syntax, empty cylinders, bands, and rays are
all constructed internally; callers retain only the lower-dimensional fibre
stratification and canonical selector-graph membership. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.finiteFiberRelationCylinderCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) B)
    (A : MaxwellRelation p 1)
    (r : Fin baseCover.count → ℕ)
    (hfiber : ∀ i x, x ∈ (baseCover.cell i).carrier →
      (maxwellScalarFiber A x).Finite ∧
      (maxwellScalarFiber A x).ncard = r i)
    (hescape : ∀ i, MaxwellScalarFiberNoEscape
      (baseCover.cell i).carrier A)
    (hcollision : ∀ i, MaxwellScalarFiberNoCollision
      (baseCover.cell i).carrier A)
    (hgraph : ∀ i (j : Fin (r i)),
      charbonnelRestrictedGraph (baseCover.cell i).carrier
        (fun x ↦ maxwellOrderedScalarFiberEnumeration
          (r := r i) A x j) ∈
          charbonnelClosure S (p + 1)) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  let f : ∀ i, Fin (r i) → RealEuclidean p → ℝ :=
    fun i (j : Fin (r i)) x ↦
      maxwellOrderedScalarFiberEnumeration (r := r i) A x j
  apply baseCover.finiteSelectorCylinderCover_of_graph_mem hC hp r f
  · intro i j
    exact continuousOn_maxwellOrderedScalarFiberEnumeration
      (hfiber i) (hescape i) (hcollision i) j
  · intro i x hx
    exact maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber i x hx).1 (hfiber i x hx).2
  · intro i z hz
    exact mem_iff_exists_maxwellOrderedScalarFiberEnumeration
      (hfiber i) z hz
  · exact hgraph

/-! ## Closed relations in continuous bands have no escaping fibre points -/

/-- A relation contained over `B` in a continuous open band has
upper-semicontinuous scalar fibres as soon as closure creates no new vertical
points over `B`.  The latter is precisely the relative-closedness plus
no-endpoint-escape input in Wilkie's open-cell argument. -/
theorem maxwellScalarFiberNoEscape_of_continuousBand_of_closureStable
    {p : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {lower upper : RealEuclidean p → ℝ}
    (hclosureStable : MaxwellScalarFiberClosureStableOver B R)
    (hlower : ContinuousOn lower B)
    (hupper : ContinuousOn upper B)
    (hband : ∀ x ∈ B, ∀ y ∈ maxwellScalarFiber R x,
      lower x < y ∧ y < upper x) :
    MaxwellScalarFiberNoEscape B R := by
  intro x hx ε hε
  obtain ⟨deltaLower, hdeltaLower, hlowerControl⟩ :=
    (Metric.continuousWithinAt_iff.mp (hlower x hx)) 1 (by norm_num)
  obtain ⟨deltaUpper, hdeltaUpper, hupperControl⟩ :=
    (Metric.continuousWithinAt_iff.mp (hupper x hx)) 1 (by norm_num)
  let V : Set ℝ := ⋃ z : maxwellScalarFiber R x, Metric.ball (z : ℝ) ε
  have hVopen : IsOpen V := isOpen_iUnion fun z ↦ Metric.isOpen_ball
  let E := realEuclideanAppendScalarContinuousLinearEquiv p
  let Q : Set (RealEuclidean p × ℝ) :=
    Metric.closedBall x 1 ×ˢ Set.Icc (lower x - 1) (upper x + 1)
  let T : Set (RealEuclidean p × ℝ) := E ⁻¹' closure R
  let W : Set (RealEuclidean p × ℝ) := Prod.snd ⁻¹' Vᶜ
  let K : Set (RealEuclidean p × ℝ) := Q ∩ T ∩ W
  have hQcompact : IsCompact Q :=
    (ProperSpace.isCompact_closedBall x 1).prod
      (isCompact_Icc : IsCompact (Set.Icc (lower x - 1) (upper x + 1)))
  have hTclosed : IsClosed T := isClosed_closure.preimage E.continuous
  have hWclosed : IsClosed W :=
    hVopen.isClosed_compl.preimage continuous_snd
  have hKcompact : IsCompact K :=
    (hQcompact.inter_right hTclosed).inter_right hWclosed
  let P : Set (RealEuclidean p) := Prod.fst '' K
  have hPclosed : IsClosed P :=
    (hKcompact.image continuous_fst).isClosed
  have hxnotP : x ∉ P := by
    rintro ⟨q, hqK, hqx⟩
    have hqT : q ∈ T := hqK.1.2
    have hqW : q ∈ W := hqK.2
    have hqyClosure :
        realEuclideanAppend x (fun _ : Fin 1 ↦ q.2) ∈ closure R := by
      have hEq : q.1 = x := hqx
      change E q ∈ closure R at hqT
      simpa [E, realEuclideanAppendScalar, hEq] using hqT
    have hqyFiber : q.2 ∈ maxwellScalarFiber R x :=
      hclosureStable x hx q.2 hqyClosure
    have hqyV : q.2 ∈ V := by
      exact Set.mem_iUnion.mpr
        ⟨⟨q.2, hqyFiber⟩, Metric.mem_ball_self hε⟩
    exact hqW hqyV
  have hPcomplNhd : Pᶜ ∈ nhds x :=
    hPclosed.isOpen_compl.mem_nhds hxnotP
  obtain ⟨deltaP, hdeltaP, hballP⟩ :=
    Metric.mem_nhds_iff.mp hPcomplNhd
  refine ⟨min (min (min 1 deltaLower) deltaUpper) deltaP,
    lt_min (lt_min (lt_min (by norm_num) hdeltaLower) hdeltaUpper) hdeltaP,
    ?_⟩
  intro x' hx' hxx' y hy
  have hxOne : dist x' x < 1 :=
    hxx'.trans_le (min_le_left _ _ |>.trans (min_le_left _ _)
      |>.trans (min_le_left _ _))
  have hxLower : dist x' x < deltaLower :=
    hxx'.trans_le (min_le_left _ _ |>.trans (min_le_left _ _)
      |>.trans (min_le_right _ _))
  have hxUpper : dist x' x < deltaUpper :=
    hxx'.trans_le (min_le_left _ _ |>.trans (min_le_right _ _))
  have hxP : dist x' x < deltaP :=
    hxx'.trans_le (min_le_right _ _)
  by_contra hno
  push Not at hno
  have hlowerDist := hlowerControl hx' hxLower
  have hupperDist := hupperControl hx' hxUpper
  have hyBand := hband x' hx' y hy
  have hyBounds : y ∈ Set.Icc (lower x - 1) (upper x + 1) := by
    rw [Real.dist_eq] at hlowerDist hupperDist
    constructor
    · have := (abs_lt.mp hlowerDist).1
      linarith
    · have := (abs_lt.mp hupperDist).2
      linarith
  have hpairK : (x', y) ∈ K := by
    refine ⟨⟨⟨Metric.mem_closedBall.mpr hxOne.le, hyBounds⟩, ?_⟩, ?_⟩
    · change E (x', y) ∈ closure R
      have hyR : E (x', y) ∈ R := by
        simpa [E, realEuclideanAppendScalar] using hy
      exact subset_closure hyR
    · change y ∈ Vᶜ
      intro hyV
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hyV
      exact (not_lt_of_ge (hno z.1 z.2)) hz
  have hxMemP : x' ∈ P := ⟨(x', y), hpairK, rfl⟩
  exact (hballP (Metric.mem_ball.mpr hxP)) hxMemP

/-- A globally closed relation in a continuous open band satisfies the
closure-stability premise automatically. -/
theorem maxwellScalarFiberNoEscape_of_isClosed_of_continuousBand
    {p : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {lower upper : RealEuclidean p → ℝ}
    (hRclosed : IsClosed R)
    (hlower : ContinuousOn lower B)
    (hupper : ContinuousOn upper B)
    (hband : ∀ x ∈ B, ∀ y ∈ maxwellScalarFiber R x,
      lower x < y ∧ y < upper x) :
    MaxwellScalarFiberNoEscape B R := by
  apply maxwellScalarFiberNoEscape_of_continuousBand_of_closureStable
    (lower := lower) (upper := upper) ?_ hlower hupper hband
  intro x hx y hy
  rwa [hRclosed.closure_eq] at hy

/-- Closed-band specialization of the selector theorem. -/
theorem exists_continuous_strictOrdered_exactFiber_selectors_of_closedBand
    {p r : ℕ} {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {lower upper : RealEuclidean p → ℝ}
    (hRclosed : IsClosed R)
    (hlower : ContinuousOn lower B)
    (hupper : ContinuousOn upper B)
    (hband : ∀ x ∈ B, ∀ y ∈ maxwellScalarFiber R x,
      lower x < y ∧ y < upper x)
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (hcollision : MaxwellScalarFiberNoCollision B R) :
    ∃ f : Fin r → RealEuclidean p → ℝ,
      (∀ i, ContinuousOn (f i) B) ∧
      (∀ x ∈ B, StrictMono (fun i ↦ f i x)) ∧
      (∀ x ∈ B, Set.range (fun i ↦ f i x) =
        maxwellScalarFiber R x) :=
  exists_continuous_strictOrdered_exactFiber_selectors hfiber
    (maxwellScalarFiberNoEscape_of_isClosed_of_continuousBand
      hRclosed hlower hupper hband)
    hcollision

end AbelFormalization
