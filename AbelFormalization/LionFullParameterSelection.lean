import AbelFormalization.LionCompactificationFiber
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Selecting Lion's compactification parameters

Lion's notion of a full subset of the target has two consequences used in
Lemma 6: its first-coordinate projection is dense, and above every point of
that projection the remaining fiber is dense.  This file isolates exactly
that consequence, constructs the nested parameters in Lemma 6, and combines
the construction with the compact-limit theorem.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The fiber of a set of compactification parameters above its first
coordinate. -/
def lionParameterFiber {Y : Type*}
    (R : Set (ℝ × (ℝ × Y))) (eta : ℝ) : Set (ℝ × Y) :=
  {w | (eta, w) ∈ R}

/-- The precise density consequence of Lion's `full` parameter sets that is
used in Lemma 6. -/
def IsLionFiberwiseDenseParameterSet {Y : Type*}
    [TopologicalSpace Y] (R : Set (ℝ × (ℝ × Y))) : Prop :=
  ∃ etaSet : Set ℝ,
    Dense etaSet ∧
      ∀ eta ∈ etaSet, Dense (lionParameterFiber R eta)

/-- A set with null complement for a measure positive on nonempty open sets
is dense. -/
theorem dense_of_measure_compl_eq_zero
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    (mu : MeasureTheory.Measure Z)
    [MeasureTheory.Measure.IsOpenPosMeasure mu]
    {S : Set Z} (hS : mu Sᶜ = 0) :
    Dense S := by
  have hinterior : interior Sᶜ = ∅ :=
    MeasureTheory.Measure.interior_eq_empty_of_null hS
  simpa only [compl_compl] using
    (interior_eq_empty_iff_dense_compl.mp hinterior)

/-- The measure-theoretic fragment of Lion's `full` condition needed for the
parameter set in Lemma 6.  The first-coordinate good set is conull and every
remaining fiber above it is conull. -/
def IsLionFullEuclideanParameterSet {p : ℕ}
    (R : Set (ℝ × (ℝ × RealEuclidean p))) : Prop :=
  ∃ etaSet : Set ℝ,
    MeasureTheory.volume etaSetᶜ = 0 ∧
      ∀ eta ∈ etaSet,
        MeasureTheory.volume (lionParameterFiber R eta)ᶜ = 0

theorem IsLionFullEuclideanParameterSet.fiberwiseDense
    {p : ℕ} {R : Set (ℝ × (ℝ × RealEuclidean p))}
    (hR : IsLionFullEuclideanParameterSet R) :
    IsLionFiberwiseDenseParameterSet R := by
  obtain ⟨etaSet, heta, hfiber⟩ := hR
  refine ⟨etaSet,
    dense_of_measure_compl_eq_zero MeasureTheory.volume heta, ?_⟩
  intro eta hetaSet
  exact dense_of_measure_compl_eq_zero MeasureTheory.volume
    (hfiber eta hetaSet)

/-- Positive elements of a dense subset of `ℝ` occur below every positive
bound. -/
theorem Dense.exists_pos_lt {S : Set ℝ} (hS : Dense S)
    {B : ℝ} (hB : 0 < B) :
    ∃ x ∈ S, 0 < x ∧ x < B := by
  obtain ⟨x, hxS, hxIoo⟩ :=
    hS.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hB)
  exact ⟨x, hxS, hxIoo⟩

/-- A canonical positive point of a dense real set below a supplied bound.
The fallback branch is irrelevant whenever the bound is positive. -/
noncomputable def lionDensePositivePick (S : Set ℝ) (hS : Dense S)
    (B : ℝ) : ℝ :=
  if hB : 0 < B then
    Classical.choose (Dense.exists_pos_lt hS hB)
  else 0

theorem lionDensePositivePick_spec (S : Set ℝ) (hS : Dense S)
    {B : ℝ} (hB : 0 < B) :
    lionDensePositivePick S hS B ∈ S ∧
      0 < lionDensePositivePick S hS B ∧
        lionDensePositivePick S hS B < B := by
  rw [lionDensePositivePick, dif_pos hB]
  exact Classical.choose_spec (Dense.exists_pos_lt hS hB)

/-- The decreasing positive threshold sequence selected from a dense set. -/
noncomputable def lionDenseThresholdSequence (S : Set ℝ)
    (hS : Dense S) : ℕ → ℝ
  | 0 => lionDensePositivePick S hS 1
  | n + 1 =>
      lionDensePositivePick S hS
        (min (lionDenseThresholdSequence S hS n)
          (1 / (n + 2 : ℝ)))

theorem lionDenseThresholdSequence_spec (S : Set ℝ) (hS : Dense S) :
    ∀ n,
      lionDenseThresholdSequence S hS n ∈ S ∧
        0 < lionDenseThresholdSequence S hS n ∧
          lionDenseThresholdSequence S hS n < 1 / (n + 1 : ℝ) := by
  intro n
  induction n with
  | zero =>
      simpa [lionDenseThresholdSequence] using
        lionDensePositivePick_spec S hS (B := 1) zero_lt_one
  | succ n ih =>
      have hrecip : 0 < (1 / (n + 2 : ℝ)) := by positivity
      have hbound :
          0 < min (lionDenseThresholdSequence S hS n)
            (1 / (n + 2 : ℝ)) := lt_min ih.2.1 hrecip
      have hpick := lionDensePositivePick_spec S hS hbound
      refine ⟨?_, ?_, ?_⟩
      · simpa only [lionDenseThresholdSequence] using hpick.1
      · simpa only [lionDenseThresholdSequence] using hpick.2.1
      · change
          lionDensePositivePick S hS
              (min (lionDenseThresholdSequence S hS n)
                (1 / (n + 2 : ℝ))) <
            1 / ((n + 1 : ℕ) + 1 : ℝ)
        have hlt := hpick.2.2.trans_le (min_le_right _ _)
        have hden :
            1 / (((n + 1 : ℕ) : ℝ) + 1) = 1 / ((n : ℝ) + 2) := by
          congr 1
          push_cast
          ring
        rw [hden]
        exact hlt

theorem lionDenseThresholdSequence_antitone (S : Set ℝ)
    (hS : Dense S) :
    Antitone (lionDenseThresholdSequence S hS) := by
  apply antitone_nat_of_succ_le
  intro n
  have hn := lionDenseThresholdSequence_spec S hS n
  have hrecip : 0 < (1 / (n + 2 : ℝ)) := by positivity
  have hbound :
      0 < min (lionDenseThresholdSequence S hS n)
        (1 / (n + 2 : ℝ)) := lt_min hn.2.1 hrecip
  have hpick := lionDensePositivePick_spec S hS hbound
  exact (by
    simpa only [lionDenseThresholdSequence] using
      hpick.2.2.le.trans (min_le_left _ _))

theorem lionDenseThresholdSequence_tendToZero (S : Set ℝ)
    (hS : Dense S) :
    LionThresholdsTendToZero (lionDenseThresholdSequence S hS) := by
  intro epsilon hepsilon
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  refine ⟨n, ?_⟩
  exact (lionDenseThresholdSequence_spec S hS n).2.2.le.trans
    (le_of_lt (by simpa using hn))

/-- The open set of target parameters whose positive square-root radius is
below `B` and whose center is closer than that radius to `t`. -/
def lionAdmissibleTargetSet {Y : Type*} [MetricSpace Y]
    (t : Y) (B : ℝ) : Set (ℝ × Y) :=
  {w | 0 < w.1 ∧ Real.sqrt w.1 < B ∧ dist t w.2 < Real.sqrt w.1}

theorem isOpen_lionAdmissibleTargetSet {Y : Type*} [MetricSpace Y]
    (t : Y) (B : ℝ) :
    IsOpen (lionAdmissibleTargetSet t B) := by
  exact
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt (Real.continuous_sqrt.comp continuous_fst)
        continuous_const).inter
        (isOpen_lt (continuous_const.dist continuous_snd)
          (Real.continuous_sqrt.comp continuous_fst)))

theorem lionAdmissibleTargetSet_nonempty {Y : Type*} [MetricSpace Y]
    (t : Y) {B : ℝ} (hB : 0 < B) :
    (lionAdmissibleTargetSet t B).Nonempty := by
  refine ⟨((B / 2) ^ 2, t), ?_⟩
  have hhalf : 0 < B / 2 := half_pos hB
  simp only [lionAdmissibleTargetSet, Set.mem_setOf_eq,
    sq_pos_of_pos hhalf, Real.sqrt_sq_eq_abs, abs_of_pos hhalf,
    dist_self, hhalf, true_and]
  exact ⟨half_lt_self hB, trivial⟩

/-- A canonical admissible parameter from a dense set. -/
noncomputable def lionDenseTargetPick {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : Dense S) (t : Y) (B : ℝ) : ℝ × Y :=
  if hB : 0 < B then
    Classical.choose
      (hS.exists_mem_open (isOpen_lionAdmissibleTargetSet t B)
        (lionAdmissibleTargetSet_nonempty t hB))
  else (0, t)

theorem lionDenseTargetPick_spec {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : Dense S) (t : Y)
    {B : ℝ} (hB : 0 < B) :
    lionDenseTargetPick S hS t B ∈ S ∧
      0 < (lionDenseTargetPick S hS t B).1 ∧
      Real.sqrt (lionDenseTargetPick S hS t B).1 < B ∧
      dist t (lionDenseTargetPick S hS t B).2 <
        Real.sqrt (lionDenseTargetPick S hS t B).1 := by
  rw [lionDenseTargetPick, dif_pos hB]
  have hspec := Classical.choose_spec
    (hS.exists_mem_open (isOpen_lionAdmissibleTargetSet t B)
      (lionAdmissibleTargetSet_nonempty t hB))
  exact ⟨hspec.1, hspec.2⟩

/-- A sequence of dense target parameters with shrinking radii and enough
room at every stage to make the corresponding closed balls nested. -/
noncomputable def lionDenseTargetSequence {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : Dense S) (t : Y) : ℕ → ℝ × Y
  | 0 => lionDenseTargetPick S hS t 1
  | n + 1 =>
      let previous := lionDenseTargetSequence S hS t n
      let margin := Real.sqrt previous.1 - dist t previous.2
      lionDenseTargetPick S hS t
        (min (margin / 2) (1 / (n + 2 : ℝ)))

theorem lionDenseTargetSequence_spec {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : Dense S) (t : Y) :
    ∀ n,
      lionDenseTargetSequence S hS t n ∈ S ∧
      0 < (lionDenseTargetSequence S hS t n).1 ∧
      Real.sqrt (lionDenseTargetSequence S hS t n).1 <
        1 / (n + 1 : ℝ) ∧
      dist t (lionDenseTargetSequence S hS t n).2 <
        Real.sqrt (lionDenseTargetSequence S hS t n).1 := by
  intro n
  induction n with
  | zero =>
      simpa [lionDenseTargetSequence] using
        lionDenseTargetPick_spec S hS t (B := 1) zero_lt_one
  | succ n ih =>
      let previous := lionDenseTargetSequence S hS t n
      let margin := Real.sqrt previous.1 - dist t previous.2
      have hmargin : 0 < margin := by
        dsimp only [margin, previous]
        linarith [ih.2.2.2]
      have hrecip : 0 < (1 / (n + 2 : ℝ)) := by positivity
      have hbound : 0 < min (margin / 2) (1 / (n + 2 : ℝ)) :=
        lt_min (half_pos hmargin) hrecip
      have hpick := lionDenseTargetPick_spec S hS t hbound
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [lionDenseTargetSequence, previous, margin] using hpick.1
      · simpa only [lionDenseTargetSequence, previous, margin] using hpick.2.1
      · change
          Real.sqrt
              (lionDenseTargetPick S hS t
                (min (margin / 2) (1 / (n + 2 : ℝ)))).1 <
            1 / ((n + 1 : ℕ) + 1 : ℝ)
        have hlt := hpick.2.2.1.trans_le (min_le_right _ _)
        have hden :
            1 / (((n + 1 : ℕ) : ℝ) + 1) = 1 / ((n : ℝ) + 2) := by
          congr 1
          push_cast
          ring
        rw [hden]
        exact hlt
      · simpa only [lionDenseTargetSequence, previous, margin] using
          hpick.2.2.2

theorem lionDenseTargetSequence_step {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : Dense S) (t : Y) (n : ℕ) :
    dist (lionDenseTargetSequence S hS t (n + 1)).2
        (lionDenseTargetSequence S hS t n).2 +
      Real.sqrt (lionDenseTargetSequence S hS t (n + 1)).1 ≤
        Real.sqrt (lionDenseTargetSequence S hS t n).1 := by
  let previous := lionDenseTargetSequence S hS t n
  let margin := Real.sqrt previous.1 - dist t previous.2
  have hprev := lionDenseTargetSequence_spec S hS t n
  have hmargin : 0 < margin := by
    dsimp only [margin, previous]
    linarith [hprev.2.2.2]
  have hrecip : 0 < (1 / (n + 2 : ℝ)) := by positivity
  have hbound : 0 < min (margin / 2) (1 / (n + 2 : ℝ)) :=
    lt_min (half_pos hmargin) hrecip
  have hnext := lionDenseTargetPick_spec S hS t hbound
  have hrnext :
      Real.sqrt (lionDenseTargetSequence S hS t (n + 1)).1 <
        margin / 2 := by
    simpa only [lionDenseTargetSequence, previous, margin] using
      hnext.2.2.1.trans_le (min_le_left _ _)
  have hcenterNext :
      dist (lionDenseTargetSequence S hS t (n + 1)).2 t <
        Real.sqrt (lionDenseTargetSequence S hS t (n + 1)).1 := by
    simpa only [dist_comm] using
      (lionDenseTargetSequence_spec S hS t (n + 1)).2.2.2
  have htriangle := dist_triangle
    (lionDenseTargetSequence S hS t (n + 1)).2 t previous.2
  dsimp only [margin, previous] at hrnext htriangle ⊢
  linarith

theorem lionDenseTargetSequence_radii_tendToZero
    {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : Dense S) (t : Y) :
    LionRadiiTendToZero
      (fun n ↦ Real.sqrt (lionDenseTargetSequence S hS t n).1) := by
  intro epsilon hepsilon
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  refine ⟨n, ?_⟩
  exact (lionDenseTargetSequence_spec S hS t n).2.2.1.trans
    (by simpa using hn)

/-- Lion's parameter-selection sentence following Lemma 6, in the exact form
consumed by the compact-limit theorem. -/
theorem IsLionFiberwiseDenseParameterSet.exists_compactificationParametersAt
    {Y : Type*} [MetricSpace Y] {R : Set (ℝ × (ℝ × Y))}
    (hR : IsLionFiberwiseDenseParameterSet R) (t : Y) :
    ∃ eta : ℕ → ℝ, ∃ r : ℕ → ℕ → ℝ, ∃ T : ℕ → ℕ → Y,
      (∀ j i, (eta j, ((r j i) ^ 2, T j i)) ∈ R) ∧
      (∀ j, 0 < eta j) ∧ Antitone eta ∧
      LionThresholdsTendToZero eta ∧
      (∀ j i, dist t (T j i) ≤ r j i) ∧
      (∀ j, LionRadiiTendToZero (r j)) ∧
      (∀ j i, dist (T j (i + 1)) (T j i) + r j (i + 1) ≤ r j i) := by
  obtain ⟨etaSet, hetaDense, hfiberDense⟩ := hR
  let eta := lionDenseThresholdSequence etaSet hetaDense
  let parameter (j i : ℕ) : ℝ × Y :=
    lionDenseTargetSequence (lionParameterFiber R (eta j))
      (hfiberDense (eta j)
        (lionDenseThresholdSequence_spec etaSet hetaDense j).1)
      t i
  let r : ℕ → ℕ → ℝ := fun j i ↦ Real.sqrt (parameter j i).1
  let T : ℕ → ℕ → Y := fun j i ↦ (parameter j i).2
  refine ⟨eta, r, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    have hparam := (lionDenseTargetSequence_spec
      (lionParameterFiber R (eta j))
      (hfiberDense (eta j)
        (lionDenseThresholdSequence_spec etaSet hetaDense j).1)
      t i).1
    change (eta j, parameter j i) ∈ R at hparam
    have hnonneg : 0 ≤ (parameter j i).1 :=
      (lionDenseTargetSequence_spec
        (lionParameterFiber R (eta j))
        (hfiberDense (eta j)
          (lionDenseThresholdSequence_spec etaSet hetaDense j).1)
        t i).2.1.le
    simpa only [r, T, Real.sq_sqrt hnonneg] using hparam
  · intro j
    exact (lionDenseThresholdSequence_spec etaSet hetaDense j).2.1
  · exact lionDenseThresholdSequence_antitone etaSet hetaDense
  · exact lionDenseThresholdSequence_tendToZero etaSet hetaDense
  · intro j i
    exact (lionDenseTargetSequence_spec
      (lionParameterFiber R (eta j))
      (hfiberDense (eta j)
        (lionDenseThresholdSequence_spec etaSet hetaDense j).1)
      t i).2.2.2.le
  · intro j
    exact lionDenseTargetSequence_radii_tendToZero
      (lionParameterFiber R (eta j))
      (hfiberDense (eta j)
        (lionDenseThresholdSequence_spec etaSet hetaDense j).1) t
  · intro j i
    exact lionDenseTargetSequence_step
      (lionParameterFiber R (eta j))
      (hfiberDense (eta j)
        (lionDenseThresholdSequence_spec etaSet hetaDense j).1) t i

/-- A uniform component bound on a fiberwise-dense set of fibers of Lion's
enlarged map bounds every fiber of the original map.  This is the complete
compactification step of Lion's proof of Theorem 2. -/
theorem enatCard_connectedComponents_lionFiber_le_of_fiberwiseDense
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    [MetricSpace Y]
    (delta : X → ℝ) (g : X → Y)
    (hcarpet : IsLionCarpetOn (Set.univ : Set X) delta)
    (hg : Continuous g)
    (R : Set (ℝ × (ℝ × Y)))
    (hR : IsLionFiberwiseDenseParameterSet R)
    (N : ℕ)
    (hbound : ∀ w ∈ R,
      ENat.card
          (ConnectedComponents
            ((lionCompactificationMap delta g) ⁻¹' {w})) ≤ (N : ℕ∞))
    (t : Y) :
    ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ (N : ℕ∞) := by
  obtain ⟨eta, r, T, hmem, hetaPos, hetaAnti,
      hetaZero, hcenter, hrzero, hstep⟩ :=
    hR.exists_compactificationParametersAt t
  have hfiber : g ⁻¹' {t} = {x | x ∈ (Set.univ : Set X) ∧ g x = t} := by
    ext x
    simp
  rw [hfiber]
  apply enatCard_connectedComponents_lionFiber_le
    Set.univ delta g hcarpet hg t eta hetaPos hetaAnti hetaZero
      r T hcenter hrzero hstep N
  intro j i
  apply enatCard_lionCompactApproximation_le_of_fiber_le
    delta g (eta j) (r j i) (T j i)
  · exact (hcenter j i).trans' dist_nonneg
  · simpa only [lionCompactificationTargetPoint] using
      hbound (lionCompactificationTargetPoint (eta j) (r j i) (T j i))
        (hmem j i)

/-- Measure-theoretic `full`-set form of the compactification step for
Euclidean targets. -/
theorem enatCard_connectedComponents_lionFiber_le_of_full
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    {p : ℕ}
    (delta : X → ℝ) (g : X → RealEuclidean p)
    (hcarpet : IsLionCarpetOn (Set.univ : Set X) delta)
    (hg : Continuous g)
    (R : Set (ℝ × (ℝ × RealEuclidean p)))
    (hR : IsLionFullEuclideanParameterSet R)
    (N : ℕ)
    (hbound : ∀ w ∈ R,
      ENat.card
          (ConnectedComponents
            ((lionCompactificationMap delta g) ⁻¹' {w})) ≤ (N : ℕ∞))
    (t : RealEuclidean p) :
    ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ (N : ℕ∞) :=
  enatCard_connectedComponents_lionFiber_le_of_fiberwiseDense
    delta g hcarpet hg R hR.fiberwiseDense N hbound t

/-- The generic conclusion supplied by Lion's Theorem 7 when it is applied
to the enlarged compactification map. -/
def HasLionFullGenericCompactificationFiberBound
    {a p : ℕ} (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean p) : Prop :=
  ∃ N : ℕ, ∃ R : Set (ℝ × (ℝ × RealEuclidean p)),
    IsLionFullEuclideanParameterSet R ∧
      ∀ w ∈ R,
        ENat.card
            (ConnectedComponents
              ((lionCompactificationMap delta g) ⁻¹' {w})) ≤ (N : ℕ∞)

/-- Quantifier-complete form of Lion's compactification argument: one generic
bound for the enlarged map gives one bound for all target fibers of `g`. -/
theorem hasUniformFiberComponentBound_of_lionFullGenericCompactification
    {a p : ℕ} (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean p)
    (hcarpet : IsLionCarpetOn (Set.univ : Set (RealEuclidean a)) delta)
    (hg : Continuous g)
    (hgeneric : HasLionFullGenericCompactificationFiberBound delta g) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ (N : ℕ∞) := by
  obtain ⟨N, R, hR, hbound⟩ := hgeneric
  refine ⟨N, ?_⟩
  intro t
  exact enatCard_connectedComponents_lionFiber_le_of_full
    delta g hcarpet hg R hR N hbound t

/-- Family-level generic conclusion that Lion's Theorem 7' must provide for
the standard compactification of every family tuple. -/
def HasLionFullGenericCompactificationBoundsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a p (g : RealEuclidean a → RealEuclidean p),
    FunctionTupleInFamily G g →
      HasLionFullGenericCompactificationFiberBound
        (lionStandardCarpet a) g

/-- The completed Lemma 6 reduction at family level.  After Theorem 7'
supplies its generic full-set bound, no further premise is needed to obtain
uniform fiber finiteness. -/
theorem hasUniformFiberFiniteness_of_lionFullGenericCompactification
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hgeneric : HasLionFullGenericCompactificationBoundsForFamily G) :
    HasUniformFiberFiniteness G := by
  intro a p g hgmem
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro j
    exact hsmooth a (fun x ↦ g x j) (hgmem j)
  exact hasUniformFiberComponentBound_of_lionFullGenericCompactification
    (lionStandardCarpet a) g
      (isLionCarpetOn_univ_lionStandardCarpet a)
      hgSmooth.continuous (hgeneric a p g hgmem)

end AbelFormalization
