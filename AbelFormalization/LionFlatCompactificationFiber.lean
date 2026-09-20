import AbelFormalization.LionFlatCompactification
import AbelFormalization.ProjectedFiberComponents
import AbelFormalization.LionFullParameterSelection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fibers of Lion's flat compactification map

Theorem 7' applies to the flat Euclidean enlarged map, whereas the initial
Lemma 6 development used nested product coordinates.  This file identifies
the visible projection of a flat fiber directly with Lion's compact
approximation and feeds flat generic bounds into the completed limit argument.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The flat target vector corresponding to `(eta,r²,T)`. -/
def lionFlatCompactificationTargetPoint {b : ℕ}
    (eta r : ℝ) (T : RealEuclidean b) :
    RealEuclidean (1 + (1 + b)) :=
  realEuclideanAppend (fun _ ↦ eta)
    (realEuclideanAppend (fun _ ↦ r ^ 2) T)

@[simp]
theorem lionFlatCompactificationTargetPoint_first {b : ℕ}
    (eta r : ℝ) (T : RealEuclidean b) :
    realEuclideanTakeLeft
        (lionFlatCompactificationTargetPoint eta r T) 0 = eta := by
  simp [lionFlatCompactificationTargetPoint]

@[simp]
theorem lionFlatCompactificationTargetPoint_second {b : ℕ}
    (eta r : ℝ) (T : RealEuclidean b) :
    realEuclideanTakeLeft
        (realEuclideanTakeRight
          (lionFlatCompactificationTargetPoint eta r T)) 0 = r ^ 2 := by
  simp [lionFlatCompactificationTargetPoint]

@[simp]
theorem lionFlatCompactificationTargetPoint_target {b : ℕ}
    (eta r : ℝ) (T : RealEuclidean b) :
    realEuclideanTakeRight
        (realEuclideanTakeRight
          (lionFlatCompactificationTargetPoint eta r T)) = T := by
  simp [lionFlatCompactificationTargetPoint]

/-- Algebraic squared distance in the flat enlarged map is the squared
Euclidean distance after the canonical `L²` realization. -/
theorem lionFlatCompactificationTargetDistanceSq_eq_dist_sq
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (x : RealEuclidean a) (T : RealEuclidean b) :
    (∑ j : Fin b, (g x j - T j) ^ 2) =
      dist (lionEuclideanTarget (g x)) (lionEuclideanTarget T) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [lionEuclideanTarget, euclideanCenter_apply, Real.dist_eq,
    sq_abs]

/-- The visible-coordinate projection of a flat compactification fiber is
exactly the compact set used in Lion's Lemma 6. -/
theorem flatProjectedFiberSet_lionFlatCompactificationMap_eq_approximation
    {a b : ℕ}
    (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean b)
    (eta r : ℝ) (T : RealEuclidean b) (hr : 0 ≤ r) :
    flatProjectedFiberSet (lionFlatCompactificationMap delta g)
        (lionFlatCompactificationTargetPoint eta r T) =
      lionCompactApproximation Set.univ delta
        (fun x ↦ lionEuclideanTarget (g x)) eta r
        (lionEuclideanTarget T) := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    let u : RealEuclidean 1 := realEuclideanTakeLeft z
    let rest : RealEuclidean (1 + b) := realEuclideanTakeRight z
    let v : RealEuclidean 1 := realEuclideanTakeLeft rest
    let t : RealEuclidean b := realEuclideanTakeRight rest
    have hzsplit : realEuclideanAppend u (realEuclideanAppend v t) = z := by
      simp only [u, v, t, rest, realEuclideanAppend_take]
    rw [← hzsplit, lionFlatCompactificationMap_append] at hz
    have hetaEq : delta x - u 0 ^ 2 = eta := by
      have h := congrArg
        (fun w ↦ realEuclideanTakeLeft w 0) hz
      simpa [lionFlatCompactificationTargetPoint] using h
    have hrEq :
        (∑ j : Fin b, (g x j - t j) ^ 2) + v 0 ^ 2 = r ^ 2 := by
      have h := congrArg
        (fun w ↦ realEuclideanTakeLeft (realEuclideanTakeRight w) 0) hz
      simpa [lionFlatCompactificationTargetPoint] using h
    have ht : t = T := by
      have h := congrArg
        (fun w ↦ realEuclideanTakeRight (realEuclideanTakeRight w)) hz
      simpa [lionFlatCompactificationTargetPoint] using h
    rw [ht] at hrEq
    have hetaLe : eta ≤ delta x := by
      nlinarith [sq_nonneg (u 0)]
    have hdist :
        dist (lionEuclideanTarget (g x)) (lionEuclideanTarget T) ≤ r := by
      have hd : 0 ≤
          dist (lionEuclideanTarget (g x)) (lionEuclideanTarget T) :=
        dist_nonneg
      have hsq :=
        lionFlatCompactificationTargetDistanceSq_eq_dist_sq g x T
      nlinarith [sq_nonneg (v 0)]
    exact ⟨⟨Set.mem_univ x, hetaLe⟩, hdist⟩
  · rintro ⟨⟨_hx, hetaLe⟩, hdist⟩
    let u : ℝ := Real.sqrt (delta x - eta)
    let d2 : ℝ := ∑ j : Fin b, (g x j - T j) ^ 2
    let v : ℝ := Real.sqrt (r ^ 2 - d2)
    have huNonneg : 0 ≤ delta x - eta := sub_nonneg.mpr hetaLe
    have hd2 : d2 =
        dist (lionEuclideanTarget (g x)) (lionEuclideanTarget T) ^ 2 := by
      exact lionFlatCompactificationTargetDistanceSq_eq_dist_sq g x T
    have hvNonneg : 0 ≤ r ^ 2 - d2 := by
      have hd : 0 ≤
          dist (lionEuclideanTarget (g x)) (lionEuclideanTarget T) :=
        dist_nonneg
      rw [hd2]
      nlinarith
    refine ⟨realEuclideanAppend (fun _ ↦ u)
      (realEuclideanAppend (fun _ ↦ v) T), ?_⟩
    rw [lionFlatCompactificationMap_append]
    simp only [lionFlatCompactificationTargetPoint, u, v, d2,
      Real.sq_sqrt huNonneg, Real.sq_sqrt hvNonneg]
    funext q
    refine Fin.addCases (fun _ ↦ ?_) (fun q' ↦ ?_) q
    · simp [realEuclideanAppend]
    · refine Fin.addCases (fun _ ↦ ?_) (fun j ↦ ?_) q'
      · simp [realEuclideanAppend]
      · simp [realEuclideanAppend]

/-- Projection cannot increase the number of components, now stated for the
flat Euclidean map to which Theorem 7' applies. -/
theorem enatCard_lionCompactApproximation_le_flatCompactificationFiber
    {a b : ℕ}
    (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean b)
    (eta r : ℝ) (T : RealEuclidean b) (hr : 0 ≤ r) :
    ENat.card
        (ConnectedComponents
          (lionCompactApproximation Set.univ delta
            (fun x ↦ lionEuclideanTarget (g x)) eta r
            (lionEuclideanTarget T))) ≤
      ENat.card
        (ConnectedComponents
          ((lionFlatCompactificationMap delta g) ⁻¹'
            {lionFlatCompactificationTargetPoint eta r T})) := by
  rw [← flatProjectedFiberSet_lionFlatCompactificationMap_eq_approximation
    delta g eta r T hr]
  exact enatCard_connectedComponents_flatProjectedFiberSet_le
    (lionFlatCompactificationMap delta g)
    (lionFlatCompactificationTargetPoint eta r T)

/-- Turning an `L²` Euclidean point back into its coordinate function and
then applying the canonical `L²` realization recovers the original point. -/
@[simp]
theorem lionEuclideanTarget_ofLp {b : ℕ}
    (T : EuclideanSpace ℝ (Fin b)) :
    lionEuclideanTarget T.ofLp = T := by
  ext j
  exact euclideanCenter_apply T.ofLp j

/-- Flatten a product parameter `(eta, epsilon, T)`, with `T` carrying the
`L²` Euclidean metric, into the target coordinates of Lion's flat map. -/
def lionFlatCompactificationParameterTarget {b : ℕ}
    (w : ℝ × (ℝ × EuclideanSpace ℝ (Fin b))) :
    RealEuclidean (1 + (1 + b)) :=
  realEuclideanAppend (fun _ ↦ w.1)
    (realEuclideanAppend (fun _ ↦ w.2.1) w.2.2.ofLp)

@[simp]
theorem lionFlatCompactificationParameterTarget_targetPoint
    {b : ℕ} (eta r : ℝ) (T : EuclideanSpace ℝ (Fin b)) :
    lionFlatCompactificationParameterTarget (eta, (r ^ 2, T)) =
      lionFlatCompactificationTargetPoint eta r T.ofLp := by
  rfl

/-- The measure-theoretic full-set hypothesis for the flat
compactification, expressed in the metric actually used by its sum of
squares.  In particular, the target factor is `EuclideanSpace`, not the
canonical Pi-norm metric on `RealEuclidean`. -/
def IsLionFullFlatEuclideanParameterSet {p : ℕ}
    (R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))) : Prop :=
  ∃ etaSet : Set ℝ,
    MeasureTheory.volume etaSetᶜ = 0 ∧
      ∀ eta ∈ etaSet,
        MeasureTheory.volume (lionParameterFiber R eta)ᶜ = 0

/-- A full flat parameter set is fiberwise dense for the `L²` metric. -/
theorem IsLionFullFlatEuclideanParameterSet.fiberwiseDense
    {p : ℕ}
    {R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))}
    (hR : IsLionFullFlatEuclideanParameterSet R) :
    IsLionFiberwiseDenseParameterSet R := by
  obtain ⟨etaSet, heta, hfiber⟩ := hR
  refine ⟨etaSet,
    dense_of_measure_compl_eq_zero MeasureTheory.volume heta, ?_⟩
  intro eta hetaSet
  exact dense_of_measure_compl_eq_zero MeasureTheory.volume
    (hfiber eta hetaSet)

/-- A uniform component bound on a fiberwise-dense `L²` set of fibers of
the flat compactification bounds every fiber of the original tuple. -/
theorem enatCard_connectedComponents_lionFiber_le_of_flat_fiberwiseDense
    {a p : ℕ}
    (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean p)
    (hcarpet : IsLionCarpetOn (Set.univ : Set (RealEuclidean a)) delta)
    (hg : Continuous g)
    (R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))))
    (hR : IsLionFiberwiseDenseParameterSet R)
    (N : ℕ)
    (hbound : ∀ w ∈ R,
      ENat.card
          (ConnectedComponents
            ((lionFlatCompactificationMap delta g) ⁻¹'
              {lionFlatCompactificationParameterTarget w})) ≤ (N : ℕ∞))
    (t : RealEuclidean p) :
    ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ (N : ℕ∞) := by
  let gL2 : RealEuclidean a → EuclideanSpace ℝ (Fin p) :=
    fun x ↦ lionEuclideanTarget (g x)
  have hgL2 : Continuous gL2 := by
    exact
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p ↦ ℝ)).symm.continuous.comp hg
  obtain ⟨eta, r, T, hmem, hetaPos, hetaAnti,
      hetaZero, hcenter, hrzero, hstep⟩ :=
    hR.exists_compactificationParametersAt (lionEuclideanTarget t)
  have hfiber :
      g ⁻¹' {t} = gL2 ⁻¹' {lionEuclideanTarget t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, gL2]
    constructor
    · intro hx
      rw [hx]
    · intro hx
      funext j
      have hj := congrArg (fun y : EuclideanSpace ℝ (Fin p) ↦ y.ofLp j) hx
      simpa [lionEuclideanTarget] using hj
  rw [hfiber]
  have hfiberSet :
      gL2 ⁻¹' {lionEuclideanTarget t} =
        {x | x ∈ (Set.univ : Set (RealEuclidean a)) ∧
          gL2 x = lionEuclideanTarget t} := by
    ext x
    simp
  rw [hfiberSet]
  apply enatCard_connectedComponents_lionFiber_le
    Set.univ delta gL2 hcarpet hgL2 (lionEuclideanTarget t)
      eta hetaPos hetaAnti hetaZero r T hcenter hrzero hstep N
  intro j i
  have hflat :=
    enatCard_lionCompactApproximation_le_flatCompactificationFiber
      delta g (eta j) (r j i) (T j i).ofLp
        ((hcenter j i).trans' dist_nonneg)
  rw [lionEuclideanTarget_ofLp] at hflat
  have hb := hbound (eta j, ((r j i) ^ 2, T j i)) (hmem j i)
  rw [lionFlatCompactificationParameterTarget_targetPoint] at hb
  exact hflat.trans hb

/-- Measure-theoretic full-set form of the flat compactification bridge. -/
theorem enatCard_connectedComponents_lionFiber_le_of_flat_full
    {a p : ℕ}
    (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean p)
    (hcarpet : IsLionCarpetOn (Set.univ : Set (RealEuclidean a)) delta)
    (hg : Continuous g)
    (R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))))
    (hR : IsLionFullFlatEuclideanParameterSet R)
    (N : ℕ)
    (hbound : ∀ w ∈ R,
      ENat.card
          (ConnectedComponents
            ((lionFlatCompactificationMap delta g) ⁻¹'
              {lionFlatCompactificationParameterTarget w})) ≤ (N : ℕ∞))
    (t : RealEuclidean p) :
    ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ (N : ℕ∞) :=
  enatCard_connectedComponents_lionFiber_le_of_flat_fiberwiseDense
    delta g hcarpet hg R hR.fiberwiseDense N hbound t

/-- The exact generic conclusion needed from Theorem 7' for one flat
compactification map. -/
def HasLionFullGenericFlatCompactificationFiberBound
    {a p : ℕ} (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean p) : Prop :=
  ∃ N : ℕ,
    ∃ R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))),
      IsLionFullFlatEuclideanParameterSet R ∧
        ∀ w ∈ R,
          ENat.card
              (ConnectedComponents
                ((lionFlatCompactificationMap delta g) ⁻¹'
                  {lionFlatCompactificationParameterTarget w})) ≤ (N : ℕ∞)

/-- One full generic bound for the flat enlarged map gives a single bound
for every target fiber of the original tuple. -/
theorem hasUniformFiberComponentBound_of_lionFullGenericFlatCompactification
    {a p : ℕ} (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean p)
    (hcarpet : IsLionCarpetOn (Set.univ : Set (RealEuclidean a)) delta)
    (hg : Continuous g)
    (hgeneric : HasLionFullGenericFlatCompactificationFiberBound delta g) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ (N : ℕ∞) := by
  obtain ⟨N, R, hR, hbound⟩ := hgeneric
  refine ⟨N, ?_⟩
  intro t
  exact enatCard_connectedComponents_lionFiber_le_of_flat_full
    delta g hcarpet hg R hR N hbound t

/-- Family-level flat generic conclusion that Lion's Theorem 7' must
provide for the standard compactification of every family tuple. -/
def HasLionFullGenericFlatCompactificationBoundsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a p (g : RealEuclidean a → RealEuclidean p),
    FunctionTupleInFamily G g →
      HasLionFullGenericFlatCompactificationFiberBound
        (lionStandardCarpet a) g

/-- The completed flat-coordinate Lemma 6 reduction at family level. -/
theorem hasUniformFiberFiniteness_of_lionFullGenericFlatCompactification
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hgeneric : HasLionFullGenericFlatCompactificationBoundsForFamily G) :
    HasUniformFiberFiniteness G := by
  intro a p g hgmem
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro j
    exact hsmooth a (fun x ↦ g x j) (hgmem j)
  exact
    hasUniformFiberComponentBound_of_lionFullGenericFlatCompactification
      (lionStandardCarpet a) g
      (isLionCarpetOn_univ_lionStandardCarpet a)
      hgSmooth.continuous (hgeneric a p g hgmem)

end AbelFormalization
