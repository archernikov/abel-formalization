import AbelFormalization.LionNestedFiberComponentBounds

/-!
# Lion's carpet compactification

This file formalizes the compact-limit part of Lemma 6 in Lion's proof of
uniform fiber finiteness.  A carpet gives compact positive superlevel sets.
Moving closed target balls then approximate an arbitrary fiber by an
increasing union of decreasing compact intersections.  The component bound
passes to that limit by `LionNestedFiberComponentBounds`.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- The two properties of a carpet used in Lion's compactification: it is
positive on its domain and every positive superlevel set in that domain is
compact. -/
structure IsLionCarpetOn {X : Type*} [TopologicalSpace X]
    (U : Set X) (delta : X → ℝ) : Prop where
  pos : ∀ x ∈ U, 0 < delta x
  isCompact_superlevel : ∀ eta : ℝ, 0 < eta →
    IsCompact {x | x ∈ U ∧ eta ≤ delta x}

/-- The radii have arbitrarily small positive upper bounds. -/
def LionRadiiTendToZero (r : ℕ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ i, r i < epsilon

/-- The carpet thresholds eventually lie below every positive number. -/
def LionThresholdsTendToZero (eta : ℕ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ j, eta j ≤ epsilon

/-- Lion's compact approximation at carpet threshold `eta`, target center
`T`, and target radius `r`. -/
def lionCompactApproximation
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (U : Set X) (delta : X → ℝ) (g : X → Y)
    (eta r : ℝ) (T : Y) : Set X :=
  {x | (x ∈ U ∧ eta ≤ delta x) ∧ dist (g x) T ≤ r}

/-- A carpet approximation is compact. -/
theorem lionCompactApproximation_isCompact
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {U : Set X} {delta : X → ℝ} {g : X → Y}
    (hcarpet : IsLionCarpetOn U delta) (hg : Continuous g)
    {eta : ℝ} (heta : 0 < eta) (r : ℝ) (T : Y) :
    IsCompact (lionCompactApproximation U delta g eta r T) := by
  have hball : IsClosed {x : X | dist (g x) T ≤ r} := by
    have hpreimage : g ⁻¹' Metric.closedBall T r =
        {x : X | dist (g x) T ≤ r} := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_closedBall,
        Set.mem_ofPred_eq]
    rw [← hpreimage]
    exact Metric.isClosed_closedBall.preimage hg
  exact (hcarpet.isCompact_superlevel eta heta).inter_right hball

/-- The moving target balls are nested under Lion's center/radius
inequality. -/
theorem lionCompactApproximation_antitone
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (U : Set X) (delta : X → ℝ) (g : X → Y) (eta : ℝ)
    (r : ℕ → ℝ) (T : ℕ → Y)
    (hstep : ∀ i,
      dist (T (i + 1)) (T i) + r (i + 1) ≤ r i) :
    Antitone (fun i ↦
      lionCompactApproximation U delta g eta (r i) (T i)) := by
  apply antitone_nat_of_succ_le
  intro i x hx
  refine ⟨hx.1, ?_⟩
  calc
    dist (g x) (T i) ≤
        dist (g x) (T (i + 1)) + dist (T (i + 1)) (T i) :=
      dist_triangle _ _ _
    _ ≤ r (i + 1) + dist (T (i + 1)) (T i) :=
      add_le_add hx.2 le_rfl
    _ = dist (T (i + 1)) (T i) + r (i + 1) := add_comm _ _
    _ ≤ r i := hstep i

/-- Moving balls centered increasingly close to `t`, with radii tending to
zero, cut out exactly the `t`-fiber at a fixed carpet threshold. -/
theorem iInter_lionCompactApproximation_eq_thresholdFiber
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (U : Set X) (delta : X → ℝ) (g : X → Y)
    (eta : ℝ) (r : ℕ → ℝ) (T : ℕ → Y) (t : Y)
    (hcenter : ∀ i, dist t (T i) ≤ r i)
    (hrzero : LionRadiiTendToZero r) :
    (⋂ i, lionCompactApproximation U delta g eta (r i) (T i)) =
      {x | (x ∈ U ∧ eta ≤ delta x) ∧ g x = t} := by
  ext x
  constructor
  · intro hx
    have hxi : ∀ i,
        x ∈ lionCompactApproximation U delta g eta (r i) (T i) :=
      Set.mem_iInter.mp hx
    refine ⟨(hxi 0).1, ?_⟩
    by_contra hne
    have hdist : 0 < dist (g x) t := dist_pos.mpr hne
    obtain ⟨i, hi⟩ := hrzero (dist (g x) t / 2) (half_pos hdist)
    have htriangle :
        dist (g x) t ≤ dist (g x) (T i) + dist (T i) t :=
      dist_triangle _ _ _
    have hleft := (hxi i).2
    have hright : dist (T i) t ≤ r i := by
      simpa only [dist_comm] using hcenter i
    linarith
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro i
    refine ⟨hx.1, ?_⟩
    simpa only [hx.2, dist_comm] using hcenter i

/-- The exact compact-limit conclusion of Lion's Lemma 6.  A uniform bound
on the compact generic approximations bounds the arbitrary target fiber. -/
theorem enatCard_connectedComponents_lionFiber_le
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    [MetricSpace Y]
    (U : Set X) (delta : X → ℝ) (g : X → Y)
    (hcarpet : IsLionCarpetOn U delta) (hg : Continuous g)
    (t : Y) (eta : ℕ → ℝ) (hetaPos : ∀ j, 0 < eta j)
    (hetaAnti : Antitone eta)
    (hetaZero : LionThresholdsTendToZero eta)
    (r : ℕ → ℕ → ℝ) (T : ℕ → ℕ → Y)
    (hcenter : ∀ j i, dist t (T j i) ≤ r j i)
    (hrzero : ∀ j, LionRadiiTendToZero (r j))
    (hstep : ∀ j i,
      dist (T j (i + 1)) (T j i) + r j (i + 1) ≤ r j i)
    (N : ℕ)
    (hbound : ∀ j i,
      ENat.card
        (ConnectedComponents
          (lionCompactApproximation U delta g
            (eta j) (r j i) (T j i))) ≤ (N : ℕ∞)) :
    ENat.card (ConnectedComponents {x | x ∈ U ∧ g x = t}) ≤
      (N : ℕ∞) := by
  let K : ℕ → ℕ → Set X := fun j i ↦
    lionCompactApproximation U delta g (eta j) (r j i) (T j i)
  have hKcompact : ∀ j i, IsCompact (K j i) := by
    intro j i
    exact lionCompactApproximation_isCompact
      hcarpet hg (hetaPos j) (r j i) (T j i)
  have hKanti : ∀ j, Antitone (K j) := by
    intro j
    exact lionCompactApproximation_antitone
      U delta g (eta j) (r j) (T j) (hstep j)
  have hKinter (j : ℕ) :
      (⋂ i, K j i) =
        {x | (x ∈ U ∧ eta j ≤ delta x) ∧ g x = t} := by
    exact iInter_lionCompactApproximation_eq_thresholdFiber
      U delta g (eta j) (r j) (T j) t (hcenter j) (hrzero j)
  have houter : Monotone (fun j ↦ ⋂ i, K j i) := by
    intro j k hjk
    change (⋂ i, K j i) ⊆ ⋂ i, K k i
    rw [hKinter j, hKinter k]
    intro x hx
    exact ⟨⟨hx.1.1, (hetaAnti hjk).trans hx.1.2⟩, hx.2⟩
  have hlimit : (⋃ j, ⋂ i, K j i) = {x | x ∈ U ∧ g x = t} := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      rw [hKinter j] at hxj
      exact ⟨hxj.1.1, hxj.2⟩
    · intro hx
      obtain ⟨j, hj⟩ := hetaZero (delta x) (hcarpet.pos x hx.1)
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      rw [hKinter j]
      exact ⟨⟨hx.1, hj⟩, hx.2⟩
  rw [← hlimit]
  exact enatCard_connectedComponents_iUnion_iInter_nat_le
    K hKanti hKcompact houter N hbound

end AbelFormalization
