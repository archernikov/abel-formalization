import AbelFormalization.CriticalSystemExpressions
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Closed denominator graphs and connected-component counting

This file isolates the topological part of the manuscript's exponential
adjunction argument.  Adjoining `z` with `z * q x = 1` produces a closed
graph whenever `q` is continuous.  A separate abstract argument shows that a
finite set meeting every connected component makes the component quotient
finite, and that a continuous function with compact sublevel sets has a
minimum on every connected component.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*}

/-- The graph obtained by adjoining the reciprocal of a denominator. -/
def denominatorGraph (q : X → ℝ) : Set (X × ℝ) :=
  {p | p.2 * q p.1 = 1}

theorem isClosed_denominatorGraph [TopologicalSpace X]
    (q : X → ℝ) (hq : Continuous q) :
    IsClosed (denominatorGraph q) := by
  exact isClosed_eq (continuous_snd.mul (hq.comp continuous_fst)) continuous_const

theorem denominatorGraph_denominator_ne_zero (q : X → ℝ)
    {p : X × ℝ} (hp : p ∈ denominatorGraph q) :
    q p.1 ≠ 0 := by
  intro hq0
  rw [denominatorGraph, mem_ofPred_eq, hq0, mul_zero] at hp
  exact zero_ne_one hp

theorem denominatorGraph_snd_eq_inv (q : X → ℝ)
    {p : X × ℝ} (hp : p ∈ denominatorGraph q) :
    p.2 = (q p.1)⁻¹ :=
  eq_inv_of_mul_eq_one_left hp

theorem existsUnique_mem_denominatorGraph_iff (q : X → ℝ) (x : X) :
    (∃! z : ℝ, (x, z) ∈ denominatorGraph q) ↔ q x ≠ 0 := by
  constructor
  · rintro ⟨z, hz, -⟩
    exact denominatorGraph_denominator_ne_zero q hz
  · intro hqx
    refine ⟨(q x)⁻¹, ?_, ?_⟩
    · exact inv_mul_cancel₀ hqx
    · intro z hz
      exact denominatorGraph_snd_eq_inv q hz

theorem fst_image_denominatorGraph (q : X → ℝ) :
    Prod.fst '' denominatorGraph q = {x | q x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact denominatorGraph_denominator_ne_zero q hp
  · intro hx
    exact ⟨(x, (q x)⁻¹), inv_mul_cancel₀ hx, rfl⟩

theorem Prod.fst_injectiveOn_denominatorGraph (q : X → ℝ) :
    Set.InjOn Prod.fst (denominatorGraph q) := by
  intro p hp p' hp' hfst
  apply Prod.ext hfst
  rw [denominatorGraph_snd_eq_inv q hp,
    denominatorGraph_snd_eq_inv q hp', hfst]

/-- A closed form of the locus used in the manuscript: equations vanish,
boundary factors are nonnegative, and the reciprocal equation holds. -/
def closedDenominatorLocus {r b : ℕ}
    (H : Fin r → X → ℝ) (u : Fin b → X → ℝ) (q : X → ℝ) :
    Set (X × ℝ) :=
  {p | (∀ i, H i p.1 = 0) ∧ (∀ i, 0 ≤ u i p.1) ∧ p.2 * q p.1 = 1}

theorem isClosed_closedDenominatorLocus [TopologicalSpace X]
    {r b : ℕ} (H : Fin r → X → ℝ) (u : Fin b → X → ℝ)
    (q : X → ℝ) (hH : ∀ i, Continuous (H i))
    (hu : ∀ i, Continuous (u i)) (hq : Continuous q) :
    IsClosed (closedDenominatorLocus H u q) := by
  have hHclosed : IsClosed {p : X × ℝ | ∀ i, H i p.1 = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i ↦
      isClosed_eq ((hH i).comp continuous_fst) continuous_const
  have huclosed : IsClosed {p : X × ℝ | ∀ i, 0 ≤ u i p.1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i ↦
      isClosed_le continuous_const ((hu i).comp continuous_fst)
  rw [show closedDenominatorLocus H u q =
      {p : X × ℝ | ∀ i, H i p.1 = 0} ∩
        ({p : X × ℝ | ∀ i, 0 ≤ u i p.1} ∩ denominatorGraph q) by
    ext p
    simp [closedDenominatorLocus, denominatorGraph]]
  exact hHclosed.inter (huclosed.inter (isClosed_denominatorGraph q hq))

/-- A denominator locus is closed when its defining functions are continuous
only on a closed set containing the locus.  This is the form needed for
expression representatives whose regularity is known on a common jet
domain rather than on the whole ambient space. -/
theorem isClosed_closedDenominatorLocus_of_continuousOn
    [TopologicalSpace X]
    {r b : ℕ} (S : Set X) (hS : IsClosed S)
    (H : Fin r → X → ℝ) (u : Fin b → X → ℝ) (q : X → ℝ)
    (hH : ∀ i, ContinuousOn (H i) S)
    (hu : ∀ i, ContinuousOn (u i) S) (hq : ContinuousOn q S)
    (hsub : closedDenominatorLocus H u q ⊆ Prod.fst ⁻¹' S) :
    IsClosed (closedDenominatorLocus H u q) := by
  let P : Set (X × ℝ) := Prod.fst ⁻¹' S
  have hP : IsClosed P := hS.preimage continuous_fst
  have hfst : MapsTo (Prod.fst : X × ℝ → X) P S := by
    intro p hp
    exact hp
  have hHsingle : ∀ i, IsClosed
      (P ∩ {p : X × ℝ | H i p.1 = 0}) := by
    intro i
    have hcont : ContinuousOn (fun p : X × ℝ ↦ H i p.1) P :=
      (hH i).comp continuous_fst.continuousOn hfst
    rw [show P ∩ {p : X × ℝ | H i p.1 = 0} =
        P ∩ (fun p : X × ℝ ↦ H i p.1) ⁻¹' ({0} : Set ℝ) by
      ext p
      simp]
    exact hcont.preimage_isClosed_of_isClosed hP isClosed_singleton
  have hHclosed : IsClosed
      (P ∩ {p : X × ℝ | ∀ i, H i p.1 = 0}) := by
    have hclosed :
        IsClosed (P ∩ ⋂ i, (P ∩ {p : X × ℝ | H i p.1 = 0})) :=
      hP.inter (isClosed_iInter hHsingle)
    rw [show P ∩ {p : X × ℝ | ∀ i, H i p.1 = 0} =
        P ∩ ⋂ i, (P ∩ {p : X × ℝ | H i p.1 = 0}) by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hp, hall⟩
        exact ⟨hp, fun i ↦ ⟨hp, hall i⟩⟩
      · rintro ⟨hp, hall⟩
        exact ⟨hp, fun i ↦ (hall i).2⟩]
    exact hclosed
  have husingle : ∀ i, IsClosed
      (P ∩ {p : X × ℝ | 0 ≤ u i p.1}) := by
    intro i
    have hcont : ContinuousOn (fun p : X × ℝ ↦ u i p.1) P :=
      (hu i).comp continuous_fst.continuousOn hfst
    rw [show P ∩ {p : X × ℝ | 0 ≤ u i p.1} =
        P ∩ (fun p : X × ℝ ↦ u i p.1) ⁻¹' Set.Ici (0 : ℝ) by
      ext p
      simp]
    exact hcont.preimage_isClosed_of_isClosed hP isClosed_Ici
  have huclosed : IsClosed
      (P ∩ {p : X × ℝ | ∀ i, 0 ≤ u i p.1}) := by
    have hclosed :
        IsClosed (P ∩ ⋂ i, (P ∩ {p : X × ℝ | 0 ≤ u i p.1})) :=
      hP.inter (isClosed_iInter husingle)
    rw [show P ∩ {p : X × ℝ | ∀ i, 0 ≤ u i p.1} =
        P ∩ ⋂ i, (P ∩ {p : X × ℝ | 0 ≤ u i p.1}) by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hp, hall⟩
        exact ⟨hp, fun i ↦ ⟨hp, hall i⟩⟩
      · rintro ⟨hp, hall⟩
        exact ⟨hp, fun i ↦ (hall i).2⟩]
    exact hclosed
  have hqclosed : IsClosed
      (P ∩ {p : X × ℝ | p.2 * q p.1 = 1}) := by
    have hqcomp : ContinuousOn (fun p : X × ℝ ↦ q p.1) P :=
      hq.comp continuous_fst.continuousOn hfst
    have hcont : ContinuousOn (fun p : X × ℝ ↦ p.2 * q p.1) P :=
      continuous_snd.continuousOn.mul hqcomp
    rw [show P ∩ {p : X × ℝ | p.2 * q p.1 = 1} =
        P ∩ (fun p : X × ℝ ↦ p.2 * q p.1) ⁻¹' ({1} : Set ℝ) by
      ext p
      simp]
    exact hcont.preimage_isClosed_of_isClosed hP isClosed_singleton
  rw [show closedDenominatorLocus H u q =
      (P ∩ {p : X × ℝ | ∀ i, H i p.1 = 0}) ∩
        ((P ∩ {p : X × ℝ | ∀ i, 0 ≤ u i p.1}) ∩
          (P ∩ {p : X × ℝ | p.2 * q p.1 = 1})) by
    ext p
    constructor
    · intro hp
      have hpP : p ∈ P := hsub hp
      exact ⟨⟨hpP, hp.1⟩, ⟨⟨hpP, hp.2.1⟩, ⟨hpP, hp.2.2⟩⟩⟩
    · rintro ⟨⟨_, hH'⟩, ⟨⟨_, hu'⟩, ⟨_, hq'⟩⟩⟩
      exact ⟨hH', hu', hq'⟩]
  exact hHclosed.inter (huclosed.inter hqclosed)

/-- Multiplying the nonvanishing Jacobian factor by all boundary factors. -/
def boundaryDenominator {b : ℕ}
    (J : X → ℝ) (u : Fin b → X → ℝ) : X → ℝ :=
  fun x ↦ J x * ∏ i, u i x

theorem closedDenominatorLocus_boundary_strictPos
    {r b : ℕ} (H : Fin r → X → ℝ) (u : Fin b → X → ℝ)
    (J : X → ℝ) {p : X × ℝ}
    (hp : p ∈ closedDenominatorLocus H u (boundaryDenominator J u)) :
    (∀ i, 0 < u i p.1) ∧ J p.1 ≠ 0 := by
  have hq : boundaryDenominator J u p.1 ≠ 0 :=
    denominatorGraph_denominator_ne_zero (boundaryDenominator J u) hp.2.2
  have hmul : J p.1 ≠ 0 ∧ (∏ i, u i p.1) ≠ 0 := by
    simpa [boundaryDenominator] using mul_ne_zero_iff.mp hq
  refine ⟨fun i ↦ lt_of_le_of_ne (hp.2.1 i) ?_, hmul.1⟩
  exact Ne.symm (Finset.prod_ne_zero_iff.mp hmul.2 i (Finset.mem_univ i))

/-- A finite subset that meets every connected component gives a finite
connected-component quotient. -/
theorem finite_connectedComponents_of_finite_meetingSet
    [TopologicalSpace X] {C : Set X} (hC : C.Finite)
    (hmeet : ∀ x : X, ∃ c ∈ C, c ∈ connectedComponent x) :
    Finite (ConnectedComponents X) := by
  letI : Finite C := Set.finite_coe_iff.mpr hC
  let f : C → ConnectedComponents X := fun c ↦ (c.1 : ConnectedComponents X)
  apply Finite.of_surjective f
  intro component
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe component
  obtain ⟨c, hcC, hcx⟩ := hmeet x
  refine ⟨⟨c, hcC⟩, ?_⟩
  exact ConnectedComponents.coe_eq_coe'.2 hcx

/-- Points that minimize `f` on their own connected component. -/
def componentMinimizers [TopologicalSpace X] (f : X → ℝ) : Set X :=
  {x | IsMinOn f (connectedComponent x) x}

/-- Compact sublevel sets force a continuous real-valued function to attain a
minimum on every connected component. -/
theorem exists_componentMinimizer_of_compact_sublevel
    [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f)
    (hcompact : ∀ r : ℝ, IsCompact {x | f x ≤ r}) (x : X) :
    ∃ y ∈ connectedComponent x, y ∈ componentMinimizers f := by
  let S : Set X := connectedComponent x ∩ {y | f y ≤ f x}
  have hScompact : IsCompact S :=
    (hcompact (f x)).inter_left isClosed_connectedComponent
  have hxS : x ∈ S := by
    change x ∈ connectedComponent x ∩ {y | f y ≤ f x}
    refine ⟨mem_connectedComponent, ?_⟩
    exact le_refl (f x)
  obtain ⟨y, hyS, hymin⟩ :=
    hScompact.exists_isMinOn ⟨x, hxS⟩ (hf.continuousOn.mono inter_subset_right)
  refine ⟨y, hyS.1, ?_⟩
  have hcomponents : connectedComponent x = connectedComponent y :=
    connectedComponent_eq hyS.1
  change IsMinOn f (connectedComponent y) y
  rw [← hcomponents]
  intro z hz
  by_cases hzsub : f z ≤ f x
  · exact hymin ⟨hz, hzsub⟩
  · exact (hymin hxS).trans (le_of_not_ge hzsub)

theorem finite_connectedComponents_of_finite_componentMinimizers
    [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f)
    (hcompact : ∀ r : ℝ, IsCompact {x | f x ≤ r})
    (hfinite : (componentMinimizers f).Finite) :
    Finite (ConnectedComponents X) :=
  finite_connectedComponents_of_finite_meetingSet hfinite fun x ↦ by
    obtain ⟨y, hycomponent, hymin⟩ :=
      exists_componentMinimizer_of_compact_sublevel f hf hcompact x
    exact ⟨y, hymin, hycomponent⟩

/-- Squaring a nonnegative function does not change its minimizers on
connected components. -/
theorem componentMinimizers_sq_eq_of_nonneg
    [TopologicalSpace X] (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    componentMinimizers (fun x ↦ (f x) ^ 2) = componentMinimizers f := by
  ext x
  constructor
  · intro hx
    intro y hy
    exact (sq_le_sq₀ (hf x) (hf y)).mp (hx hy)
  · intro hx
    intro y hy
    exact (sq_le_sq₀ (hf x) (hf y)).mpr (hx hy)

/-- Squared distance to an ambient point. -/
def metricSquaredDistance [PseudoMetricSpace X] (c : X) : X → ℝ :=
  fun x ↦ dist x c ^ 2

@[fun_prop]
theorem continuous_metricSquaredDistance [PseudoMetricSpace X] (c : X) :
    Continuous (metricSquaredDistance c) :=
  (continuous_id.dist continuous_const).pow 2

/-- On a closed subset of a proper metric space, ambient-distance sublevels
are compact even when the center does not belong to the subset. -/
theorem isCompact_closedSet_distance_sublevel
    [PseudoMetricSpace X] [ProperSpace X] {M : Set X} (hM : IsClosed M)
    (c : X) (r : ℝ) :
    IsCompact {y : M | dist (y : X) c ≤ r} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [show ((↑) : M → X) '' {y : M | dist (y : X) c ≤ r} =
      M ∩ Metric.closedBall c r by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxM, hxball⟩
      exact ⟨⟨x, hxM⟩, hxball, rfl⟩]
  exact (isCompact_closedBall c r).inter_left hM

/-- The precise component-count conclusion used after the Morse step in the
manuscript.  Once the squared-distance minima on a closed locus form a finite
set, that locus has finitely many connected components. -/
theorem finite_connectedComponents_closedSet_of_finite_squaredDistanceMinimizers
    [PseudoMetricSpace X] [ProperSpace X] {M : Set X} (hM : IsClosed M)
    (c : X)
    (hfinite :
      (componentMinimizers (fun y : M ↦ metricSquaredDistance c (y : X))).Finite) :
    Finite (ConnectedComponents M) := by
  apply finite_connectedComponents_of_finite_componentMinimizers
    (fun y : M ↦ dist (y : X) c)
    (continuous_subtype_val.dist continuous_const)
    (isCompact_closedSet_distance_sublevel hM c)
  rw [← componentMinimizers_sq_eq_of_nonneg
    (fun y : M ↦ dist (y : X) c) (fun _ ↦ dist_nonneg)]
  simpa [metricSquaredDistance] using hfinite

/-- It is enough that a finite critical set contain every componentwise
squared-distance minimizer.  This separates the compactness argument from
the differential claim that minima are critical points. -/
theorem finite_connectedComponents_closedSet_of_finite_criticalSuperset
    [PseudoMetricSpace X] [ProperSpace X] {M : Set X} (hM : IsClosed M)
    (c : X) {critical : Set M} (hcritical : critical.Finite)
    (hminCritical :
      componentMinimizers (fun y : M ↦ metricSquaredDistance c (y : X)) ⊆ critical) :
    Finite (ConnectedComponents M) :=
  finite_connectedComponents_closedSet_of_finite_squaredDistanceMinimizers hM c
    (hcritical.subset hminCritical)

end AbelFormalization
