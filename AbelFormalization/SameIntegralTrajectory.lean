import AbelFormalization.RolleComponentUniqueness
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Scratch: gluing ambient ODE trajectories

This file is an uncompiled proof sketch.  It isolates the relation that would be
useful for replacing the `RegularArcIn` hypothesis by an ambient ODE argument.

The intended vector field is autonomous.  A witness is allowed to live on any
open interval and records two (unordered) times in that interval.  This choice
makes symmetry free.  Transitivity translates the second solution so that the
two witnesses agree at the common point, invokes ODE uniqueness on the overlap,
and glues them with `Set.piecewise`.
-/


noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : E → E} {M : Set E}

/-- Specialization of mathlib's uniqueness theorem to an autonomous vector
field on an open interval. -/
theorem autonomous_ODE_solution_unique_of_mem_Ioo
    {K : NNReal} (hV : LipschitzWith K V)
    {a b t₀ : ℝ} {γ δ : ℝ → E}
    (ht₀ : t₀ ∈ Ioo a b)
    (hγ : IsIntegralCurveOn γ (fun _ ↦ V) (Ioo a b))
    (hδ : IsIntegralCurveOn δ (fun _ ↦ V) (Ioo a b))
    (heq : γ t₀ = δ t₀) :
    EqOn γ δ (Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun _ ↦ V) (s := fun _ ↦ (Set.univ : Set E)) (K := K)
    (fun _ _ ↦ hV.lipschitzOnWith) ht₀
  · intro t ht
    exact ⟨(hγ t ht).hasDerivAt (Ioo_mem_nhds ht.1 ht.2), mem_univ _⟩
  · intro t ht
    exact ⟨(hδ t ht).hasDerivAt (Ioo_mem_nhds ht.1 ht.2), mem_univ _⟩
  · exact heq

/-- Local uniqueness under the natural `C¹` hypothesis.  This packages
`ContDiffAt.exists_lipschitzOnWith` with
`ODE_solution_unique_of_eventually`. -/
theorem isIntegralCurveAt_eventuallyEq_of_contDiffAt
    {t₀ : ℝ} {γ δ : ℝ → E}
    (hV : ContDiffAt ℝ 1 V (γ t₀))
    (hγ : IsIntegralCurveAt γ (fun _ ↦ V) t₀)
    (hδ : IsIntegralCurveAt δ (fun _ ↦ V) t₀)
    (heq : γ t₀ = δ t₀) :
    γ =ᶠ[𝓝 t₀] δ := by
  obtain ⟨K, s, hs, hVs⟩ := hV.exists_lipschitzOnWith
  have hsδ : s ∈ 𝓝 (δ t₀) := by simpa only [← heq] using hs
  apply ODE_solution_unique_of_eventually
    (v := fun _ ↦ V) (s := fun _ ↦ s) (K := K)
    (Filter.Eventually.of_forall fun _ ↦ hVs)
    (hγ.and (hγ.continuousAt hs))
    (hδ.and (hδ.continuousAt hsδ)) heq

/-- Integral curves of an autonomous `C¹` vector field are unique on an open
interval.  The proof globalizes the preceding local uniqueness because an
open interval is preconnected.  This is the ambient normed-space analogue of
`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`. -/
theorem isIntegralCurveOn_Ioo_eqOn_of_contDiff
    (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    {a b t₀ : ℝ} {γ δ : ℝ → E}
    (ht₀ : t₀ ∈ Ioo a b)
    (hγ : IsIntegralCurveOn γ (fun _ ↦ V) (Ioo a b))
    (hδ : IsIntegralCurveOn δ (fun _ ↦ V) (Ioo a b))
    (hγM : MapsTo γ (Ioo a b) M)
    (hδM : MapsTo δ (Ioo a b) M)
    (heq : γ t₀ = δ t₀) :
    EqOn γ δ (Ioo a b) := by
  set s := {t | γ t = δ t} ∩ Ioo a b with hs
  suffices hsub : Ioo a b ⊆ s from
    fun t ht ↦ (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset
    (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm,
      ← Subtype.image_preimage_val, image_subset_image_iff Subtype.val_injective,
      preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hγ.continuousWithinAt ht |>.continuousAt
        (Ioo_mem_nhds ht.1 ht.2)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hδ.continuousWithinAt ht |>.continuousAt
        (Ioo_mem_nhds ht.1 ht.2)
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have hlocal : γ =ᶠ[𝓝 t] δ :=
      isIntegralCurveAt_eventuallyEq_of_contDiffAt (hV (γ t) (hγM ht.2))
        (hγ.isIntegralCurveAt hmem) (hδ.isIntegralCurveAt hmem) ht.1
    apply (hlocal.and hmem).mono
    exact fun _ hu ↦ hu

/-- On the second interval, the piecewise extension is equal to the second
solution.  On the overlap this is ODE uniqueness; off the first interval it is
true by definition. -/
theorem eqOn_piecewise_of_isIntegralCurveOn_Ioo
    (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    {a b a' b' t₀ : ℝ} {γ δ : ℝ → E}
    (hγ : IsIntegralCurveOn γ (fun _ ↦ V) (Ioo a b))
    (hδ : IsIntegralCurveOn δ (fun _ ↦ V) (Ioo a' b'))
    (hγM : MapsTo γ (Ioo a b) M)
    (hδM : MapsTo δ (Ioo a' b') M)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b')
    (heq : γ t₀ = δ t₀) :
    EqOn (piecewise (Ioo a b) γ δ) δ (Ioo a' b') := by
  intro t ht
  suffices hover : EqOn γ δ (Ioo (max a a') (min b b')) by
    by_cases hmem : t ∈ Ioo a b
    · rw [piecewise, if_pos hmem]
      apply hover
      exact ⟨max_lt hmem.1 ht.1, lt_min hmem.2 ht.2⟩
    · rw [piecewise, if_neg hmem]
  apply isIntegralCurveOn_Ioo_eqOn_of_contDiff hV
  · exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
  · exact hγ.mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _))
  · exact hδ.mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _))
  · intro t ht
    exact hγM (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _) ht)
  · intro t ht
    exact hδM (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _) ht)
  · exact heq

/-- Two autonomous integral curves on overlapping open intervals glue to an
integral curve on their union.  This is the normed-space analogue of
`isMIntegralCurveOn_piecewise` in
`Mathlib.Geometry.Manifold.IntegralCurve.UniformTime`. -/
theorem isIntegralCurveOn_piecewise_Ioo
    (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    {a b a' b' t₀ : ℝ} {γ δ : ℝ → E}
    (hγ : IsIntegralCurveOn γ (fun _ ↦ V) (Ioo a b))
    (hδ : IsIntegralCurveOn δ (fun _ ↦ V) (Ioo a' b'))
    (hγM : MapsTo γ (Ioo a b) M)
    (hδM : MapsTo δ (Ioo a' b') M)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b')
    (heq : γ t₀ = δ t₀) :
    IsIntegralCurveOn (piecewise (Ioo a b) γ δ) (fun _ ↦ V)
      (Ioo a b ∪ Ioo a' b') := by
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, if_pos hmem]
    apply (hγ t hmem).hasDerivAt (Ioo_mem_nhds hmem.1 hmem.2)
      |>.hasDerivWithinAt (s := Ioo a b ∪ Ioo a' b')
      |>.congr_of_eventuallyEq _ (by rw [piecewise, if_pos hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, ?_, fun _ hu ↦ by rw [piecewise, if_pos hu]⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht]
    exact Ioo_mem_nhds hmem.1 hmem.2
  · have ht' := ht
    rw [mem_union, or_iff_not_imp_left] at ht
    rw [piecewise, if_neg hmem]
    apply (hδ t (ht hmem)).hasDerivAt
      (Ioo_mem_nhds (ht hmem).1 (ht hmem).2)
      |>.hasDerivWithinAt (s := Ioo a b ∪ Ioo a' b')
      |>.congr_of_eventuallyEq _ (by rw [piecewise, if_neg hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a' b', ?_,
      eqOn_piecewise_of_isIntegralCurveOn_Ioo
        hV hγ hδ hγM hδM ht₀ heq⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht']
    exact Ioo_mem_nhds (ht hmem).1 (ht hmem).2

/-- Two points lie on the same local integral trajectory inside `M` when one
integral curve, defined on an open interval, passes through both and remains in
`M` on that interval.  The two marked times are deliberately unordered. -/
structure SameIntegralTrajectoryIn (V : E → E) (M : Set E) (x y : E) where
  lower : ℝ
  upper : ℝ
  sourceTime : ℝ
  targetTime : ℝ
  curve : ℝ → E
  sourceTime_mem : sourceTime ∈ Ioo lower upper
  targetTime_mem : targetTime ∈ Ioo lower upper
  source_eq : curve sourceTime = x
  target_eq : curve targetTime = y
  isIntegral : IsIntegralCurveOn curve (fun _ ↦ V) (Ioo lower upper)
  curve_mem : MapsTo curve (Ioo lower upper) M

namespace SameIntegralTrajectoryIn

def symm {x y : E} (h : SameIntegralTrajectoryIn V M x y) :
    SameIntegralTrajectoryIn V M y x where
  lower := h.lower
  upper := h.upper
  sourceTime := h.targetTime
  targetTime := h.sourceTime
  curve := h.curve
  sourceTime_mem := h.targetTime_mem
  targetTime_mem := h.sourceTime_mem
  source_eq := h.target_eq
  target_eq := h.source_eq
  isIntegral := h.isIntegral
  curve_mem := h.curve_mem

/-- A local integral curve through `x` supplies reflexivity.  Local ODE
existence gives the curve; preservation of the constraint supplies `curve_mem`.
-/
def refl_of_local_curve {x : E} {a b : ℝ} {γ : ℝ → E}
    (h0 : 0 ∈ Ioo a b) (hγ0 : γ 0 = x)
    (hγ : IsIntegralCurveOn γ (fun _ ↦ V) (Ioo a b))
    (hγM : MapsTo γ (Ioo a b) M) :
    SameIntegralTrajectoryIn V M x x where
  lower := a
  upper := b
  sourceTime := 0
  targetTime := 0
  curve := γ
  sourceTime_mem := h0
  targetTime_mem := h0
  source_eq := hγ0
  target_eq := hγ0
  isIntegral := hγ
  curve_mem := hγM

/-- Transitivity follows by translating the second curve to align the two
occurrences of `y`, then applying the preceding uniqueness/gluing lemmas. -/
def trans (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    {x y z : E} (hxy : SameIntegralTrajectoryIn V M x y)
    (hyz : SameIntegralTrajectoryIn V M y z) :
    SameIntegralTrajectoryIn V M x z := by
  let dt : ℝ := hyz.sourceTime - hxy.targetTime
  let δ : ℝ → E := fun t ↦ hyz.curve (t + dt)
  let a' : ℝ := hyz.lower - dt
  let b' : ℝ := hyz.upper - dt
  have hδ : IsIntegralCurveOn δ (fun _ ↦ V) (Ioo a' b') := by
    intro t ht
    have ht' : t + dt ∈ Ioo hyz.lower hyz.upper := by
      dsimp [a', b'] at ht
      exact ⟨(sub_lt_iff_lt_add.mp ht.1),
        (lt_sub_iff_add_lt.mp ht.2)⟩
    have hd := (hyz.isIntegral (t + dt) ht').hasDerivAt
      (Ioo_mem_nhds ht'.1 ht'.2)
    simpa [δ] using (hd.comp_add_const t dt).hasDerivWithinAt
  have hδM : MapsTo δ (Ioo a' b') M := by
    intro t ht
    apply hyz.curve_mem
    dsimp [a', b'] at ht
    exact ⟨(sub_lt_iff_lt_add.mp ht.1),
      (lt_sub_iff_add_lt.mp ht.2)⟩
  have halign_mem : hxy.targetTime ∈
      Ioo hxy.lower hxy.upper ∩ Ioo a' b' := by
    refine ⟨hxy.targetTime_mem, ?_⟩
    dsimp [a', b', dt]
    constructor <;> linarith [hyz.sourceTime_mem.1, hyz.sourceTime_mem.2]
  have halign : hxy.curve hxy.targetTime = δ hxy.targetTime := by
    rw [hxy.target_eq]
    calc
      y = hyz.curve hyz.sourceTime := hyz.source_eq.symm
      _ = δ hxy.targetTime := by
        dsimp [δ, dt]
        congr 1
        ring
  let η : ℝ → E := piecewise (Ioo hxy.lower hxy.upper) hxy.curve δ
  have hη : IsIntegralCurveOn η (fun _ ↦ V)
      (Ioo hxy.lower hxy.upper ∪ Ioo a' b') := by
    exact isIntegralCurveOn_piecewise_Ioo hV hxy.isIntegral hδ
      hxy.curve_mem hδM halign_mem halign
  have hη_eq_δ : EqOn η δ (Ioo a' b') := by
    exact eqOn_piecewise_of_isIntegralCurveOn_Ioo
      hV hxy.isIntegral hδ hxy.curve_mem hδM halign_mem halign
  have ha'lt : a' < hxy.upper := by
    exact lt_trans halign_mem.2.1 hxy.targetTime_mem.2
  have hlowerlt : hxy.lower < b' := by
    exact lt_trans hxy.targetTime_mem.1 halign_mem.2.2
  have hunion : Ioo hxy.lower hxy.upper ∪ Ioo a' b' =
      Ioo (min hxy.lower a') (max hxy.upper b') :=
    Ioo_union_Ioo' ha'lt hlowerlt
  let zTime : ℝ := hyz.targetTime - dt
  have hzTime_mem : zTime ∈ Ioo a' b' := by
    dsimp [zTime, a', b']
    constructor <;> linarith [hyz.targetTime_mem.1, hyz.targetTime_mem.2]
  have hηM : MapsTo η
      (Ioo (min hxy.lower a') (max hxy.upper b')) M := by
    rw [← hunion]
    intro t ht
    rcases ht with ht | ht
    · simpa only [η, piecewise, if_pos ht] using hxy.curve_mem ht
    · by_cases hfirst : t ∈ Ioo hxy.lower hxy.upper
      · simpa only [η, piecewise, if_pos hfirst] using
          hxy.curve_mem hfirst
      · simpa only [η, piecewise, if_neg hfirst] using hδM ht
  refine
    { lower := min hxy.lower a'
      upper := max hxy.upper b'
      sourceTime := hxy.sourceTime
      targetTime := zTime
      curve := η
      sourceTime_mem := ?_
      targetTime_mem := ?_
      source_eq := ?_
      target_eq := ?_
      isIntegral := ?_
      curve_mem := hηM }
  · rw [← hunion]
    exact Or.inl hxy.sourceTime_mem
  · rw [← hunion]
    exact Or.inr hzTime_mem
  · simpa only [η, piecewise, if_pos hxy.sourceTime_mem] using
      hxy.source_eq
  · calc
      η zTime = δ zTime := hη_eq_δ hzTime_mem
      _ = hyz.curve hyz.targetTime := by
        dsimp [δ, zTime, dt]
        congr 1
        ring
      _ = z := hyz.target_eq
  · rwa [← hunion]

/-- A same-trajectory witness with distinct endpoints is already a
`RegularArcIn`: order its two marked times, and reverse the parameter in the
second case. -/
theorem regularArcIn {x y : E} (h : SameIntegralTrajectoryIn V M x y)
    (hVne : ∀ z ∈ M, V z ≠ 0) (hxy : x ≠ y) :
    RegularArcIn M x y := by
  have htime : h.sourceTime ≠ h.targetTime := by
    intro heq
    apply hxy
    calc
      x = h.curve h.sourceTime := h.source_eq.symm
      _ = h.curve h.targetTime := congrArg h.curve heq
      _ = y := h.target_eq
  rcases lt_or_gt_of_ne htime with hst | hts
  · let vel : ℝ → E := fun t ↦ V (h.curve t)
    have hIcc : Icc h.sourceTime h.targetTime ⊆ Ioo h.lower h.upper := by
      intro t ht
      exact ⟨lt_of_lt_of_le h.sourceTime_mem.1 ht.1,
        lt_of_le_of_lt ht.2 h.targetTime_mem.2⟩
    have hder : ∀ t ∈ Icc h.sourceTime h.targetTime,
        HasDerivAt h.curve (vel t) t := by
      intro t ht
      exact (h.isIntegral t (hIcc ht)).hasDerivAt
        (Ioo_mem_nhds (hIcc ht).1 (hIcc ht).2)
    refine ⟨h.sourceTime, h.targetTime, h.curve, vel, hst,
      h.source_eq, h.target_eq, HasDerivAt.continuousOn hder,
      fun t ht ↦ h.curve_mem (hIcc ht), ?_⟩
    intro t ht
    have ht' := hIcc (Ioo_subset_Icc_self ht)
    exact ⟨hder t (Ioo_subset_Icc_self ht),
      hVne (h.curve t) (h.curve_mem ht')⟩
  · let rev : ℝ → E := fun t ↦ h.curve (h.sourceTime + h.targetTime - t)
    let vel : ℝ → E := fun t ↦ -V (rev t)
    have hrevTime (t : ℝ) (ht : t ∈ Icc h.targetTime h.sourceTime) :
        h.sourceTime + h.targetTime - t ∈ Ioo h.lower h.upper := by
      constructor
      · calc
          h.lower < h.targetTime := h.targetTime_mem.1
          _ ≤ h.sourceTime + h.targetTime - t := by
            linarith only [ht.2]
      · calc
          h.sourceTime + h.targetTime - t ≤ h.sourceTime := by
            linarith only [ht.1]
          _ < h.upper := h.sourceTime_mem.2
    have hder : ∀ t ∈ Icc h.targetTime h.sourceTime,
        HasDerivAt rev (vel t) t := by
      intro t ht
      have hu := hrevTime t ht
      have hd := (h.isIntegral _ hu).hasDerivAt
        (Ioo_mem_nhds hu.1 hu.2)
      simpa [rev, vel] using
        hd.comp_const_sub (h.sourceTime + h.targetTime) t
    refine ⟨h.targetTime, h.sourceTime, rev, vel, hts,
      ?_, ?_, HasDerivAt.continuousOn hder, ?_, ?_⟩
    · simpa [rev] using h.source_eq
    · simpa [rev] using h.target_eq
    · intro t ht
      exact h.curve_mem (hrevTime t ht)
    · intro t ht
      have htIcc := Ioo_subset_Icc_self ht
      have hmem := h.curve_mem (hrevTime t htIcc)
      exact ⟨hder t htIcc, neg_ne_zero.mpr (hVne (rev t) (by simpa [rev] using hmem))⟩

end SameIntegralTrajectoryIn

/-- The trajectory class of `x`, viewed in the subtype `M`. -/
def trajectoryClass (V : E → E) (M : Set E) (x : M) : Set M :=
  {y | Nonempty (SameIntegralTrajectoryIn V M x y)}

/-- If every point has a trajectory neighborhood in `M`, then trajectory
classes are clopen.  This is the topological globalisation step used to pass
from local flow boxes to connected components. -/
theorem isClopen_trajectoryClass
    (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    (hrefl : ∀ x : M, Nonempty (SameIntegralTrajectoryIn V M x x))
    (hlocal : ∀ x : M, trajectoryClass V M x ∈ 𝓝 x)
    (x : M) : IsClopen (trajectoryClass V M x) := by
  have hopen : IsOpen (trajectoryClass V M x) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hlocal y] with z hyz
    rcases hy with ⟨hy⟩
    rcases hyz with ⟨hyz⟩
    exact ⟨SameIntegralTrajectoryIn.trans hV hy hyz⟩
  have hopen_compl : IsOpen (trajectoryClass V M x)ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hlocal y] with z hyz
    change ¬Nonempty (SameIntegralTrajectoryIn V M x z)
    intro hxz
    rcases hxz with ⟨hxz⟩
    rcases hyz with ⟨hyz⟩
    apply hy
    exact ⟨SameIntegralTrajectoryIn.trans hV hxz hyz.symm⟩
  exact ⟨isOpen_compl_iff.mp hopen_compl, hopen⟩

/-- Local trajectory neighborhoods plus connectedness put every point of a
connected component on the same trajectory. -/
theorem sameIntegralTrajectoryIn_of_mem_connectedComponent
    (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    (hrefl : ∀ x : M, Nonempty (SameIntegralTrajectoryIn V M x x))
    (hlocal : ∀ x : M, trajectoryClass V M x ∈ 𝓝 x)
    (x y : M) (hy : y ∈ connectedComponent x) :
    Nonempty (SameIntegralTrajectoryIn V M x y) := by
  have hclopen := isClopen_trajectoryClass hV hrefl hlocal x
  apply hclopen.connectedComponent_subset
  · exact hrefl x
  · exact hy

/-- Candidate end product for the geometric input expected by
`eq_of_mem_connectedComponent_of_regularArcs`. -/
theorem regularArcIn_of_mem_connectedComponent
    (hV : ∀ z ∈ M, ContDiffAt ℝ 1 V z)
    (hVne : ∀ z ∈ M, V z ≠ 0)
    (hrefl : ∀ x : M, Nonempty (SameIntegralTrajectoryIn V M x x))
    (hlocal : ∀ x : M, trajectoryClass V M x ∈ 𝓝 x)
    (x y : M) (hy : y ∈ connectedComponent x) (hxy : x ≠ y) :
    RegularArcIn M x y := by
  obtain ⟨htraj⟩ :=
    sameIntegralTrajectoryIn_of_mem_connectedComponent hV hrefl hlocal x y hy
  apply SameIntegralTrajectoryIn.regularArcIn
    htraj hVne
  exact fun h ↦ hxy (Subtype.ext h)

end AbelFormalization
