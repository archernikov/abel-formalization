import AbelFormalization.RestrictedAllUnboundedPairPullbackSequence
import AbelFormalization.RestrictedPairMergeExceptionalJetVerticalDerivative
import AbelFormalization.RegularZeroLinearEquiv
import Mathlib.Topology.Sequences

/-!
# A convergent exceptional-graph sequence in the pair branch

This module adjoins all exceptional fixed-iterate graph coordinates to the
lower-representative pair-merge sequence.  After one finite shift all graph
coordinates lie in their open boxes and the implicit graph theorem transports
the pair-merged regular zeros to the combined square system.  Compactness of
the enlarged closed box then supplies a convergent injective subsequence.
-/

noncomputable section

open Set Filter Function Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-! ## Product coordinates and the combined square system -/

/-- Unpack an enlarged restricted source into its pair-merge source and its
appended exceptional graph-coordinate vector. -/
def restrictedPairMergeExceptionalGraphProduct {m p a N : ℕ} :
    RestrictedSource (m + 1) ((p + 1) + N) a →
      RestrictedSource (m + 1) (p + 1) a × (Fin N → ℝ) :=
  fun z ↦
    (restrictedPairMergeExceptionalGraphDrop z,
      fun t ↦ z.1.2 (Fin.natAdd (p + 1) t))

@[simp]
theorem restrictedPairMergeExceptionalGraphProduct_lift
    {m p a N : ℕ}
    (eta : Fin N → RestrictedSource (m + 1) (p + 1) a → ℝ)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    restrictedPairMergeExceptionalGraphProduct
        (restrictedPairMergeExceptionalGraphLift eta x) =
      (x, fun t ↦ eta t x) := by
  ext <;> simp [restrictedPairMergeExceptionalGraphProduct]

/-- Linear equivalence between the flat enlarged restricted source and the
product coordinates of the finite implicit-graph theorem. -/
def restrictedPairMergeExceptionalGraphLinearEquiv {m p a N : ℕ} :
    RestrictedSource (m + 1) ((p + 1) + N) a ≃ₗ[ℝ]
      RestrictedSource (m + 1) (p + 1) a × (Fin N → ℝ) where
  toFun := restrictedPairMergeExceptionalGraphProduct
  invFun := fun z ↦
    ((z.1.1.1, Fin.addCases z.1.1.2 z.2), z.1.2)
  left_inv := by
    intro z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext r
        refine Fin.addCases (fun q ↦ ?_) (fun t ↦ ?_) r
        · simp [restrictedPairMergeExceptionalGraphProduct,
            restrictedPairMergeExceptionalGraphDrop]
        · simp [restrictedPairMergeExceptionalGraphProduct,
            restrictedPairMergeExceptionalGraphDrop]
    · rfl
  right_inv := by
    intro z
    ext r <;>
      simp [restrictedPairMergeExceptionalGraphProduct,
        restrictedPairMergeExceptionalGraphDrop]
  map_add' := by
    intro x y
    ext r <;>
      simp [restrictedPairMergeExceptionalGraphProduct,
        restrictedPairMergeExceptionalGraphDrop]
  map_smul' := by
    intro c x
    ext r <;>
      simp [restrictedPairMergeExceptionalGraphProduct,
        restrictedPairMergeExceptionalGraphDrop]

/-- Continuous-linear form of the flat/product graph-coordinate
identification.  Continuity follows from finite dimensionality. -/
def restrictedPairMergeExceptionalGraphContinuousLinearEquiv
    {m p a N : ℕ} :
    RestrictedSource (m + 1) ((p + 1) + N) a ≃L[ℝ]
      RestrictedSource (m + 1) (p + 1) a × (Fin N → ℝ) :=
  restrictedPairMergeExceptionalGraphLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem restrictedPairMergeExceptionalGraphContinuousLinearEquiv_apply
    {m p a N : ℕ}
    (z : RestrictedSource (m + 1) ((p + 1) + N) a) :
    restrictedPairMergeExceptionalGraphContinuousLinearEquiv z =
      restrictedPairMergeExceptionalGraphProduct z := rfl

/-- The pair-merged equations together with all exceptional graph equations,
in the product coordinates used by the finite implicit-graph theorem. -/
def restrictedPairMergeExceptionalCombinedSystem
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (M : Fin n → RestrictedSource (m + 1) (p + 1) a → ℝ) :
    (RestrictedSource (m + 1) (p + 1) a ×
        (Fin (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card → ℝ)) →
      ((Fin n → ℝ) ×
        (Fin (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card → ℝ)) :=
  finiteImplicitGraphLiftSystem
    (constraintMap M ∘ Prod.fst)
    (restrictedPairMergeExceptionalVectorGraphEquation
      D representative offset K k i j S)

/-- The combined open domain only restricts the underlying pair-merge source;
the graph equations themselves control the appended coordinates. -/
def restrictedPairMergeExceptionalCombinedDomain
    {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Set (RestrictedSource (m + 1) (p + 1) a ×
      (Fin (restrictedPairMergeExceptionalOffsetSupport
        representative i j S).card → ℝ)) :=
  (fun z ↦ z.1) ⁻¹' restrictedBaseOpenDomain (restrictedPairMergeBox D) R

/-- The combined graph domain transported to the flat enlarged restricted
source. -/
def restrictedPairMergeExceptionalFlatCombinedDomain
    {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Set (RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a) :=
  restrictedPairMergeExceptionalGraphContinuousLinearEquiv ⁻¹'
    restrictedPairMergeExceptionalCombinedDomain D R representative i j S

/-- The combined square system in flat enlarged restricted-source
coordinates. -/
def restrictedPairMergeExceptionalFlatCombinedSystem
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (M : Fin n → RestrictedSource (m + 1) (p + 1) a → ℝ) :
    RestrictedSource (m + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card) a →
      ((Fin n → ℝ) ×
        (Fin (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card → ℝ)) :=
  restrictedPairMergeExceptionalCombinedSystem
      D representative offset K k i j S M ∘
    restrictedPairMergeExceptionalGraphContinuousLinearEquiv

/-- Flat/product regular-zero equivalence for the combined graph system. -/
theorem mem_regularZeroSet_restrictedPairMergeExceptionalFlatCombinedSystem_iff
    {m p a n : ℕ} (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (M : Fin n → RestrictedSource (m + 1) (p + 1) a → ℝ)
    (z : RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a) :
    z ∈ regularZeroSet
        (restrictedPairMergeExceptionalFlatCombinedDomain
          D R representative i j S)
        (restrictedPairMergeExceptionalFlatCombinedSystem
          D representative offset K k i j S M) ↔
      restrictedPairMergeExceptionalGraphProduct z ∈
        regularZeroSet
          (restrictedPairMergeExceptionalCombinedDomain
            D R representative i j S)
          (restrictedPairMergeExceptionalCombinedSystem
            D representative offset K k i j S M) := by
  let e := restrictedPairMergeExceptionalGraphContinuousLinearEquiv
    (m := m) (p := p) (a := a)
    (N := (restrictedPairMergeExceptionalOffsetSupport
      representative i j S).card)
  let q := ContinuousLinearEquiv.refl ℝ
    ((Fin n → ℝ) ×
      (Fin (restrictedPairMergeExceptionalOffsetSupport
        representative i j S).card → ℝ))
  have hset := regularZeroSet_preimage_continuousLinearEquiv
    e q
    (restrictedPairMergeExceptionalCombinedDomain
      D R representative i j S)
    (restrictedPairMergeExceptionalCombinedSystem
      D representative offset K k i j S M)
  have hmem := Set.ext_iff.mp hset z
  have hfun :
      q ∘ restrictedPairMergeExceptionalCombinedSystem
          D representative offset K k i j S M ∘ e =
        restrictedPairMergeExceptionalCombinedSystem
          D representative offset K k i j S M ∘ e := by
    funext x
    rfl
  rw [hfun] at hmem
  simpa only [e, restrictedPairMergeExceptionalFlatCombinedDomain,
    restrictedPairMergeExceptionalFlatCombinedSystem,
    restrictedPairMergeExceptionalGraphContinuousLinearEquiv_apply,
    Function.comp_apply, Set.mem_preimage] using hmem

/-! ## Compact bounds and differentiability of the old system -/

/-- One analytic offset is uniformly bounded in absolute value on the compact
pair-merge closed box. -/
theorem exists_restrictedPairMergeExceptionalOldOffsetBound
    {p : ℕ} (D : RestrictedBox p)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (q : ι) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ w ∈ (restrictedPairMergeBox D).closedBox,
        |(restrictedPairMergeExceptionalOldOffset D offset q :
          RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B := by
  have hcont : ContinuousOn
      (fun w ↦ |(restrictedPairMergeExceptionalOldOffset D offset q :
        RestrictedBoxSpace (p + 1) → ℝ) w|)
      (restrictedPairMergeBox D).closedBox :=
    (((restrictedPairMergeBox D).analyticNearClosedBox_iff.mp
      (restrictedPairMergeExceptionalOldOffset D offset q).property).continuousOn).abs
  obtain ⟨C, hC⟩ :=
    (restrictedPairMergeBox D).isCompact_closedBox.bddAbove_image hcont
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro w hw
  exact (hC ⟨w, hw, rfl⟩).trans (le_max_left C 0)

private def pairGraphEmptyRestrictedExpressionTower
    {m p a : ℕ} (D : RestrictedBox p)
    (S : Set (RestrictedSource m p a → ℝ)) :
    RestrictedExpressionTower D S (ell := 0) where
  exponent := fun i ↦ Fin.elim0 i
  exponent_mem_level := fun i ↦ Fin.elim0 i

/-- The original equation map is differentiable at every point of the base
open domain under the same Abel-jet domain hypothesis used by the pullback
sequence theorem. -/
theorem IsAbel.differentiableAt_constraintMap_pairGraph_of_mem_base
    {A : ℝ → ℝ} (hA : IsAbel A) {ι : Type*} [Finite ι]
    {q p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin (q + 2))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := q + 2) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((q + 2) + p) + a) →
      RestrictedSource (q + 2) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    {x : RestrictedSource (q + 2) p a}
    (hx : x ∈ restrictedBaseOpenDomain D R) :
    DifferentiableAt ℝ (constraintMap F) x := by
  let T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := 0) :=
    pairGraphEmptyRestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
  have hxInterior : x ∈ interior
      (restrictedAbelJetDomain (a := a) D representative offset) :=
    restrictedBaseOpenDomain_subset_interior_AbelJetDomain
      D R representative offset hDomain hx
  have hcomponent : ∀ r, HasStrictFDerivAt (F r)
      (fderiv ℝ (F r) x) x := by
    intro r
    apply hA.hasStrictFDerivAt_of_mem_restrictedAbelTower_level_of_mem_interior
      representative offset T 0 (restrictedSourceBasis (q + 2) p a)
        (⟨0, by omega⟩ : Fin (((q + 2) + p) + a))
    · simpa only [T.level_zero] using hF r
    · exact hxInterior
  exact (hasStrictFDerivAt_constraintMap F x hcomponent).differentiableAt

/-! ## Generic finite-tail construction -/

/-- A pair-merged regular-zero sequence with an eventually differentiable
equation map and the simultaneous quantitative graph tail has an injective
exceptional-graph subsequence whose bounded coordinates converge in the
enlarged closed box.  Every selected point is a regular zero of the combined
square system. -/
theorem exists_restrictedPairMergeExceptionalGraphSubsequence
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport
      representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration
            representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (R : ℝ)
    (M : Fin n → RestrictedSource (m + 1) (p + 1) a → ℝ)
    (y : ℕ → RestrictedSource (m + 1) (p + 1) a)
    (hyinj : Function.Injective y)
    (hyrep : ∀ r, Tendsto (fun n ↦ (y n).1.1 r) atTop atTop)
    (hyregular : ∀ᶠ n in atTop,
      y n ∈ regularZeroSet
        (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
        (constraintMap M))
    (hydiff : ∀ᶠ n in atTop,
      DifferentiableAt ℝ (constraintMap M) (y n))
    (hytail : ∀ᶠ n in atTop, ∀ t,
      B t + 2 <
        restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration
            representative i j S t) (y n)) :
    ∃ (n₁ : ℕ)
      (w₁ : RestrictedBoxSpace
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card))
      (φ : ℕ → ℕ)
      (z : ℕ → RestrictedSource (m + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card) a),
      StrictMono φ ∧
      (∀ n, z n =
        restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S (y (n₁ + φ n))) ∧
      Function.Injective z ∧
      w₁ ∈ (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card).closedBox ∧
      Tendsto (fun n ↦ (z n).1.2) atTop (nhds w₁) ∧
      (∀ n, (z n).1.2 ∈
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card).openBox) ∧
      (∀ r, Tendsto (fun n ↦ (z n).1.1 r) atTop atTop) ∧
      ∀ n,
        z n ∈
          regularZeroSet
            (restrictedPairMergeExceptionalFlatCombinedDomain
              D R representative i j S)
            (restrictedPairMergeExceptionalFlatCombinedSystem
              D representative offset K k i j S M) := by
  have hall : ∀ᶠ n in atTop,
      y n ∈ regularZeroSet
          (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
          (constraintMap M) ∧
        DifferentiableAt ℝ (constraintMap M) (y n) ∧
        (∀ t, B t + 2 <
          restrictedPairMergeExceptionalBaseArgument representative i j
            (restrictedPairMergeExceptionalOffsetEnumeration
              representative i j S t) (y n)) := by
    filter_upwards [hyregular, hydiff, hytail] with n hn hdiff htail
    exact ⟨hn, hdiff, htail⟩
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hall
  let v : ℕ → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a :=
    fun n ↦ restrictedPairMergeExceptionalFiniteGraphLift
      D representative offset K k i j S (y (n₁ + n))
  have hvOpen : ∀ n, (v n).1.2 ∈
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card).openBox := by
    intro n
    have hn := hn₁ (n₁ + n) (Nat.le_add_right n₁ n)
    exact (restrictedPairMergeExceptionalFiniteGraphLift_spec
      D representative offset hK i j S B hB hbB (y (n₁ + n))
        hn.1.1.2 hn.2.2).1
  have hvClosed : ∀ n, (v n).1.2 ∈
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card).closedBox := fun n ↦
    (restrictedPairMergeExceptionalGraphBox D _).openBox_subset_closedBox
      (hvOpen n)
  obtain ⟨w₁, hw₁, φ, hφ, hφlim⟩ :=
    (restrictedPairMergeExceptionalGraphBox D
      (restrictedPairMergeExceptionalOffsetSupport
        representative i j S).card).isCompact_closedBox.tendsto_subseq
      hvClosed
  let z : ℕ → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a :=
    v ∘ φ
  have hzdef : ∀ n, z n =
      restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S (y (n₁ + φ n)) := by
    intro n
    rfl
  have hzinj : Function.Injective z := by
    intro r s hrs
    have hdrop := congrArg
      (restrictedPairMergeExceptionalGraphDrop
        (m := m) (p := p) (a := a)
        (N := (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card)) hrs
    simp only [z, v, Function.comp_apply,
      restrictedPairMergeExceptionalFiniteGraphLift,
      restrictedPairMergeExceptionalGraphDrop_lift] at hdrop
    have hindex : n₁ + φ r = n₁ + φ s := hyinj hdrop
    exact hφ.injective (Nat.add_left_cancel hindex)
  have hzrep : ∀ r, Tendsto (fun n ↦ (z n).1.1 r) atTop atTop := by
    intro r
    have hindex : Tendsto (fun n ↦ n₁ + φ n) atTop atTop := by
      have hadd : Tendsto (fun n : ℕ ↦ n₁ + n) atTop atTop := by
        simpa only [Nat.add_comm] using tendsto_add_atTop_nat n₁
      exact hadd.comp hφ.tendsto_atTop
    change Tendsto
      ((fun n ↦ (y n).1.1 r) ∘ (fun n ↦ n₁ + φ n)) atTop atTop
    exact (hyrep r).comp hindex
  have hzregular : ∀ n,
      z n ∈
        regularZeroSet
          (restrictedPairMergeExceptionalFlatCombinedDomain
            D R representative i j S)
          (restrictedPairMergeExceptionalFlatCombinedSystem
            D representative offset K k i j S M) := by
    intro n
    apply
      (mem_regularZeroSet_restrictedPairMergeExceptionalFlatCombinedSystem_iff
        D R representative offset K k i j S M (z n)).2
    have hn := hn₁ (n₁ + φ n) (Nat.le_add_right n₁ (φ n))
    let yn := y (n₁ + φ n)
    have hFtilde : DifferentiableAt ℝ
        ((constraintMap M) ∘
          (Prod.fst : RestrictedSource (m + 1) (p + 1) a ×
            (Fin (restrictedPairMergeExceptionalOffsetSupport
              representative i j S).card → ℝ) →
                RestrictedSource (m + 1) (p + 1) a))
        (yn, restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S yn) :=
      hn.2.1.comp
        (yn, restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S yn) differentiableAt_fst
    have hlift :=
      (mem_regularZeroSet_restrictedPairMergeExceptionalFiniteGraphLift_iff
        D representative offset hK i j S B hB hbB yn
          hn.1.1.2 hn.2.2 hFtilde).mp (by
            change yn ∈ regularZeroSet
              (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
              (constraintMap M)
            simpa only [yn] using hn.1)
    rw [hzdef n]
    change restrictedPairMergeExceptionalGraphProduct
      (restrictedPairMergeExceptionalGraphLift
        (restrictedPairMergeExceptionalGraphShift
          D representative offset K k i j S) (y (n₁ + φ n))) ∈ _
    rw [restrictedPairMergeExceptionalGraphProduct_lift]
    change
      (yn, restrictedPairMergeExceptionalVectorShift
        D representative offset K k i j S yn) ∈
          regularZeroSet
            ((fun z ↦ z.1) ⁻¹'
              restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
            (finiteImplicitGraphLiftSystem
              (constraintMap M ∘ Prod.fst)
              (restrictedPairMergeExceptionalVectorGraphEquation
                D representative offset K k i j S))
    exact hlift
  refine ⟨n₁, w₁, φ, z, hφ, hzdef, hzinj, hw₁, ?_, ?_, hzrep,
    hzregular⟩
  · change Tendsto ((fun n ↦ (v n).1.2) ∘ φ) atTop (nhds w₁)
    exact hφlim
  · exact fun n ↦ hvOpen (φ n)

/-! ## End-to-end assembly from the all-unbounded pair branch -/

/-- Starting from the selected `q+2` near-integer pair, first pull the
regular-zero sequence back to `q+1` representatives and then append all
exceptional graph coordinates.  The result is an injective sequence of
regular zeros of the flat combined square system, with every representative
still tending to `+∞` and all bounded coordinates converging in the enlarged
closed box. -/
theorem IsAbel.exists_restrictedPairMergeExceptionalGraphSequence_q_add_two
    {A : ℝ → ℝ} (hA : IsAbel A) {ι : Type*} [Finite ι]
    {q p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin (q + 2))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := q + 2) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((q + 2) + p) + a) →
      RestrictedSource (q + 2) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource (q + 2) p a)
    (w₀ : RestrictedBoxSpace p)
    (i j : Fin (q + 2)) {K k : ℕ} (hK : 1 ≤ K)
    (S : Finset (ι × ℕ))
    (hxinj : Function.Injective x)
    (hxmem : ∀ n, x n ∈
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F))
    (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀))
    (hxrep : ∀ r, Tendsto (fun n ↦ (x n).1.1 r) atTop atTop)
    (hij : i ≠ j)
    (hxi : Tendsto (fun n ↦
      L^[K + k] ((x n).1.1 i) - L^[K] ((x n).1.1 j))
      atTop (nhds 0)) :
    ∃ (j' : Fin (q + 1)) (n₀ : ℕ)
      (y : ℕ → RestrictedSource (q + 1) (p + 1) a)
      (B : Fin (restrictedPairMergeExceptionalOffsetSupport
        representative i j' S).card → ℝ)
      (n₁ : ℕ)
      (w₁ : RestrictedBoxSpace
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j' S).card))
      (φ : ℕ → ℕ)
      (z : ℕ → RestrictedSource (q + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j' S).card) a),
      i.succAbove j' = j ∧
      (∀ n, y n =
        restrictedPairMergePullback K k i j' (x (n₀ + n))) ∧
      (∀ t, 0 ≤ B t) ∧
      (∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
        |(restrictedPairMergeExceptionalOldOffset D offset
            (restrictedPairMergeExceptionalOffsetEnumeration
              representative i j' S t) :
          RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t) ∧
      StrictMono φ ∧
      (∀ n, z n =
        restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j' S (y (n₁ + φ n))) ∧
      Function.Injective z ∧
      w₁ ∈ (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j' S).card).closedBox ∧
      Tendsto (fun n ↦ (z n).1.2) atTop (nhds w₁) ∧
      (∀ n, (z n).1.2 ∈
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j' S).card).openBox) ∧
      (∀ r, Tendsto (fun n ↦ (z n).1.1 r) atTop atTop) ∧
      ∀ n, z n ∈ regularZeroSet
        (restrictedPairMergeExceptionalFlatCombinedDomain
          D R representative i j' S)
        (restrictedPairMergeExceptionalFlatCombinedSystem
          D representative offset K k i j' S
            (restrictedPairMergedEquationFamily K k i j' F)) := by
  obtain ⟨j', n₀, y, hj', hydef, hyinj, _hyclosed, hylim, hyrep,
      _hydomain, hyregular⟩ :=
    hA.exists_restrictedPairMergePullbackSequence_q_add_two
      D representative offset R hDomain F hF x w₀ i j K k hxinj hxmem
        hw₀ hxlim hxrep hij hxi
  have hbound : ∀ t : Fin (restrictedPairMergeExceptionalOffsetSupport
      representative i j' S).card,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ (restrictedPairMergeBox D).closedBox,
          |(restrictedPairMergeExceptionalOldOffset D offset
              (restrictedPairMergeExceptionalOffsetEnumeration
                representative i j' S t) :
            RestrictedBoxSpace (p + 1) → ℝ) w| ≤ C := by
    intro t
    exact exists_restrictedPairMergeExceptionalOldOffsetBound D offset _
  choose B hB hbB using hbound
  have hlast : Tendsto (fun n ↦ (y n).1.2 (Fin.last p)) atTop
      (nhds 0) := by
    simpa using tendsto_pi_nhds.mp hylim (Fin.last p)
  have hbase : ∀ t : Fin (restrictedPairMergeExceptionalOffsetSupport
      representative i j' S).card,
      Tendsto
        (fun n ↦ restrictedPairMergeExceptionalBaseArgument
          representative i j'
            (restrictedPairMergeExceptionalOffsetEnumeration
              representative i j' S t) (y n)) atTop atTop := by
    intro t
    unfold restrictedPairMergeExceptionalBaseArgument
    split
    · exact (hyrep j').atTop_add hlast
    · exact hyrep j'
  have hytail : ∀ᶠ n in atTop,
      ∀ t : Fin (restrictedPairMergeExceptionalOffsetSupport
        representative i j' S).card,
        B t + 2 <
          restrictedPairMergeExceptionalBaseArgument representative i j'
            (restrictedPairMergeExceptionalOffsetEnumeration
              representative i j' S t) (y n) := by
    exact Filter.eventually_all.mpr fun t ↦
      (hbase t).eventually (eventually_gt_atTop (B t + 2))
  have holdDiff : ∀ n, DifferentiableAt ℝ (constraintMap F) (x n) := by
    intro n
    exact hA.differentiableAt_constraintMap_pairGraph_of_mem_base
      D representative offset R hDomain F hF (hxmem n).1
  let shift : ℕ → ℕ := fun n ↦ n₀ + n
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat n₀
  have hxiPos : ∀ᶠ n in atTop, 0 < (x (shift n)).1.1 i :=
    ((hxrep i).comp hshift).eventually (eventually_gt_atTop 0)
  have hxjPos : ∀ᶠ n in atTop,
      0 < (x (shift n)).1.1 (i.succAbove j') :=
    ((hxrep (i.succAbove j')).comp hshift).eventually
      (eventually_gt_atTop 0)
  have hydiff : ∀ᶠ n in atTop,
      DifferentiableAt ℝ
        (constraintMap (restrictedPairMergedEquationFamily K k i j' F))
        (y n) := by
    filter_upwards [hxiPos, hxjPos] with n hin hjn
    have hsource : restrictedPairMergeSourceMap K k i j' (y n) =
        x (shift n) := by
      rw [hydef n]
      exact restrictedPairMergeSourceMap_pullback K k i j'
        (x (shift n)) hin hjn
    have holdAt : DifferentiableAt ℝ (constraintMap F)
        (restrictedPairMergeSourceMap K k i j' (y n)) := by
      simpa only [hsource] using holdDiff (shift n)
    have hsourceDiff : DifferentiableAt ℝ
        (restrictedPairMergeSourceMap K k i j') (y n) :=
      ((contDiff_restrictedPairMergeSourceMap
        (p := p) (a := a) K k i j').differentiable
          (by simp)).differentiableAt
    have hmiddle : DifferentiableAt ℝ
        ((constraintMap F) ∘ restrictedPairMergeSourceMap K k i j')
        (y n) :=
      holdAt.comp (y n) hsourceDiff
    rw [constraintMap_restrictedPairMergedEquationFamily]
    exact (restrictedReclassificationTargetEquiv
      (q + 1) p a).differentiableAt.comp (y n) hmiddle
  obtain ⟨n₁, w₁, φ, z, hφ, hzdef, hzinj, hw₁, hzlim, hzopen,
      hzrep, hzregular⟩ :=
    exists_restrictedPairMergeExceptionalGraphSubsequence
      D representative offset hK i j' S B hB hbB R
        (restrictedPairMergedEquationFamily K k i j' F)
        y hyinj hyrep hyregular hydiff hytail
  exact ⟨j', n₀, y, B, n₁, w₁, φ, z, hj', hydef, hB, hbB,
    hφ, hzdef, hzinj, hw₁, hzlim, hzopen, hzrep, hzregular⟩

end AbelFormalization
