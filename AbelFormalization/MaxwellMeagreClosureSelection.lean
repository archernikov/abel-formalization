import AbelFormalization.KuratowskiUlamProduct
import AbelFormalization.MaxwellMeagreClosureFamilyEquivalence
import AbelFormalization.MaxwellLocalFiberCardinality
import AbelFormalization.ReciprocalConstraintGraph

/-!
# Maxwell meagre closure selection

This file proves the family-geometric step left open in
`CharbonnelClosureInteriorRegularity`.  The proof follows the source's
dimension induction.  Kuratowski--Ulam supplies a vertical line on which a
meagre set remains meagre.  Lower-dimensional closure regularity makes the
projections of finitely many disjoint vertical slabs simultaneously large,
and the resulting fiber points lie in distinct connected components.
-/

noncomputable section

open Filter Set Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Elementary category and finite-intersection lemmas -/

/-- A meagre subset of the real line is totally disconnected. -/
theorem IsMeagre.isTotallyDisconnected_real
    {A : Set ℝ} (hA : IsMeagre A) :
    IsTotallyDisconnected A := by
  rw [isTotallyDisconnected_iff_lt]
  intro x hx y hy hxy
  by_contra hnone
  have hsub : Set.Ioo x y ⊆ A := by
    intro z hz
    by_contra hzA
    exact hnone ⟨z, hzA, hz⟩
  have hmeagre : IsMeagre (Set.Ioo x y) := hA.mono hsub
  exact not_isMeagre_of_isOpen isOpen_Ioo (Set.nonempty_Ioo.mpr hxy) hmeagre

/-- Under closure-interior regularity, finitely many family members whose
closures contain one nonempty open set have a common nonempty open part.
Only polynomial-sign balls and binary intersections are used in the
localization. -/
theorem exists_open_common_subset_of_closures
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n k : ℕ} (hn : 0 < n)
    (hregularity : MaxwellClosureInteriorRegularityAt C n)
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (P : Fin k → Set (RealEuclidean n))
    (hPmem : ∀ i, P i ∈ C n)
    (hUclosure : ∀ i, U ⊆ closure (P i)) :
    ∃ W : Set (RealEuclidean n),
      IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧ W ⊆ ⋂ i, P i := by
  classical
  have aux : ∀ s : Finset (Fin k),
      ∃ W : Set (RealEuclidean n),
        IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧
          ∀ i ∈ s, W ⊆ P i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨U, hUopen, hUnonempty, Subset.rfl, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨W, hWopen, hWnonempty, hWU, hWs⟩ := ih
        obtain ⟨x, hxW⟩ := hWnonempty
        obtain ⟨r, hr, hballW⟩ := Metric.isOpen_iff.mp hWopen x hxW
        let B : Set (RealEuclidean n) := Metric.ball x r
        have hBopen : IsOpen B := Metric.isOpen_ball
        have hBnonempty : B.Nonempty := ⟨x, Metric.mem_ball_self hr⟩
        have hBmem : B ∈ C n :=
          hC.ws2_polynomialSign hn (polynomialSignConstructible_ball x hr)
        let Q : Set (RealEuclidean n) := P i ∩ B
        have hQmem : Q ∈ C n := hC.ws1_inter hn (hPmem i) hBmem
        have hBclosure : B ⊆ closure Q := by
          intro y hy
          have hyClosureP : y ∈ closure (P i) :=
            hUclosure i (hWU (hballW hy))
          have hy' : y ∈ B ∩ closure (P i) := ⟨hy, hyClosureP⟩
          have := hBopen.inter_closure hy'
          simpa only [Q, inter_comm] using this
        have hclosureNonempty : (interior (closure Q)).Nonempty := by
          exact hBnonempty.mono
            (hBopen.subset_interior_iff.mpr hBclosure)
        have hQinterior : interior Q ≠ ∅ := by
          intro hQempty
          have := hregularity hQmem hQempty
          rw [this] at hclosureNonempty
          exact hclosureNonempty.ne_empty rfl
        refine ⟨interior Q, isOpen_interior,
          Set.nonempty_iff_ne_empty.mpr hQinterior, ?_, ?_⟩
        · exact interior_subset.trans
            ((inter_subset_right.trans hballW).trans hWU)
        · intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact interior_subset.trans inter_subset_left
          · exact interior_subset.trans
              ((inter_subset_right.trans hballW).trans (hWs j hj))
  obtain ⟨W, hWopen, hWnonempty, hWU, hWall⟩ := aux Finset.univ
  refine ⟨W, hWopen, hWnonempty, hWU, ?_⟩
  intro x hx
  simp only [Set.mem_iInter]
  intro i
  exact hWall i (Finset.mem_univ i) hx

/-! ## A finite family of separated scalar slabs -/

/-- The common radius used for `k` separated scalar slabs inside a prescribed
real neighborhood. -/
def maxwellSelectionSlabStep (radius : ℝ) (k : ℕ) : ℝ :=
  radius / (4 * (k : ℝ))

/-- The center of the `i`th slab.  Consecutive centers are three slab radii
apart. -/
def maxwellSelectionSlabCenter
    (center radius : ℝ) {k : ℕ} (i : Fin k) : ℝ :=
  center + 3 * (i.val : ℝ) * maxwellSelectionSlabStep radius k

theorem maxwellSelectionSlabStep_pos
    {radius : ℝ} {k : ℕ} (hradius : 0 < radius) (hk : 0 < k) :
    0 < maxwellSelectionSlabStep radius k := by
  unfold maxwellSelectionSlabStep
  positivity

/-- Every scalar slab lies in the original scalar ball. -/
theorem maxwellSelectionSlab_subset_ball
    {center radius : ℝ} {k : ℕ}
    (hradius : 0 < radius) (hk : 0 < k) (i : Fin k) :
    Metric.ball (maxwellSelectionSlabCenter center radius i)
        (maxwellSelectionSlabStep radius k) ⊆
      Metric.ball center radius := by
  intro y hy
  let s : ℝ := maxwellSelectionSlabStep radius k
  have hs : 0 < s := maxwellSelectionSlabStep_pos hradius hk
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkOne : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hiSucc : (i.val : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast i.isLt
  have hiScaled : ((i.val : ℝ) + 1) * s ≤ (k : ℝ) * s :=
    mul_le_mul_of_nonneg_right hiSucc hs.le
  have hscale : 4 * (k : ℝ) * s = radius := by
    dsimp only [s, maxwellSelectionSlabStep]
    field_simp
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy ⊢
  dsimp only [maxwellSelectionSlabCenter] at hy
  constructor <;> nlinarith

/-- Points chosen in distinct scalar slabs are distinct. -/
theorem maxwellSelectionSlab_index_eq_of_point_eq
    {center radius : ℝ} {k : ℕ}
    (hradius : 0 < radius) (hk : 0 < k)
    {i j : Fin k} {yi yj : ℝ}
    (hyi : yi ∈ Metric.ball
      (maxwellSelectionSlabCenter center radius i)
      (maxwellSelectionSlabStep radius k))
    (hyj : yj ∈ Metric.ball
      (maxwellSelectionSlabCenter center radius j)
      (maxwellSelectionSlabStep radius k))
    (hijPoint : yi = yj) : i = j := by
  let s : ℝ := maxwellSelectionSlabStep radius k
  have hs : 0 < s := maxwellSelectionSlabStep_pos hradius hk
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hij | hji
  · have hijSucc : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hijScaled : ((i.val : ℝ) + 1) * s ≤
        (j.val : ℝ) * s :=
      mul_le_mul_of_nonneg_right hijSucc hs.le
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyi hyj
    dsimp only [maxwellSelectionSlabCenter] at hyi hyj
    rw [hijPoint] at hyi
    nlinarith
  · have hjiSucc : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hji)
    have hjiScaled : ((j.val : ℝ) + 1) * s ≤
        (i.val : ℝ) * s :=
      mul_le_mul_of_nonneg_right hjiSucc hs.le
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyi hyj
    dsimp only [maxwellSelectionSlabCenter] at hyi hyj
    rw [hijPoint] at hyi
    nlinarith

/-- The one-dimensional Euclidean ball representing one scalar slab in flat
coordinates. -/
def maxwellSelectionHeightSlab
    (center radius : ℝ) {k : ℕ} (i : Fin k) :
    Set (RealEuclidean 1) :=
  Metric.ball
    (fun _ : Fin 1 ↦ maxwellSelectionSlabCenter center radius i)
    (maxwellSelectionSlabStep radius k)

theorem scalar_mem_maxwellSelectionSlab_of_mem_heightSlab
    {center radius : ℝ} {k : ℕ}
    (hradius : 0 < radius) (hk : 0 < k)
    {i : Fin k} {y : RealEuclidean 1}
    (hy : y ∈ maxwellSelectionHeightSlab center radius i) :
    y 0 ∈ Metric.ball (maxwellSelectionSlabCenter center radius i)
      (maxwellSelectionSlabStep radius k) := by
  have hs := maxwellSelectionSlabStep_pos hradius hk
  rw [maxwellSelectionHeightSlab, Metric.mem_ball] at hy
  rw [Metric.mem_ball]
  exact ((dist_pi_lt_iff hs).mp hy) 0

/-! ## The Maxwell successor selection -/

/-- The source-shaped successor step.  Lower-dimensional closure regularity,
Charbonnel projection membership, and Kuratowski--Ulam produce arbitrarily
many components in one vertical affine section of a meagre successor-arity
member whose closure has interior. -/
theorem maxwellMeagreClosureComponentSelection_of_lower_regular
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    (hprevious : MaxwellClosureInteriorRegularityAt
      (charbonnelClosure S0) n)
    {A : Set (RealEuclidean (n + 1))}
    (hAmem : A ∈ charbonnelClosure S0 (n + 1)) :
    MaxwellMeagreClosureComponentSelection A := by
  intro hAmeagre hclosure N
  classical
  let E : (RealEuclidean n × ℝ) ≃L[ℝ] RealEuclidean (n + 1) :=
    realEuclideanAppendScalarContinuousLinearEquiv n
  let D : Set (RealEuclidean n × ℝ) := E ⁻¹' A
  have hDmeagre : IsMeagre D :=
    hAmeagre.preimage_of_isOpenMap E.continuous E.toHomeomorph.isOpenMap
  have hgood : ∀ᶠ x in residual (RealEuclidean n),
      IsMeagre (maxwellScalarFiber A x) := by
    have hsections :=
      IsMeagre.eventually_isMeagre_productFiber hDmeagre
    filter_upwards [hsections] with x hx
    change IsMeagre {y : ℝ | E (x, y) ∈ A} at hx
    change IsMeagre
      {y : ℝ | realEuclideanAppendScalar x y ∈ A} at hx
    simpa only [maxwellScalarFiber, realEuclideanAppendScalar] using hx
  have hinteriorNonempty : (interior (closure A)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hclosure
  obtain ⟨z, hz⟩ := hinteriorNonempty
  let p : RealEuclidean n × ℝ := E.symm z
  have hpInterior : E p ∈ interior (closure A) := by
    rw [show E p = z from E.apply_symm_apply z]
    exact hz
  have hpreimageNhd : E ⁻¹' interior (closure A) ∈ 𝓝 p :=
    (isOpen_interior.preimage E.continuous).mem_nhds hpInterior
  obtain ⟨baseNhd, hbaseNhd, scalarNhd, hscalarNhd, hrectangle⟩ :=
    mem_nhds_prod_iff.mp hpreimageNhd
  obtain ⟨baseRadius, hbaseRadius, hbaseBall⟩ :=
    Metric.mem_nhds_iff.mp hbaseNhd
  obtain ⟨scalarRadius, hscalarRadius, hscalarBall⟩ :=
    Metric.mem_nhds_iff.mp hscalarNhd
  let k : ℕ := N + 1
  have hk : 0 < k := by omega
  let U : Set (RealEuclidean n) := Metric.ball p.1 baseRadius
  let I : Fin k → Set (RealEuclidean 1) := fun i ↦
    maxwellSelectionHeightSlab p.2 scalarRadius i
  let P : Fin k → Set (RealEuclidean n) := fun i ↦
    realEuclideanExistentialProjection
      (A ∩ realEuclideanSetProduct Set.univ (I i))
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUnonempty : U.Nonempty :=
    ⟨p.1, Metric.mem_ball_self hbaseRadius⟩
  have hPmem : ∀ i, P i ∈ charbonnelClosure S0 n := by
    intro i
    have huniv : (Set.univ : Set (RealEuclidean n)) ∈
        charbonnelClosure S0 n :=
      hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
    have hI : I i ∈ charbonnelClosure S0 1 := by
      exact hC.ws2_polynomialSign (by omega)
        (polynomialSignConstructible_ball _
          (maxwellSelectionSlabStep_pos hscalarRadius hk))
    have hcylinder : realEuclideanSetProduct Set.univ (I i) ∈
        charbonnelClosure S0 (n + 1) :=
      hC.ws3_prod hn (by omega) huniv hI
    have hcut : A ∩ realEuclideanSetProduct Set.univ (I i) ∈
        charbonnelClosure S0 (n + 1) :=
      hC.ws1_inter (by omega) hAmem hcylinder
    exact charbonnelClosure_projection hn hcut
  have hUclosure : ∀ i, U ⊆ closure (P i) := by
    intro i x hxU
    let center : ℝ := maxwellSelectionSlabCenter p.2 scalarRadius i
    let yvec : RealEuclidean 1 := fun _ ↦ center
    let q : RealEuclidean (n + 1) := realEuclideanAppend x yvec
    have hySlab : yvec ∈ I i := by
      change yvec ∈ Metric.ball (fun _ : Fin 1 ↦ center)
        (maxwellSelectionSlabStep scalarRadius k)
      exact Metric.mem_ball_self
        (maxwellSelectionSlabStep_pos hscalarRadius hk)
    have hyScalar : center ∈ Metric.ball p.2 scalarRadius := by
      apply maxwellSelectionSlab_subset_ball hscalarRadius hk i
      exact Metric.mem_ball_self
        (maxwellSelectionSlabStep_pos hscalarRadius hk)
    have hqInterior : q ∈ interior (closure A) := by
      have hpRectangle : (x, center) ∈ baseNhd ×ˢ scalarNhd := by
        exact ⟨hbaseBall hxU, hscalarBall hyScalar⟩
      have hpPreimage := hrectangle hpRectangle
      change E (x, center) ∈ interior (closure A) at hpPreimage
      simpa only [q, yvec, center, E,
        realEuclideanAppendScalarContinuousLinearEquiv_apply,
        realEuclideanAppendScalar] using hpPreimage
    let cylinder : Set (RealEuclidean (n + 1)) :=
      realEuclideanSetProduct Set.univ (I i)
    have hcylinderOpen : IsOpen cylinder := by
      have htakeRight : Continuous
          (realEuclideanTakeRight :
            RealEuclidean (n + 1) → RealEuclidean 1) := by
        apply continuous_pi
        intro j
        exact continuous_apply (Fin.natAdd n j)
      rw [show cylinder =
          (realEuclideanTakeRight :
            RealEuclidean (n + 1) → RealEuclidean 1) ⁻¹' I i by
        ext w
        simp only [cylinder, realEuclideanSetProduct, Set.mem_ofPred_eq,
          Set.mem_preimage, Set.mem_univ, true_and]]
      exact (show IsOpen (I i) from Metric.isOpen_ball).preimage htakeRight
    have hqCylinder : q ∈ cylinder := by
      exact ⟨Set.mem_univ _, by simpa only [q, cylinder,
        realEuclideanSetProduct, realEuclideanTakeRight_append] using hySlab⟩
    have hqCutClosure : q ∈ closure (A ∩ cylinder) := by
      have hq' : q ∈ cylinder ∩ closure A :=
        ⟨hqCylinder, interior_subset hqInterior⟩
      have := hcylinderOpen.inter_closure hq'
      simpa only [inter_comm] using this
    have htakeLeft : Continuous
        (realEuclideanTakeLeft :
          RealEuclidean (n + 1) → RealEuclidean n) := by
      apply continuous_pi
      intro j
      exact continuous_apply (Fin.castAdd 1 j)
    have hmap : MapsTo
        (realEuclideanTakeLeft :
          RealEuclidean (n + 1) → RealEuclidean n)
        (A ∩ cylinder) (P i) := by
      intro w hw
      refine ⟨realEuclideanTakeRight w, ?_⟩
      rw [realEuclideanAppend_take]
      simpa only [P, cylinder] using hw
    have hxClosure : realEuclideanTakeLeft q ∈ closure (P i) :=
      map_mem_closure htakeLeft hqCutClosure hmap
    simpa only [q, realEuclideanTakeLeft_append] using hxClosure
  obtain ⟨W, hWopen, hWnonempty, _hWU, hWall⟩ :=
    exists_open_common_subset_of_closures
      hC.toPositiveArityWeakSetStructure hn hprevious
      hUopen hUnonempty P hPmem hUclosure
  obtain ⟨x, hxW, hxgood⟩ :=
    (dense_of_mem_residual hgood).inter_open_nonempty W hWopen hWnonempty
  have hxP : ∀ i, x ∈ P i := by
    intro i
    exact (Set.mem_iInter.mp (hWall hxW)) i
  have hxExists : ∀ i, ∃ y : RealEuclidean 1,
      realEuclideanAppend x y ∈
        A ∩ realEuclideanSetProduct Set.univ (I i) := by
    intro i
    exact hxP i
  choose y hy using hxExists
  let point : Fin k → maxwellScalarVerticalSection A x := fun i ↦
    ⟨realEuclideanAppend x (y i), (hy i).1,
      (mem_maxwellScalarVerticalAffineSubspace_iff x _).mpr
        (realEuclideanTakeLeft_append x (y i))⟩
  let selected : Fin k →
      ConnectedComponents (maxwellScalarVerticalSection A x) := fun i ↦
    ConnectedComponents.mk (point i)
  have hySlab : ∀ i, y i 0 ∈
      Metric.ball (maxwellSelectionSlabCenter p.2 scalarRadius i)
        (maxwellSelectionSlabStep scalarRadius k) := by
    intro i
    apply scalar_mem_maxwellSelectionSlab_of_mem_heightSlab
      hscalarRadius hk
    simpa only [realEuclideanSetProduct,
      realEuclideanTakeRight_append] using (hy i).2.2
  have htotally : IsTotallyDisconnected (maxwellScalarFiber A x) :=
    IsMeagre.isTotallyDisconnected_real hxgood
  let _ : TotallyDisconnectedSpace (maxwellScalarFiber A x) :=
    totallyDisconnectedSpace_subtype_iff.mpr htotally
  have hselected : Function.Injective selected := by
    intro i j hij
    let f := maxwellScalarVerticalSectionToFiber A x
    have hcomponent := congrArg
      (continuous_maxwellScalarVerticalSectionToFiber A x).connectedComponentsMap
      hij
    have hfiberPoint : f (point i) = f (point j) := by
      simpa only [selected, Continuous.connectedComponentsMap_mk,
        ConnectedComponents.coe_eq_coe, connectedComponent_eq_singleton,
        Set.singleton_eq_singleton_iff] using hcomponent
    have hyEq : y i 0 = y j 0 := by
      have := congrArg Subtype.val hfiberPoint
      simpa only [f, point, maxwellScalarVerticalSectionToFiber,
        realEuclideanTakeRight_append] using this
    exact maxwellSelectionSlab_index_eq_of_point_eq
      hscalarRadius hk (hySlab i) (hySlab j) hyEq
  exact ⟨maxwellScalarVerticalAffineSubspace x, selected, hselected⟩

/-! ## Dimension induction and family-level closure -/

/-- WS6 turns the empty-interior input of the closure induction into
meagreness; the preceding Kuratowski--Ulam construction then supplies its
successor component selection. -/
theorem charbonnelClosure_maxwellClosureInteriorDimensionStep
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0)) :
    MaxwellClosureInteriorDimensionStep (charbonnelClosure S0) := by
  intro n hn hprevious A hAmem
  exact maxwellInteriorGapComponentSelection_of_countableUnionClosed
    (hC.isCountableUnionOfClosedSets (by omega) hAmem)
    (maxwellMeagreClosureComponentSelection_of_lower_regular
      hC hn hprevious hAmem)

/-- Maxwell--Servi closure-interior regularity follows for any Charbonnel
closure carrying the positive-arity o-minimal weak-structure axioms. -/
theorem charbonnelClosure_closureInteriorRegularity
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0)) :
    CharbonnelClosureInteriorRegularity (charbonnelClosure S0) :=
  charbonnelClosureInteriorRegularity_of_maxwellDimensionStep hC
    (charbonnelClosure_maxwellClosureInteriorDimensionStep hC)

/-- The exact family-geometric Maxwell residual is therefore automatic for
a Charbonnel closure satisfying WS1--WS6. -/
theorem charbonnelClosure_hasMaxwellMeagreClosureComponentSelection
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0)) :
    HasMaxwellMeagreClosureComponentSelection (charbonnelClosure S0) :=
  (hasMaxwellMeagreClosureComponentSelection_iff_closureInteriorRegularity
    hC).mpr (charbonnelClosure_closureInteriorRegularity hC)

/-- Literal-zero specialization: geometricity, smoothness, and uniform fiber
finiteness discharge the complete Maxwell meagre-closure selection residual. -/
theorem
    literalZeroSet_charbonnelClosure_hasMaxwellMeagreClosureComponentSelection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)) := by
  exact charbonnelClosure_hasMaxwellMeagreClosureComponentSelection
    (literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF)

end AbelFormalization
