import AbelFormalization.MaxwellMeagreClosureSelection
import AbelFormalization.CharbonnelTraceMembership
import AbelFormalization.CharbonnelSection56InfiniteFiberLocalClosedness

/-!
# Positive zero traces from category and affine-section finiteness

This file gives a direct category proof of the empty-interior part of
Charbonnel's Theorem 2.2.  If a positive zero trace contained an open set,
one can repeatedly shrink that open set into the projections of disjoint
positive height bands.  Kuratowski--Ulam then supplies a base point whose
vertical fibre is meagre.  The band selections give arbitrarily many points
in that fibre, while WS5 forces two of them into one connected component and
therefore forces a nondegenerate interval in the meagre fibre.

The argument uses only WS1--WS6 and closure-interior regularity.  In
particular it does not use the stationary component-count argument of
Charbonnel section 5.3.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Positive vertical bands -/

/-- The one-dimensional open interval `(a,b)`, represented as a ball in
`RealEuclidean 1`. -/
def charbonnelHeightBand (a b : ℝ) : Set (RealEuclidean 1) :=
  Metric.ball (fun _ : Fin 1 ↦ (a + b) / 2) ((b - a) / 2)

theorem mem_charbonnelHeightBand_iff
    {a b : ℝ} (hab : a < b) (y : RealEuclidean 1) :
    y ∈ charbonnelHeightBand a b ↔ a < y 0 ∧ y 0 < b := by
  have hr : 0 < (b - a) / 2 := half_pos (sub_pos.mpr hab)
  rw [charbonnelHeightBand, Metric.mem_ball, dist_pi_lt_iff hr]
  simp only [Fin.forall_fin_one]
  rw [Real.dist_eq, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The vertical cylinder whose final coordinate lies in `(a,b)`. -/
def charbonnelVerticalBand (n : ℕ) (a b : ℝ) :
    Set (RealEuclidean (n + 1)) :=
  realEuclideanSetProduct Set.univ (charbonnelHeightBand a b)

theorem mem_charbonnelVerticalBand_iff
    {n : ℕ} {a b : ℝ} (hab : a < b)
    (z : RealEuclidean (n + 1)) :
    z ∈ charbonnelVerticalBand n a b ↔
      a < z (Fin.last n) ∧ z (Fin.last n) < b := by
  rw [charbonnelVerticalBand]
  simp only [realEuclideanSetProduct, Set.mem_ofPred_eq, Set.mem_univ,
    true_and]
  rw [mem_charbonnelHeightBand_iff hab]
  simp only [realEuclideanTakeRight]
  have hi : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext rfl
  rw [hi]

/-- The set of base points having a point of `A` in the height band
`(a,b)`. -/
def charbonnelVerticalBandProjection {n : ℕ}
    (A : Set (RealEuclidean (n + 1))) (a b : ℝ) :
    Set (RealEuclidean n) :=
  realEuclideanExistentialProjection
    (A ∩ charbonnelVerticalBand n a b)

theorem charbonnelVerticalBand_mem
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n) {a b : ℝ} (hab : a < b) :
    charbonnelVerticalBand n a b ∈ charbonnelClosure S0 (n + 1) := by
  have huniv : (Set.univ : Set (RealEuclidean n)) ∈
      charbonnelClosure S0 n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
  have hheight : charbonnelHeightBand a b ∈
      charbonnelClosure S0 1 := by
    exact hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_ball _
        (half_pos (sub_pos.mpr hab)))
  exact hC.ws3_prod hn (by omega) huniv hheight

theorem charbonnelVerticalBandProjection_mem
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ∈ charbonnelClosure S0 (n + 1))
    {a b : ℝ} (hab : a < b) :
    charbonnelVerticalBandProjection A a b ∈
      charbonnelClosure S0 n := by
  apply charbonnelClosure_projection hn
  exact hC.ws1_inter (by omega) hA
    (charbonnelVerticalBand_mem hC hn hab)

/-! ## A trace point lies in the closure of every low-band projection -/

theorem mem_closure_charbonnelVerticalBandProjection_zero
    {n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (hpositive : A ⊆ charbonnelPositiveLastCoordinateLocus n)
    {x : RealEuclidean n} (hx : x ∈ charbonnelPositiveZeroTrace A)
    {b : ℝ} (hb : 0 < b) :
    x ∈ closure (charbonnelVerticalBandProjection A 0 b) := by
  rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure hpositive] at hx
  let z₀ : RealEuclidean (n + 1) := charbonnelAppendLastCoordinate x 0
  have hz₀ : z₀ ∈ closure A := by
    simpa only [charbonnelZeroSection, Set.mem_ofPred_eq, z₀] using hx
  let H : Set (RealEuclidean (n + 1)) :=
    {z | z (Fin.last n) < b}
  have hHnhds : H ∈ nhds z₀ := by
    have hHopen : IsOpen H := by
      exact isOpen_Iio.preimage
        (continuous_apply (Fin.last n) : Continuous
          (fun z : RealEuclidean (n + 1) ↦ z (Fin.last n)))
    apply hHopen.mem_nhds
    change z₀ (Fin.last n) < b
    simpa only [z₀, charbonnelAppendLastCoordinate_last] using hb
  have hz₀restricted : z₀ ∈ closure (A ∩ H) :=
    mem_closure_inter_of_mem_nhds hHnhds hz₀
  have htakeLeft : Continuous
      (realEuclideanTakeLeft :
        RealEuclidean (n + 1) → RealEuclidean n) := by
    apply continuous_pi
    intro j
    exact continuous_apply (Fin.castAdd 1 j)
  have hmaps : MapsTo
      (realEuclideanTakeLeft :
        RealEuclidean (n + 1) → RealEuclidean n)
      (A ∩ H) (charbonnelVerticalBandProjection A 0 b) := by
    intro z hz
    refine ⟨realEuclideanTakeRight z, ?_⟩
    rw [realEuclideanAppend_take]
    refine ⟨hz.1, ?_⟩
    rw [mem_charbonnelVerticalBand_iff hb]
    exact ⟨hpositive hz.1, hz.2⟩
  have := map_mem_closure htakeLeft hz₀restricted hmaps
  simpa only [z₀, charbonnelAppendLastCoordinate,
    realEuclideanTakeLeft_append] using this

/-! ## One category localization step -/

/-- The lower endpoint used in the countable cover of `(0,b)`. -/
def charbonnelBandLower (b : ℝ) (m : ℕ) : ℝ :=
  b / (m + 2 : ℕ)

theorem charbonnelBandLower_pos {b : ℝ} (hb : 0 < b) (m : ℕ) :
    0 < charbonnelBandLower b m := by
  unfold charbonnelBandLower
  positivity

theorem charbonnelBandLower_lt {b : ℝ} (hb : 0 < b) (m : ℕ) :
    charbonnelBandLower b m < b := by
  unfold charbonnelBandLower
  have hm : (1 : ℝ) < (m + 2 : ℕ) := by exact_mod_cast (by omega : 1 < m + 2)
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (m + 2 : ℕ))).2
    (by nlinarith)

theorem exists_charbonnelBandLower_lt
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    ∃ m : ℕ, charbonnelBandLower b m < t := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos ht hb)
  refine ⟨m, ?_⟩
  unfold charbonnelBandLower
  have hm' : 1 / (((m + 1 : ℕ) : ℝ)) < t / b := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  have hfrac : 1 / ((m + 2 : ℕ) : ℝ) < t / b := by
    have hle : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      norm_num
    exact (one_div_le_one_div_of_le (by positivity) hle).trans_lt hm'
  have hmul :
      b * (1 / ((m + 2 : ℕ) : ℝ)) < b * (t / b) :=
    mul_lt_mul_of_pos_left hfrac hb
  have hbne : b ≠ 0 := ne_of_gt hb
  calc
    b / (m + 2 : ℕ) =
        b * (1 / ((m + 2 : ℕ) : ℝ)) := by ring
    _ < b * (t / b) := hmul
    _ = t := by field_simp

/-- A nonempty open part of a positive zero trace contains a smaller open
ball lying in the projection of one band `(a,b)`, with `a > 0`.

Closure-interior regularity first makes the whole low-band projection large.
The `F_sigma` clause WS6 then prevents its countable cover by the bands
`(b/(m+2),b)` from consisting entirely of empty-interior members. -/
theorem exists_open_ball_subset_charbonnelVerticalBandProjection
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ∈ charbonnelClosure S0 (n + 1))
    (hpositive : A ⊆ charbonnelPositiveLastCoordinateLocus n)
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hUmem : U ∈ charbonnelClosure S0 n)
    (hUtrace : U ⊆ charbonnelPositiveZeroTrace A)
    {b : ℝ} (hb : 0 < b) :
    ∃ (V : Set (RealEuclidean n)) (a : ℝ),
      IsOpen V ∧ V.Nonempty ∧
      V ∈ charbonnelClosure S0 n ∧ V ⊆ U ∧
      0 < a ∧ a < b ∧
      V ⊆ charbonnelVerticalBandProjection A a b := by
  let P₀ : Set (RealEuclidean n) :=
    charbonnelVerticalBandProjection A 0 b
  let Q₀ : Set (RealEuclidean n) := U ∩ P₀
  have hP₀mem : P₀ ∈ charbonnelClosure S0 n :=
    charbonnelVerticalBandProjection_mem
      hC.toPositiveArityWeakSetStructure hn hA hb
  have hQ₀mem : Q₀ ∈ charbonnelClosure S0 n :=
    hC.ws1_inter hn hUmem hP₀mem
  have hUclosure : U ⊆ closure Q₀ := by
    intro x hxU
    have hxP₀ : x ∈ closure P₀ :=
      mem_closure_charbonnelVerticalBandProjection_zero
        hpositive (hUtrace hxU) hb
    have hxQ : x ∈ closure (P₀ ∩ U) :=
      mem_closure_inter_of_mem_nhds (hUopen.mem_nhds hxU) hxP₀
    simpa only [Q₀, inter_comm] using hxQ
  have hQ₀interior : (interior Q₀).Nonempty := by
    by_contra hnone
    have hempty : interior Q₀ = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnone
    have hclosureEmpty : interior (closure Q₀) = ∅ :=
      hregularity hn hQ₀mem hempty
    obtain ⟨x, hxU⟩ := hUnonempty
    have hxInterior : x ∈ interior (closure Q₀) :=
      hUopen.subset_interior_iff.mpr hUclosure hxU
    rw [hclosureEmpty] at hxInterior
    exact hxInterior
  let P : ℕ → Set (RealEuclidean n) := fun m ↦
    charbonnelVerticalBandProjection A (charbonnelBandLower b m) b
  let Q : ℕ → Set (RealEuclidean n) := fun m ↦ U ∩ P m
  have hPmem : ∀ m, P m ∈ charbonnelClosure S0 n := by
    intro m
    exact charbonnelVerticalBandProjection_mem
      hC.toPositiveArityWeakSetStructure hn hA
        (charbonnelBandLower_lt hb m)
  have hQmem : ∀ m, Q m ∈ charbonnelClosure S0 n := by
    intro m
    exact hC.ws1_inter hn hUmem (hPmem m)
  have hcover : Q₀ = ⋃ m : ℕ, Q m := by
    ext x
    constructor
    · rintro ⟨hxU, y, hyA, hyBand⟩
      have hyBounds :=
        (mem_charbonnelVerticalBand_iff hb
          (realEuclideanAppend x y)).mp hyBand
      obtain ⟨m, hm⟩ := exists_charbonnelBandLower_lt
        hb hyBounds.1
      apply Set.mem_iUnion.mpr
      refine ⟨m, hxU, y, hyA, ?_⟩
      apply (mem_charbonnelVerticalBand_iff
        (charbonnelBandLower_lt hb m) _).mpr
      exact ⟨hm, hyBounds.2⟩
    · rintro hx
      obtain ⟨m, hxU, y, hyA, hyBand⟩ := Set.mem_iUnion.mp hx
      have hyBounds :=
        (mem_charbonnelVerticalBand_iff
          (charbonnelBandLower_lt hb m)
          (realEuclideanAppend x y)).mp hyBand
      refine ⟨hxU, y, hyA, ?_⟩
      apply (mem_charbonnelVerticalBand_iff hb _).mpr
      exact ⟨(charbonnelBandLower_pos hb m).trans hyBounds.1,
        hyBounds.2⟩
  have hexists : ∃ m : ℕ, (interior (Q m)).Nonempty := by
    by_contra hnone
    have hempty : ∀ m : ℕ, interior (Q m) = ∅ := by
      intro m
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hm
      exact hnone ⟨m, hm⟩
    have hmeagre : IsMeagre Q₀ := by
      rw [hcover]
      exact isMeagre_iUnion fun m ↦
        hC.isMeagre_of_interior_eq_empty hn (hQmem m) (hempty m)
    exact (not_isMeagre_of_isOpen isOpen_interior hQ₀interior)
      (hmeagre.mono interior_subset)
  obtain ⟨m, x, hx⟩ := hexists
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior x hx
  let V : Set (RealEuclidean n) := Metric.ball x r
  have hVmem : V ∈ charbonnelClosure S0 n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_ball x hr)
  refine ⟨V, charbonnelBandLower b m, Metric.isOpen_ball,
    ⟨x, Metric.mem_ball_self hr⟩, hVmem, ?_,
    charbonnelBandLower_pos hb m, charbonnelBandLower_lt hb m, ?_⟩
  · exact hball.trans (interior_subset.trans inter_subset_left)
  · exact hball.trans (interior_subset.trans inter_subset_right)

/-! ## Iterating the band localization -/

/-- Over a smaller open base, choose `k` distinct points of every vertical
fibre, all below a prescribed positive height. -/
structure CharbonnelLowFiberSelection
    (S0 : EuclideanSetFamily) {n : ℕ}
    (A : Set (RealEuclidean (n + 1)))
    (U : Set (RealEuclidean n)) (b : ℝ) (k : ℕ) where
  base : Set (RealEuclidean n)
  base_open : IsOpen base
  base_nonempty : base.Nonempty
  base_mem : base ∈ charbonnelClosure S0 n
  base_subset : base ⊆ U
  select : ∀ x ∈ base,
    ∃ f : Fin k → maxwellScalarFiber A x,
      Function.Injective f ∧ ∀ i, (f i : ℝ) < b

/-- Repeating the category localization produces any prescribed finite
number of distinct fibre points.  Successive choices are made below the
lower endpoint of the preceding band, so injectivity is immediate. -/
theorem exists_charbonnelLowFiberSelection
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ∈ charbonnelClosure S0 (n + 1))
    (hpositive : A ⊆ charbonnelPositiveLastCoordinateLocus n)
    {U : Set (RealEuclidean n)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hUmem : U ∈ charbonnelClosure S0 n)
    (hUtrace : U ⊆ charbonnelPositiveZeroTrace A)
    {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Nonempty (CharbonnelLowFiberSelection S0 A U b k) := by
  induction k generalizing U b with
  | zero =>
      refine ⟨
        { base := U
          base_open := hUopen
          base_nonempty := hUnonempty
          base_mem := hUmem
          base_subset := Subset.rfl
          select := ?_ }⟩
      intro x _hx
      refine ⟨Fin.elim0, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
  | succ k ih =>
      obtain ⟨W, a, hWopen, hWnonempty, hWmem, hWU,
        ha, hab, hWprojection⟩ :=
        exists_open_ball_subset_charbonnelVerticalBandProjection
          hC hregularity hn hA hpositive hUopen hUnonempty hUmem
            hUtrace hb
      have hWtrace : W ⊆ charbonnelPositiveZeroTrace A :=
        hWU.trans hUtrace
      let lower := Classical.choice
        (ih hWopen hWnonempty hWmem hWtrace ha)
      refine ⟨
        { base := lower.base
          base_open := lower.base_open
          base_nonempty := lower.base_nonempty
          base_mem := lower.base_mem
          base_subset := lower.base_subset.trans hWU
          select := ?_ }⟩
      intro x hx
      obtain ⟨old, holdInjective, holdBound⟩ := lower.select x hx
      have hxW : x ∈ W := lower.base_subset hx
      obtain ⟨y, hyA, hyBand⟩ := hWprojection hxW
      have hyBounds :=
        (mem_charbonnelVerticalBand_iff hab
          (realEuclideanAppend x y)).mp hyBand
      have hyBounds' : a < y 0 ∧ y 0 < b := by
        simpa only [realEuclideanAppend_last_one] using hyBounds
      let high : maxwellScalarFiber A x := ⟨y 0, by
        have hyConst : y = fun _ : Fin 1 ↦ y 0 := by
          funext i
          rw [show i = 0 from Fin.eq_zero i]
        change realEuclideanAppend x (fun _ : Fin 1 ↦ y 0) ∈ A
        rw [← hyConst]
        exact hyA⟩
      let selected : Fin (k + 1) → maxwellScalarFiber A x :=
        Fin.cases high old
      have hselectedInjective : Function.Injective selected := by
        intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · rfl
          exfalso
          have heq : (high : ℝ) = (old j' : ℝ) :=
            by simpa only [selected, Fin.cases_zero, Fin.cases_succ] using
              congrArg Subtype.val hij
          have hhigh : a < (high : ℝ) := by
            simpa only [high] using hyBounds'.1
          have hlow : (old j' : ℝ) < a := holdBound j'
          linarith
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exfalso
            have heq : (old i' : ℝ) = (high : ℝ) :=
              by simpa only [selected, Fin.cases_zero, Fin.cases_succ] using
                congrArg Subtype.val hij
            have hhigh : a < (high : ℝ) := by
              simpa only [high] using hyBounds'.1
            have hlow : (old i' : ℝ) < a := holdBound i'
            linarith
          · apply congrArg Fin.succ
            apply holdInjective
            simpa only [selected, Fin.cases_succ] using hij
      refine ⟨selected, hselectedInjective, ?_⟩
      intro i
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · change (high : ℝ) < b
        simpa only [high] using hyBounds'.2
      · change (old i' : ℝ) < b
        exact (holdBound i').trans hab

/-! ## Direct Theorem 2.2 -/

/-! ## The compact nullity induction -/

/-- The same category closure theorem also closes Maxwell's nullity
dimension induction.  The repaired section 5.6 argument uses the closure of
the infinite-fibre locus as its compact exceptional base; closure regularity
then supplies its interior-lifting property. -/
theorem charbonnelClosure_maxwellClosureNullityDimensionInduction
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0)) :
    MaxwellClosureNullityDimensionInduction (charbonnelClosure S0) := by
  let hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0) :=
    charbonnelClosure_closureInteriorRegularity hC
  let hcompact : CharbonnelSection56CompactFiberReduction
      (charbonnelClosure S0) :=
    charbonnelSection56CompactFiberReduction_of_closureInteriorRegularity
      hC hregularity
  refine
    { closureStep := charbonnelClosure_maxwellClosureInteriorDimensionStep hC
      nullityStep := ?_ }
  intro n hn hPPrime S hScompact _hSconnected hSmem hSpositive
  exact charbonnelCompactPositiveVolumeInterior_of_section56FiberReduction
    hmem hcompact hn hPPrime S hScompact hSmem hSpositive

/-- Consequently WS1--WS6 prove all closure/interior/nullity equivalences
of Charbonnel's Theorem 2.1 for a Charbonnel closure. -/
theorem charbonnelClosure_theorem21_of_category
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0)) :
    CharbonnelTheorem21 (charbonnelClosure S0) :=
  (charbonnelClosure_maxwellClosureNullityDimensionInduction hC hmem)
    |>.theorem21 hC hmem

/-- Literal-zero specialization of the direct Theorem 2.1 proof. -/
theorem literalZeroSet_charbonnelClosure_theorem21
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  intro n hn S hS
  exact charbonnelClosure_theorem21_of_category hC
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
    hn hS

/-- Category, closure regularity, and WS5 rule out interior in the positive
zero trace of an interiorless positive member. -/
theorem charbonnelPositiveZeroTrace_interior_eq_empty_of_category
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ∈ charbonnelClosure S0 (n + 1))
    (hpositive : A ⊆ charbonnelPositiveLastCoordinateLocus n)
    (hAempty : interior A = ∅) :
    interior (charbonnelPositiveZeroTrace A) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro htrace
  obtain ⟨x₀, hx₀⟩ := htrace
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  let U : Set (RealEuclidean n) := Metric.ball x₀ r
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUnonempty : U.Nonempty := ⟨x₀, Metric.mem_ball_self hr⟩
  have hUmem : U ∈ charbonnelClosure S0 n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_ball x₀ hr)
  have hUtrace : U ⊆ charbonnelPositiveZeroTrace A :=
    hball.trans interior_subset
  obtain ⟨N, hcomponents⟩ :=
    exists_maxwellScalarFiber_component_bound_of_ws5 hC hn hA
  let selection := Classical.choice
    (exists_charbonnelLowFiberSelection hC hregularity hn hA hpositive
      hUopen hUnonempty hUmem hUtrace (by norm_num : (0 : ℝ) < 1)
        (N + 1))
  have hAmeagre : IsMeagre A :=
    hC.isMeagre_of_interior_eq_empty (by omega) hA hAempty
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
  obtain ⟨x, hxBase, hxMeagre⟩ :=
    (dense_of_mem_residual hgood).inter_open_nonempty
      selection.base selection.base_open selection.base_nonempty
  obtain ⟨points, hpointsInjective, _hpointsBound⟩ :=
    selection.select x hxBase
  obtain ⟨y, hyOrdered⟩ :=
    exists_maxwellOrderedScalarFiberWitness_of_fin_succ_injection
      points hpointsInjective
  obtain ⟨a, b, hab, hinterval⟩ :=
    exists_interval_subset_maxwellScalarFiber_of_orderedWitness
      (hcomponents x) hyOrdered
  have hIooMeagre : IsMeagre (Set.Ioo a b) :=
    hxMeagre.mono (fun t ht ↦ hinterval ⟨ht.1.le, ht.2.le⟩)
  exact not_isMeagre_of_isOpen isOpen_Ioo
    (Set.nonempty_Ioo.mpr hab) hIooMeagre

/-- Direct category proof of Charbonnel's Theorem 2.2 for a Charbonnel
closure. -/
theorem charbonnelTheorem22_of_category
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S0))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S0)) :
    CharbonnelTheorem22 (charbonnelClosure S0) := by
  intro n hn A hA hpositive
  refine ⟨hmem.positiveZeroTrace_mem hn hA, ?_⟩
  intro hAempty
  exact charbonnelPositiveZeroTrace_interior_eq_empty_of_category
    hC hregularity hn hA hpositive hAempty

/-- For the literal-zero Charbonnel closure, uniform fibre finiteness gives
both closure regularity and positive-zero-trace smallness. -/
theorem literalZeroSet_charbonnelClosure_theorem22
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    CharbonnelTheorem22
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  intro n hn A hA hpositive
  exact charbonnelTheorem22_of_category hC
    (charbonnelClosure_closureInteriorRegularity hC)
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
    hn hA hpositive

/-- The direct category argument supplies the complete trace-smallness
interface. -/
theorem literalZeroSet_charbonnelClosure_approximationTraceSmallness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    CharbonnelApproximationTraceSmallness
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  let hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure (literalZeroSetFamily G)) :=
    charbonnelClosure_closureInteriorRegularity hC
  have h22 : CharbonnelTheorem22
      (charbonnelClosure (literalZeroSetFamily G)) := by
    intro n hn S hS hpositive
    exact literalZeroSet_charbonnelClosure_theorem22 hG hsmooth hUFF
      hn hS hpositive
  refine
    { closure_interior_eq_empty := hregularity
      positiveZeroTrace_interior_eq_empty := ?_ }
  intro n hn S hS hSempty
  have hpositiveMem :=
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
      |>.positiveLastPart_mem hn hS
  have hpositiveEmpty : interior (charbonnelPositiveLastPart S) = ∅ :=
    interior_eq_empty_of_subset inter_subset_left hSempty
  have htrace :=
    (h22 hn hpositiveMem inter_subset_right).2 hpositiveEmpty
  rwa [charbonnelPositiveZeroTrace_positiveLastPart] at htrace

/-- Hence the full approximation-trace tameness input used by Wilkie's
boundary descent is unconditional under the standing family hypotheses and
uniform fibre finiteness. -/
theorem literalZeroSet_charbonnelClosure_approximationTraceTameness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)) :=
  literalZeroSet_charbonnelClosure_traceTameness hG hsmooth
    (literalZeroSet_charbonnelClosure_approximationTraceSmallness
      hG hsmooth hUFF)

end AbelFormalization
