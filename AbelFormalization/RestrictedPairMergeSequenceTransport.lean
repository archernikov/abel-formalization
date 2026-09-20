import AbelFormalization.RestrictedPairMergeCoordinates
import AbelFormalization.PairMergeSequenceEstimate
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Sequence and domain transport for an unbounded pair merge

This file packages the geometric part of the manuscript's pair-merging
argument.  The old source has `m + 2` unbounded representatives and `p`
bounded coordinates.  The new source has `m + 1` representatives and appends
the bounded logarithmic displacement `xi` to the box coordinates.

The explicit pullback below is a right inverse to
`restrictedPairMergeSourceMap` whenever the two selected old representative
coordinates are positive.  Sequence convergence, eventual box membership,
and regular-zero transport then follow from this identity and
`IsAbel.pairMerge_logCoordinate_tendsto_zero`.
-/

noncomputable section

open Set Filter Function Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## The explicit logarithmic pullback -/

/-- Recover the pair-merged source coordinates from an old source point.

The retained representative `j` becomes
`u = L^[K] (s_(i.succAbove j))`; the deleted representative `i` is encoded by
the appended coordinate
`xi = L^[K+k] (s_i) - u`. -/
def restrictedPairMergePullback {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a) :
    RestrictedSource (m + 1) (p + 1) a :=
  ((Function.update
      (fun r : Fin (m + 1) ↦ x.1.1 (i.succAbove r)) j
      (L^[K] (x.1.1 (i.succAbove j))),
    Fin.snoc x.1.2
      (L^[K + k] (x.1.1 i) - L^[K] (x.1.1 (i.succAbove j)))),
    x.2)

@[simp]
theorem restrictedPairMergePullback_rep_partner {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a) :
    (restrictedPairMergePullback K k i j x).1.1 j =
      L^[K] (x.1.1 (i.succAbove j)) := by
  simp [restrictedPairMergePullback]

@[simp]
theorem restrictedPairMergePullback_rep_other {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j r : Fin (m + 1))
    (hr : r ≠ j) (x : RestrictedSource ((m + 1) + 1) p a) :
    (restrictedPairMergePullback K k i j x).1.1 r =
      x.1.1 (i.succAbove r) := by
  simp [restrictedPairMergePullback, hr]

@[simp]
theorem restrictedPairMergePullback_box_last {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a) :
    (restrictedPairMergePullback K k i j x).1.2 (Fin.last p) =
      L^[K + k] (x.1.1 i) - L^[K] (x.1.1 (i.succAbove j)) := by
  simp [restrictedPairMergePullback]

@[simp]
theorem restrictedPairMergePullback_box_castSucc {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a) (r : Fin p) :
    (restrictedPairMergePullback K k i j x).1.2 r.castSucc = x.1.2 r := by
  simp [restrictedPairMergePullback]

@[simp]
theorem restrictedPairMergePullback_aux {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a) (r : Fin a) :
    (restrictedPairMergePullback K k i j x).2 r = x.2 r := rfl

/-- On the positive old pair tail, the explicit logarithmic pullback is a
right inverse to the pair-merge source map. -/
theorem restrictedPairMergeSourceMap_pullback {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a)
    (hi : 0 < x.1.1 i) (hj : 0 < x.1.1 (i.succAbove j)) :
    restrictedPairMergeSourceMap K k i j
        (restrictedPairMergePullback K k i j x) = x := by
  apply Prod.ext
  · apply Prod.ext
    · funext r
      refine Fin.succAboveCases i ?_ (fun q ↦ ?_) r
      · simp [restrictedPairMergePullback, E_iterate_L_iterate hi]
      · by_cases hq : q = j
        · subst q
          simp [restrictedPairMergePullback, E_iterate_L_iterate hj]
        · simp [restrictedPairMergePullback, hq]
    · funext r
      simp [restrictedPairMergePullback]
  · rfl

/-- Positivity of the selected old pair is exactly what is needed to put its
logarithmic pullback in the natural positive pair tail. -/
theorem restrictedPairMergePullback_mem_tail {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource ((m + 1) + 1) p a)
    (hi : 0 < x.1.1 i) (hj : 0 < x.1.1 (i.succAbove j)) :
    restrictedPairMergePullback K k i j x ∈
      restrictedPairMergeTail (p := p) (a := a) j := by
  constructor
  · simpa using L_iterate_pos hj K
  · simpa [restrictedPairMergePullback] using L_iterate_pos hi (K + k)

/-- Pulling back an injective old sequence remains injective when the selected
pair is positive at every index. -/
theorem restrictedPairMergePullback_injective_sequence {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hx : Function.Injective x)
    (hi : ∀ n, 0 < (x n).1.1 i)
    (hj : ∀ n, 0 < (x n).1.1 (i.succAbove j)) :
    Function.Injective (fun n ↦ restrictedPairMergePullback K k i j (x n)) := by
  intro n n' h
  apply hx
  have := congrArg (restrictedPairMergeSourceMap K k i j) h
  simpa [restrictedPairMergeSourceMap_pullback K k i j (x n) (hi n) (hj n),
    restrictedPairMergeSourceMap_pullback K k i j (x n') (hi n') (hj n')] using this

/-! ## Coordinatewise sequence behavior -/

/-- The logarithmic inverse coordinate tends to infinity. -/
theorem tendsto_L_atTop : Tendsto L atTop atTop := by
  unfold L
  exact Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))

/-- Every fixed logarithmic iterate preserves divergence to infinity. -/
theorem tendsto_L_iterate_atTop (K : ℕ) :
    Tendsto (L^[K]) atTop atTop :=
  tendsto_L_atTop.iterate K

/-- The new unbounded representative `u` tends to infinity whenever its old
partner representative does. -/
theorem restrictedPairMergePullback_partner_tendsto_atTop
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop) :
    Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.1 j)
      atTop atTop := by
  apply ((tendsto_L_iterate_atTop K).comp hj).congr'
  filter_upwards [] with n
  simp [restrictedPairMergePullback]

/-- All retained representatives still tend to infinity.  At `j` this is
the fixed logarithmic iterate of the chosen partner; away from `j` it is an
unchanged old coordinate. -/
theorem restrictedPairMergePullback_representatives_tendsto_atTop
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hx : ∀ r, Tendsto (fun n ↦ (x n).1.1 r) atTop atTop) :
    ∀ r, Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.1 r)
      atTop atTop := by
  intro r
  by_cases hr : r = j
  · subst r
    exact restrictedPairMergePullback_partner_tendsto_atTop K k i j x
      (hx (i.succAbove j))
  · simpa [restrictedPairMergePullback, hr] using hx (i.succAbove r)

/-- Manuscript-shaped inputs imply convergence of the appended logarithmic
displacement coordinate to zero. -/
theorem IsAbel.restrictedPairMergePullback_xi_tendsto_zero
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (t : ℕ → ℝ) (N D K k : ℕ)
    (hK : K = N + D + 3)
    (ht : Tendsto t atTop atTop)
    (hi : Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop)
    (hiUpper : ∀ᶠ n in atTop,
      A ((x n).1.1 i) ≤ t n + (D : ℝ))
    (hjUpper : ∀ᶠ n in atTop,
      A ((x n).1.1 (i.succAbove j)) ≤ t n + (D : ℝ))
    (hnear : ∀ᶠ n in atTop,
      |pairMergeDelta
          (fun r ↦ A ((x r).1.1 i))
          (fun r ↦ A ((x r).1.1 (i.succAbove j))) k n| <
        (inverse A (t n - (N : ℝ)))⁻¹) :
    Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.2
        (Fin.last p)) atTop (nhds 0) := by
  simpa using hA.pairMerge_logCoordinate_tendsto_zero
    t (fun n ↦ (x n).1.1 i)
      (fun n ↦ (x n).1.1 (i.succAbove j))
      N D K k hK ht hi hj hiUpper hjUpper hnear

/-- If the old bounded tuple converges and the appended displacement tends to
zero, then the enlarged bounded tuple converges to `Fin.snoc w0 0`. -/
theorem restrictedPairMergePullback_box_tendsto
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (w0 : RestrictedBoxSpace p)
    (hw : Tendsto (fun n ↦ (x n).1.2) atTop (nhds w0))
    (hxi : Tendsto
      (fun n ↦ L^[K + k] ((x n).1.1 i) -
        L^[K] ((x n).1.1 (i.succAbove j))) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.2)
      atTop (nhds (Fin.snoc w0 0)) := by
  simpa [restrictedPairMergePullback] using hw.finSnoc hxi

/-- Convergence of the displacement supplies a uniform bound, including the
finite prefix of the sequence. -/
theorem exists_uniform_bound_pairMergePullback_xi
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hxi : Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.2
        (Fin.last p)) atTop (nhds 0)) :
    ∃ B : ℝ, 0 < B ∧ ∀ n,
      |(restrictedPairMergePullback K k i j (x n)).1.2 (Fin.last p)| < B := by
  obtain ⟨B, hB, hbound⟩ :=
    (Metric.isBounded_range_of_tendsto _ hxi).exists_pos_norm_lt
  refine ⟨B, hB, ?_⟩
  intro n
  simpa only [Real.norm_eq_abs] using
    hbound _ ⟨n, rfl⟩

/-! ## Eventual positivity and restricted-box membership -/

/-- Divergence of the selected pair gives eventual membership of the
transformed sequence in the positive pair tail. -/
theorem eventually_restrictedPairMergePullback_mem_tail
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hi : Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop) :
    ∀ᶠ n in atTop, restrictedPairMergePullback K k i j (x n) ∈
      restrictedPairMergeTail (p := p) (a := a) j := by
  filter_upwards [hi.eventually (eventually_gt_atTop 0),
    hj.eventually (eventually_gt_atTop 0)] with n hin hjn
  exact restrictedPairMergePullback_mem_tail K k i j (x n) hin hjn

/-- Consequently the pair-merge map sends the transformed sequence back to
the old sequence eventually. -/
theorem eventually_restrictedPairMergeSourceMap_pullback
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hi : Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop) :
    ∀ᶠ n in atTop,
      restrictedPairMergeSourceMap K k i j
          (restrictedPairMergePullback K k i j (x n)) = x n := by
  filter_upwards [hi.eventually (eventually_gt_atTop 0),
    hj.eventually (eventually_gt_atTop 0)] with n hin hjn
  exact restrictedPairMergeSourceMap_pullback K k i j (x n) hin hjn

/-- Discarding a finite prefix turns the transformed sequence into an
everywhere-positive, exact right-inverse sequence.  If the old sequence is
injective, the shifted transformed sequence is injective as well. -/
theorem exists_shift_restrictedPairMergePullback_injective
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hx : Function.Injective x)
    (hi : Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop) :
    ∃ n0 : ℕ,
      Function.Injective
        (fun n ↦ restrictedPairMergePullback K k i j (x (n0 + n))) ∧
      ∀ n,
        restrictedPairMergePullback K k i j (x (n0 + n)) ∈
            restrictedPairMergeTail (p := p) (a := a) j ∧
          restrictedPairMergeSourceMap K k i j
              (restrictedPairMergePullback K k i j (x (n0 + n))) =
            x (n0 + n) := by
  have hgood : ∀ᶠ n in atTop,
      0 < (x n).1.1 i ∧ 0 < (x n).1.1 (i.succAbove j) :=
    (hi.eventually (eventually_gt_atTop 0)).and
      (hj.eventually (eventually_gt_atTop 0))
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hgood
  have hpos : ∀ n,
      0 < (x (n0 + n)).1.1 i ∧
        0 < (x (n0 + n)).1.1 (i.succAbove j) := by
    intro n
    exact hn0 (n0 + n) (Nat.le_add_right n0 n)
  refine ⟨n0, ?_, ?_⟩
  · exact restrictedPairMergePullback_injective_sequence K k i j
      (fun n ↦ x (n0 + n))
      (fun _ _ h ↦ Nat.add_left_cancel (hx h))
      (fun n ↦ (hpos n).1) (fun n ↦ (hpos n).2)
  · intro n
    exact ⟨restrictedPairMergePullback_mem_tail K k i j _
        (hpos n).1 (hpos n).2,
      restrictedPairMergeSourceMap_pullback K k i j _
        (hpos n).1 (hpos n).2⟩

/-- Appending any fixed interval around zero eventually contains the new
bounded tuple, provided the old tuple stays in the old open box. -/
theorem eventually_restrictedPairMergePullback_mem_openBox_snoc
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (D : RestrictedBox p) (l u : ℝ) (hlu : l < u)
    (hl : l < 0) (hu : 0 < u)
    (hbox : ∀ n, (x n).1.2 ∈ D.openBox)
    (hxi : Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.2
        (Fin.last p)) atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      (restrictedPairMergePullback K k i j (x n)).1.2 ∈
        (D.snoc l u hlu).openBox := by
  have hIoo : Set.Ioo l u ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨hl, hu⟩
  filter_upwards [hxi.eventually hIoo] with n hxin
  rw [D.mem_openBox_snoc]
  refine ⟨?_, ?_⟩
  · simpa using hbox n
  · simpa only [Set.mem_Ioo] using hxin

/-- The expected limit point of the enlarged bounded tuple lies in the
enlarged closed box. -/
theorem finSnoc_zero_mem_closedBox_snoc {p : ℕ}
    (D : RestrictedBox p) (w0 : RestrictedBoxSpace p)
    (l u : ℝ) (hlu : l < u)
    (hw0 : w0 ∈ D.closedBox) (hl : l ≤ 0) (hu : 0 ≤ u) :
    Fin.snoc w0 0 ∈ (D.snoc l u hlu).closedBox := by
  rw [D.mem_closedBox_snoc]
  exact ⟨by simpa using hw0, by simpa using hl, by simpa using hu⟩

/-- The transformed sequence eventually lies in every prescribed lower-tail
restricted base domain for the enlarged box. -/
theorem eventually_restrictedPairMergePullback_mem_baseOpenDomain
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (D : RestrictedBox p) (l u : ℝ) (hlu : l < u)
    (hl : l < 0) (hu : 0 < u) (R : ℝ)
    (hreps : ∀ r, Tendsto (fun n ↦ (x n).1.1 r) atTop atTop)
    (hbox : ∀ n, (x n).1.2 ∈ D.openBox)
    (hxi : Tendsto
      (fun n ↦ (restrictedPairMergePullback K k i j (x n)).1.2
        (Fin.last p)) atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      restrictedPairMergePullback K k i j (x n) ∈
        restrictedBaseOpenDomain (D.snoc l u hlu) R := by
  have hnewReps :=
    restrictedPairMergePullback_representatives_tendsto_atTop K k i j x hreps
  have hrepR : ∀ᶠ n in atTop,
      ∀ r, R < (restrictedPairMergePullback K k i j (x n)).1.1 r :=
    Filter.eventually_all.mpr fun r ↦
      (hnewReps r).eventually (eventually_gt_atTop R)
  have hnewBox := eventually_restrictedPairMergePullback_mem_openBox_snoc
    K k i j x D l u hlu hl hu hbox hxi
  filter_upwards [hrepR, hnewBox] with n hnR hnbox
  exact ⟨hnR, hnbox⟩

/-! ## Regular-zero transport along the sequence -/

/-- Pointwise regular-zero transport stated directly for the explicit
logarithmic pullback. -/
theorem mem_regularZeroSet_restrictedPairMergePullback_iff
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (Omega : Set (RestrictedSource ((m + 1) + 1) p a))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ)
    (x : RestrictedSource ((m + 1) + 1) p a)
    (hi : 0 < x.1.1 i) (hj : 0 < x.1.1 (i.succAbove j))
    (hF : DifferentiableAt ℝ (constraintMap F) x) :
    restrictedPairMergePullback K k i j x ∈
        regularZeroSet
          (restrictedPairMergeSourceMap K k i j ⁻¹' Omega)
          (constraintMap (restrictedPairMergedEquationFamily K k i j F)) ↔
      x ∈ regularZeroSet Omega (constraintMap F) := by
  have htail := restrictedPairMergePullback_mem_tail K k i j x hi hj
  have hmap := restrictedPairMergeSourceMap_pullback K k i j x hi hj
  have hiff := mem_regularZeroSet_restrictedPairMergedEquationFamily_iff
    K k i j Omega F (restrictedPairMergePullback K k i j x)
      htail.1 htail.2 (by simpa [hmap] using hF)
  simpa [hmap] using hiff

/-- An old sequence of regular zeros pulls back eventually to regular zeros
of the merged equation family on the positive pair tail. -/
theorem eventually_restrictedPairMergePullback_mem_regularZeroSet
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (Omega : Set (RestrictedSource ((m + 1) + 1) p a))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ)
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hi : Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop)
    (hx : ∀ n, x n ∈ regularZeroSet Omega (constraintMap F))
    (hF : ∀ n, DifferentiableAt ℝ (constraintMap F) (x n)) :
    ∀ᶠ n in atTop,
      restrictedPairMergePullback K k i j (x n) ∈
        regularZeroSet
          (restrictedPairMergeTail j ∩
            restrictedPairMergeSourceMap K k i j ⁻¹' Omega)
          (constraintMap (restrictedPairMergedEquationFamily K k i j F)) := by
  filter_upwards [hi.eventually (eventually_gt_atTop 0),
    hj.eventually (eventually_gt_atTop 0)] with n hin hjn
  have htail := restrictedPairMergePullback_mem_tail K k i j (x n) hin hjn
  have hbase :=
    (mem_regularZeroSet_restrictedPairMergePullback_iff
      K k i j Omega F (x n) hin hjn (hF n)).mpr (hx n)
  exact ⟨⟨htail, hbase.1⟩, hbase.2.1, hbase.2.2⟩

/-- The same eventual regular zeros can be localized to the enlarged
restricted base domain once its eventual membership has been proved.  The
old domain disappears from the conclusion: it was used only to import the
zero equation and the surjective derivative. -/
theorem eventually_restrictedPairMergePullback_mem_regularZeroSet_baseOpen
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (D : RestrictedBox p) (l u : ℝ) (hlu : l < u) (R : ℝ)
    (Omega : Set (RestrictedSource ((m + 1) + 1) p a))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ)
    (x : ℕ → RestrictedSource ((m + 1) + 1) p a)
    (hnewDomain : ∀ᶠ n in atTop,
      restrictedPairMergePullback K k i j (x n) ∈
        restrictedBaseOpenDomain (D.snoc l u hlu) R)
    (hi : Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j)) atTop atTop)
    (hx : ∀ n, x n ∈ regularZeroSet Omega (constraintMap F))
    (hF : ∀ n, DifferentiableAt ℝ (constraintMap F) (x n)) :
    ∀ᶠ n in atTop,
      restrictedPairMergePullback K k i j (x n) ∈
        regularZeroSet
          (restrictedBaseOpenDomain (D.snoc l u hlu) R)
          (constraintMap (restrictedPairMergedEquationFamily K k i j F)) := by
  have hregular := eventually_restrictedPairMergePullback_mem_regularZeroSet
    K k i j Omega F x hi hj hx hF
  filter_upwards [hnewDomain, hregular] with n hdomain hn
  exact ⟨hdomain, hn.2.1, hn.2.2⟩

end AbelFormalization
