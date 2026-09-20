import AbelFormalization.CharbonnelApproximationTrace
import AbelFormalization.CharbonnelSardianProjectionCase2Bridge

/-!
# Boundary localization for the Sardian projection constructor

The full-projection outcome in Wilkie's Case 2 cannot persist near a
boundary point of the closed target projection.  The reason is quantitative:
an open set meeting that boundary contains a visible point outside the closed
projection, and the whole vertical fiber above that point has positive
distance from the old target closure.  An old from-below approximation then
forces every sufficiently small old parameter section to omit that point.

This module first records the metric separation independently of Sardian
syntax.  It then identifies points of the named old tuple fiber with points
of the corresponding old constituent section.  The final theorem combines
the resulting strict projection inequality with the automatic Case 2 bridge,
thereby retaining only the small-level outcome.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- An open set meeting the frontier of a closed visible projection contains
a point whose entire vertical fiber is uniformly separated from the target
closure. -/
theorem exists_verticalFiber_separated_of_open_inter_frontier_projection
    {n q : ℕ} (A : Set (RealEuclidean (n + q)))
    (U : Set (RealEuclidean n)) (hUopen : IsOpen U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ x ∈ U, ∃ δ : ℝ, 0 < δ ∧
      ∀ z : RealEuclidean (n + q),
        realEuclideanTakeLeft z = x →
          ∀ a ∈ closure A, δ ≤ dist z a := by
  let P : Set (RealEuclidean n) :=
    closure (realEuclideanExistentialProjection A)
  obtain ⟨b, hbU, hbfrontier⟩ := hboundary
  have hbClosureCompl : b ∈ closure Pᶜ := by
    rw [frontier_eq_closure_inter_closure] at hbfrontier
    exact hbfrontier.2
  obtain ⟨x, hxU, hxCompl⟩ :=
    (mem_closure_iff.mp hbClosureCompl) U hUopen hbU
  have hxNotMem : x ∉ P := hxCompl
  have hbP : b ∈ P := isClosed_closure.frontier_subset hbfrontier
  have hPnonempty : P.Nonempty := ⟨b, hbP⟩
  let δ : ℝ := Metric.infDist x P
  have hδpos : 0 < δ :=
    (isClosed_closure.notMem_iff_infDist_pos hPnonempty).mp hxNotMem
  refine ⟨x, hxU, δ, hδpos, ?_⟩
  intro z hz a ha
  have haProjected :
      realEuclideanTakeLeft a ∈
        realEuclideanExistentialProjection (closure A) := by
    rw [realEuclideanExistentialProjection_eq_takeLeft_image]
    exact ⟨a, ha, rfl⟩
  have haP : realEuclideanTakeLeft a ∈ P :=
    realEuclideanExistentialProjection_closure_subset_closure A haProjected
  calc
    δ ≤ dist x (realEuclideanTakeLeft a) :=
      Metric.infDist_le_dist_of_mem haP
    _ = dist (realEuclideanTakeLeft z) (realEuclideanTakeLeft a) := by
      rw [hz]
    _ ≤ dist z a := dist_realEuclideanTakeLeft_le z a

/-- The visible one-coordinate section of a parameterized carrier.  The
single erased visible coordinate is existentially quantified. -/
def charbonnelOneCoordinateVisibleSection
    {n k : ℕ} (T : Set (RealEuclidean ((n + 1) + k)))
    (e : RealEuclidean k) : Set (RealEuclidean n) :=
  {x | ∃ erased : RealEuclidean 1,
    realEuclideanAppend (realEuclideanAppend x erased) e ∈ T}

/-- Boundary separation plus an old from-below approximation gives one
visible point which is absent from every sufficiently small old section.
The point and threshold are uniform over all modulus vectors below the
threshold. -/
theorem exists_point_notMem_visibleSection_of_approximatesFromBelow_boundary
    {n k : ℕ} (A : Set (RealEuclidean (n + 1)))
    (T : Set (RealEuclidean ((n + 1) + k)))
    (oldModulus : CharbonnelModulus k)
    (U : Set (RealEuclidean n))
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus T (closure A))
    (hUopen : IsOpen U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ x ∈ U, ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : RealEuclidean (k + 1),
        oldModulus.IsBounded ε → ε 0 < δ →
          x ∉ charbonnelOneCoordinateVisibleSection T
            (CharbonnelModulus.parameterTail ε) := by
  obtain ⟨x, hxU, δ, hδpos, hseparated⟩ :=
    exists_verticalFiber_separated_of_open_inter_frontier_projection
      A U hUopen hboundary
  refine ⟨x, hxU, δ, hδpos, ?_⟩
  intro ε hε hεδ hxSection
  obtain ⟨erased, hcarrier⟩ := hxSection
  obtain ⟨a, haClosure, hdist⟩ :=
    hbelow ε hε (realEuclideanAppend x erased) hcarrier
  have hfar : δ ≤ dist (realEuclideanAppend x erased) a :=
    hseparated (realEuclideanAppend x erased)
      (realEuclideanTakeLeft_append x erased) a haClosure
  linarith

/-- The old visible input represented by a new flat Case 2 point.  It
contains the retained visible block followed by the erased coordinate. -/
def sardianProjectionOldVisiblePoint
    (n q : ℕ) (v : RealEuclidean (n + (q + 1))) :
    RealEuclidean (n + 1) :=
  realEuclideanTakeLeft (sardianProjectionOldInputReindex n q v)

/-- Reading the retained visible block from the reindexed old input recovers
the visible block of the new flat Case 2 point. -/
@[simp]
theorem realEuclideanTakeLeft_sardianProjectionOldVisiblePoint
    (n q : ℕ) (v : RealEuclidean (n + (q + 1))) :
    realEuclideanTakeLeft (sardianProjectionOldVisiblePoint n q v) =
      realEuclideanTakeLeft v := by
  have hreindex := sardianProjectionOldInputReindex_append_eq n q
    (realEuclideanTakeLeft v) (realEuclideanTakeRight v)
  rw [realEuclideanAppend_take] at hreindex
  simp only [sardianProjectionOldVisiblePoint, hreindex,
    realEuclideanTakeLeft_append]

/-- A point of the old tuple fiber supplies a point in the old constituent
section at the same positive parameter block. -/
theorem append_oldVisiblePoint_mem_carrier_of_mem_oldTupleFiber
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hepos : ∀ i, 0 < e i)
    {v : RealEuclidean (n + (q + 1))}
    (hv : v ∈ sardianProjectionOldTupleFiber old U e) :
    realEuclideanAppend (sardianProjectionOldVisiblePoint n q v) e ∈
      old.carrier := by
  rw [old.mem_carrier_iff]
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  refine ⟨⟨realEuclideanTakeRight
    (sardianProjectionOldInputReindex n q v), ?_⟩, hepos⟩
  intro i
  change old.equation i
      (realEuclideanAppend
        (realEuclideanTakeLeft (sardianProjectionOldInputReindex n q v))
        (realEuclideanTakeRight (sardianProjectionOldInputReindex n q v))) =
    e i
  rw [realEuclideanAppend_take]
  exact hv.2 i

/-- Every old tuple-fiber point puts its retained visible coordinates in the
one-coordinate visible section of the old constituent. -/
theorem takeLeft_mem_visibleSection_of_mem_oldTupleFiber
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hepos : ∀ i, 0 < e i)
    {v : RealEuclidean (n + (q + 1))}
    (hv : v ∈ sardianProjectionOldTupleFiber old U e) :
    realEuclideanTakeLeft v ∈
      charbonnelOneCoordinateVisibleSection old.carrier e := by
  let w : RealEuclidean (n + 1) :=
    sardianProjectionOldVisiblePoint n q v
  refine ⟨realEuclideanTakeRight w, ?_⟩
  have hrecover :
      realEuclideanAppend (realEuclideanTakeLeft v)
          (realEuclideanTakeRight w) = w := by
    rw [← realEuclideanTakeLeft_sardianProjectionOldVisiblePoint n q v]
    exact realEuclideanAppend_take w
  rw [hrecover]
  exact append_oldVisiblePoint_mem_carrier_of_mem_oldTupleFiber
    old U e hepos hv

/-- Conversely, a point of an old constituent section whose retained visible
coordinates lie in `U` supplies a point of the named old tuple fiber. -/
theorem oldTupleFiber_nonempty_of_append_mem_carrier
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    {x : RealEuclidean n} {erased : RealEuclidean 1}
    (hxU : x ∈ U)
    (hcarrier :
      realEuclideanAppend (realEuclideanAppend x erased) e ∈ old.carrier) :
    (sardianProjectionOldTupleFiber old U e).Nonempty := by
  rw [old.mem_carrier_iff] at hcarrier
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append] at hcarrier
  obtain ⟨⟨hidden, hequations⟩, _hpositive⟩ := hcarrier
  let newHidden : RealEuclidean (q + 1) :=
    Fin.cases (erased 0) hidden
  let v : RealEuclidean (n + (q + 1)) :=
    realEuclideanAppend x newHidden
  refine ⟨v, ?_, ?_⟩
  · simpa only [v, realEuclideanTakeLeft_append] using hxU
  intro i
  change old.equation i (sardianProjectionOldInputReindex n q v) = e i
  have herased : (fun _ : Fin 1 ↦ newHidden 0) = erased := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [newHidden]
  have htail : Fin.tail newHidden = hidden := by
    funext j
    simp [newHidden, Fin.tail]
  have hreindex :
      sardianProjectionOldInputReindex n q v =
        realEuclideanAppend (realEuclideanAppend x erased) hidden := by
    rw [show v = realEuclideanAppend x newHidden by rfl,
      sardianProjectionOldInputReindex_append_eq]
    rw [herased, htail]
  rw [hreindex]
  exact hequations i

/-- Boundary localization remains valid when the old constituent is merely
one piece of a larger carrier with a from-below approximation.  This is the
form used for a constituent selected from an old finite Sardian family. -/
theorem
    exists_threshold_takeLeft_image_oldTupleFiber_ne_of_boundary_of_carrier_subset
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (A : Set (RealEuclidean (n + 1)))
    (T : Set (RealEuclidean ((n + 1) + (q + 1))))
    (oldModulus : CharbonnelModulus (q + 1))
    (U : Set (RealEuclidean n))
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus T (closure A))
    (hcarrier : old.carrier ⊆ T)
    (hUopen : IsOpen U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : RealEuclidean ((q + 1) + 1),
        oldModulus.IsBounded ε → ε 0 < δ →
          realEuclideanTakeLeft ''
              sardianProjectionOldTupleFiber old U
                (CharbonnelModulus.parameterTail ε) ≠ U := by
  obtain ⟨x, hxU, δ, hδpos, hxMissing⟩ :=
    exists_point_notMem_visibleSection_of_approximatesFromBelow_boundary
      A T oldModulus U hbelow hUopen hboundary
  refine ⟨δ, hδpos, ?_⟩
  intro ε hε hεδ hprojection
  have hxImage : x ∈ realEuclideanTakeLeft ''
      sardianProjectionOldTupleFiber old U
        (CharbonnelModulus.parameterTail ε) := by
    rw [hprojection]
    exact hxU
  obtain ⟨v, hvFiber, hvx⟩ := hxImage
  apply hxMissing ε hε hεδ
  rw [← hvx]
  obtain ⟨erased, holdCarrier⟩ :=
    takeLeft_mem_visibleSection_of_mem_oldTupleFiber
      old U (CharbonnelModulus.parameterTail ε)
      (fun i ↦ hε.coord_pos i.succ) hvFiber
  exact ⟨erased, hcarrier holdCarrier⟩

/-- Exact boundary localization for the named old tuple fiber.  For every
sufficiently small vector allowed by the old modulus, its visible projection
is strictly smaller than the selected open set. -/
theorem exists_threshold_takeLeft_image_oldTupleFiber_ne_of_boundary
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (A : Set (RealEuclidean (n + 1)))
    (oldModulus : CharbonnelModulus (q + 1))
    (U : Set (RealEuclidean n))
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus old.carrier (closure A))
    (hUopen : IsOpen U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : RealEuclidean ((q + 1) + 1),
        oldModulus.IsBounded ε → ε 0 < δ →
          realEuclideanTakeLeft ''
              sardianProjectionOldTupleFiber old U
                (CharbonnelModulus.parameterTail ε) ≠ U := by
  exact
    exists_threshold_takeLeft_image_oldTupleFiber_ne_of_boundary_of_carrier_subset
      old A old.carrier oldModulus U hbelow (fun _ h ↦ h)
        hUopen hboundary

/-- The source-shaped projection Case 2 conclusion after boundary
localization.  At every sufficiently small old modulus vector, regularity
and bounded nonemptiness of the localized fiber force all small positive
last levels in the projected Sardian family; the full-projection branch has
been eliminated. -/
theorem
    exists_threshold_sardianProjection_smallLevels_of_theorems21_22_of_boundary_of_carrier_subset
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily f) (order + 1) (n + 1) q)
    (A : Set (RealEuclidean (n + 1)))
    (T : Set (RealEuclidean ((n + 1) + (q + 1))))
    (oldModulus : CharbonnelModulus (q + 1))
    (U : Set (RealEuclidean n))
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus T (closure A))
    (hcarrier : old.carrier ⊆ T)
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : RealEuclidean ((q + 1) + 1),
        oldModulus.IsBounded ε → ε 0 < δ →
        (∀ v, sardianProjectionOldTuple old v =
              CharbonnelModulus.parameterTail ε →
          Function.Surjective
            (fderiv ℝ (sardianProjectionOldTuple old) v)) →
        Bornology.IsBounded
          (sardianProjectionOldTupleFiber old U
            (CharbonnelModulus.parameterTail ε)) →
        (sardianProjectionOldTupleFiber old U
          (CharbonnelModulus.parameterTail ε)).Nonempty →
        ∃ η : ℝ, 0 < η ∧
          ∀ t : ℝ, 0 < t → t < η →
            ∃ x ∈ U,
              realEuclideanAppend x
                  (charbonnelAppendLastParameter
                    (CharbonnelModulus.parameterTail ε) t) ∈
                (sardianProjectionAlgebraicFamily
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
                  hn old).carrier := by
  obtain ⟨δ, hδpos, hnotProjection⟩ :=
    exists_threshold_takeLeft_image_oldTupleFiber_ne_of_boundary_of_carrier_subset
      old A T oldModulus U hbelow hcarrier hUopen hboundary
  refine ⟨δ, hδpos, ?_⟩
  intro ε hε hεδ hregular hbounded hnonempty
  have hepos : ∀ i, 0 < CharbonnelModulus.parameterTail ε i := by
    intro i
    exact hε.coord_pos i.succ
  rcases sardianProjection_projection_or_smallLevels_of_theorems21_22
      hf hUFF hn old U (CharbonnelModulus.parameterTail ε) hepos
      h21 h22 hUopen hUconvex hregular hbounded hnonempty with
    hprojection | hsmallLevels
  · exact (hnotProjection ε hε hεδ hprojection).elim
  · exact hsmallLevels

/-- Specialization of the boundary-localized Case 2 conclusion when the
old constituent itself carries the from-below approximation. -/
theorem exists_threshold_sardianProjection_smallLevels_of_theorems21_22_of_boundary
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily f) (order + 1) (n + 1) q)
    (A : Set (RealEuclidean (n + 1)))
    (oldModulus : CharbonnelModulus (q + 1))
    (U : Set (RealEuclidean n))
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus old.carrier (closure A))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hboundary :
      (U ∩ frontier
        (closure (realEuclideanExistentialProjection A))).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : RealEuclidean ((q + 1) + 1),
        oldModulus.IsBounded ε → ε 0 < δ →
        (∀ v, sardianProjectionOldTuple old v =
              CharbonnelModulus.parameterTail ε →
          Function.Surjective
            (fderiv ℝ (sardianProjectionOldTuple old) v)) →
        Bornology.IsBounded
          (sardianProjectionOldTupleFiber old U
            (CharbonnelModulus.parameterTail ε)) →
        (sardianProjectionOldTupleFiber old U
          (CharbonnelModulus.parameterTail ε)).Nonempty →
        ∃ η : ℝ, 0 < η ∧
          ∀ t : ℝ, 0 < t → t < η →
            ∃ x ∈ U,
              realEuclideanAppend x
                  (charbonnelAppendLastParameter
                    (CharbonnelModulus.parameterTail ε) t) ∈
                (sardianProjectionAlgebraicFamily
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                  hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
                  hn old).carrier := by
  exact
    exists_threshold_sardianProjection_smallLevels_of_theorems21_22_of_boundary_of_carrier_subset
      hf hUFF hn old A old.carrier oldModulus U hbelow (fun _ h ↦ h)
        h21 h22 hUopen hUconvex hboundary

end AbelFormalization
