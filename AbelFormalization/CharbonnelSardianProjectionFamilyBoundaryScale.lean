import AbelFormalization.CharbonnelSardianProjectionBoundaryScale
import AbelFormalization.CharbonnelSardianProjectionRadialEscapeDichotomy
import AbelFormalization.CharbonnelSardianExactDepthExtension

/-!
# Finite-family boundary separation scale for Sardian projection

The geometric boundary scale must also lie below the separation threshold
for every old constituent, because the constituent selected by the old
from-above approximation is not known in advance. This file takes that
finite minimum and packages the resulting nonprojection conclusion.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A positive minimum over a finite list, with one as the empty default. -/
def charbonnelPositiveListMinimum {α : Type*}
    (items : List α) (bound : α → ℝ) : ℝ :=
  items.foldr (fun item rest ↦ min (bound item) rest) 1

theorem charbonnelPositiveListMinimum_pos
    {α : Type*} (items : List α) (bound : α → ℝ)
    (hbound : ∀ item ∈ items, 0 < bound item) :
    0 < charbonnelPositiveListMinimum items bound := by
  induction items with
  | nil =>
      simp [charbonnelPositiveListMinimum]
  | cons item items ih =>
      simp only [charbonnelPositiveListMinimum, List.foldr_cons]
      exact lt_min (hbound item (by simp))
        (ih (fun other hother ↦ hbound other (by simp [hother])))

theorem charbonnelPositiveListMinimum_le_of_mem
    {α : Type*} (items : List α) (bound : α → ℝ)
    {item : α} (hitem : item ∈ items) :
    charbonnelPositiveListMinimum items bound ≤ bound item := by
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
      simp only [charbonnelPositiveListMinimum, List.foldr_cons]
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih htail)

/-- The boundary-localization theorem supplies a positive threshold for one
exact-depth extension of one member of the old padded family. -/
private theorem exists_sardianProjectionPieceBoundaryThreshold
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {r : ℝ} (hr : 0 < r) (c : RealEuclidean n)
    (hcBoundary :
      c ∈ frontier (closure (realEuclideanExistentialProjection A)))
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) old.commonHiddenArity)
    (hpiece : piece ∈ old.family.constituents) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ epsilon : RealEuclidean ((old.commonHiddenArity + 1) + 1),
        old.modulus.IsBounded epsilon → epsilon 0 < delta →
          realEuclideanTakeLeft ''
              sardianProjectionOldTupleFiber
                (sardianConstituentExactDepthExtension
                  hG hsmooth piece.hiddenArity_le piece.constituent)
                (Metric.ball c (r / 2))
                (CharbonnelModulus.parameterTail epsilon) ≠
            Metric.ball c (r / 2) := by
  let exactOld :=
    sardianConstituentExactDepthExtension
      hG hsmooth piece.hiddenArity_le piece.constituent
  have hcarrier : exactOld.carrier ⊆ old.family.carrier := by
    intro v hv
    refine ⟨piece, hpiece, ?_⟩
    rw [sardianConstituentExactDepthExtension_carrier_eq_pad
      hG hsmooth piece.hiddenArity_le piece.constituent] at hv
    exact hv
  have hboundary :
      (Metric.ball c (r / 2) ∩
        frontier (closure (realEuclideanExistentialProjection A))).Nonempty :=
    ⟨c, Metric.mem_ball_self (by positivity), hcBoundary⟩
  exact
    exists_threshold_takeLeft_image_oldTupleFiber_ne_of_boundary_of_carrier_subset
      exactOld A old.family.carrier old.modulus
      (Metric.ball c (r / 2))
      old.approximates.approximatesFromBelow hcarrier
      Metric.isOpen_ball hboundary

/-- The selected separation threshold for a possible old piece. Outside the
actual boundary or the old finite list, the harmless value one is used. -/
noncomputable def sardianProjectionPieceBoundaryThreshold
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (r : ℝ) (hr : 0 < r) (c : RealEuclidean n)
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) old.commonHiddenArity) : ℝ := by
  classical
  exact
    if hc : c ∈
        frontier (closure (realEuclideanExistentialProjection A)) then
      if hp : piece ∈ old.family.constituents then
        Classical.choose
          (exists_sardianProjectionPieceBoundaryThreshold
            hG hsmooth old hr c hc piece hp)
      else 1
    else 1

theorem sardianProjectionPieceBoundaryThreshold_pos
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {r : ℝ} (hr : 0 < r) (c : RealEuclidean n)
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) old.commonHiddenArity) :
    0 < sardianProjectionPieceBoundaryThreshold
      hG hsmooth old r hr c piece := by
  classical
  by_cases hc : c ∈
      frontier (closure (realEuclideanExistentialProjection A))
  · by_cases hp : piece ∈ old.family.constituents
    · rw [sardianProjectionPieceBoundaryThreshold, dif_pos hc, dif_pos hp]
      exact (Classical.choose_spec
        (exists_sardianProjectionPieceBoundaryThreshold
          hG hsmooth old hr c hc piece hp)).1
    · simp [sardianProjectionPieceBoundaryThreshold, hc, hp]
  · simp [sardianProjectionPieceBoundaryThreshold, hc]

theorem sardianProjectionPieceBoundaryThreshold_spec
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {r : ℝ} (hr : 0 < r) {c : RealEuclidean n}
    (hc : c ∈ frontier
      (closure (realEuclideanExistentialProjection A)))
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) old.commonHiddenArity)
    (hpiece : piece ∈ old.family.constituents)
    (epsilon : RealEuclidean ((old.commonHiddenArity + 1) + 1))
    (hepsilon : old.modulus.IsBounded epsilon)
    (hepsilonThreshold : epsilon 0 <
      sardianProjectionPieceBoundaryThreshold
        hG hsmooth old r hr c piece) :
    realEuclideanTakeLeft ''
        sardianProjectionOldTupleFiber
          (sardianConstituentExactDepthExtension
            hG hsmooth piece.hiddenArity_le piece.constituent)
          (Metric.ball c (r / 2))
          (CharbonnelModulus.parameterTail epsilon) ≠
      Metric.ball c (r / 2) := by
  classical
  rw [sardianProjectionPieceBoundaryThreshold,
    dif_pos hc, dif_pos hpiece] at hepsilonThreshold
  exact (Classical.choose_spec
    (exists_sardianProjectionPieceBoundaryThreshold
      hG hsmooth old hr c hc piece hpiece)).2
        epsilon hepsilon hepsilonThreshold

/-- The minimum separation threshold over every possible old constituent at
one visible center. -/
noncomputable def sardianProjectionFamilyBoundaryThreshold
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (r : ℝ) (hr : 0 < r) (c : RealEuclidean n) : ℝ :=
  charbonnelPositiveListMinimum old.family.constituents
    (sardianProjectionPieceBoundaryThreshold
      hG hsmooth old r hr c)

theorem sardianProjectionFamilyBoundaryThreshold_pos
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {r : ℝ} (hr : 0 < r) (c : RealEuclidean n) :
    0 < sardianProjectionFamilyBoundaryThreshold
      hG hsmooth old r hr c := by
  apply charbonnelPositiveListMinimum_pos
  intro piece hpiece
  exact sardianProjectionPieceBoundaryThreshold_pos
    hG hsmooth old hr c piece

theorem sardianProjectionFamilyBoundaryThreshold_le_piece
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {r : ℝ} (hr : 0 < r) (c : RealEuclidean n)
    (piece : CharbonnelPaddedSardianConstituent
      G (order + 1) (n + 1) old.commonHiddenArity)
    (hpiece : piece ∈ old.family.constituents) :
    sardianProjectionFamilyBoundaryThreshold hG hsmooth old r hr c ≤
      sardianProjectionPieceBoundaryThreshold
        hG hsmooth old r hr c piece :=
  charbonnelPositiveListMinimum_le_of_mem
    old.family.constituents
    (sardianProjectionPieceBoundaryThreshold
      hG hsmooth old r hr c) hpiece

/-- The final geometric scale includes the finite minimum of every
constituent's boundary-separation threshold. -/
noncomputable def sardianProjectionFiniteFamilyBoundaryScale
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (B : ℝ) (hB : 0 < B) (r : ℝ) : ℝ :=
  if hr : 0 < r then
    Classical.choose
      (exists_sardianProjectionBoundaryCoverScale A
        (sardianProjectionFamilyBoundaryThreshold
          hG hsmooth old r hr)
        hr hB
        (fun c _hc ↦
          sardianProjectionFamilyBoundaryThreshold_pos
            hG hsmooth old hr c))
  else B / 2

theorem sardianProjectionFiniteFamilyBoundaryScale_pos
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) :
    0 < sardianProjectionFiniteFamilyBoundaryScale
      hG hsmooth old B hB r := by
  rw [sardianProjectionFiniteFamilyBoundaryScale, dif_pos hr]
  exact (Classical.choose_spec
    (exists_sardianProjectionBoundaryCoverScale A
      (sardianProjectionFamilyBoundaryThreshold
        hG hsmooth old r hr)
      hr hB
      (fun c _hc ↦
        sardianProjectionFamilyBoundaryThreshold_pos
          hG hsmooth old hr c))).1

theorem sardianProjectionFiniteFamilyBoundaryScale_lt_initial
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) :
    sardianProjectionFiniteFamilyBoundaryScale
      hG hsmooth old B hB r < B := by
  rw [sardianProjectionFiniteFamilyBoundaryScale, dif_pos hr]
  exact (Classical.choose_spec
    (exists_sardianProjectionBoundaryCoverScale A
      (sardianProjectionFamilyBoundaryThreshold
        hG hsmooth old r hr)
      hr hB
      (fun c _hc ↦
        sardianProjectionFamilyBoundaryThreshold_pos
          hG hsmooth old hr c))).2.2.1

theorem sardianProjectionFiniteFamilyBoundaryScale_lt_visible
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) :
    sardianProjectionFiniteFamilyBoundaryScale
      hG hsmooth old B hB r < r / 8 := by
  rw [sardianProjectionFiniteFamilyBoundaryScale, dif_pos hr]
  exact (Classical.choose_spec
    (exists_sardianProjectionBoundaryCoverScale A
      (sardianProjectionFamilyBoundaryThreshold
        hG hsmooth old r hr)
      hr hB
      (fun c _hc ↦
        sardianProjectionFamilyBoundaryThreshold_pos
          hG hsmooth old hr c))).2.1

/-- The assembly-facing specification: a selected cover ball contains a
fixed old-boundary lift, and the chosen global scale rules out full
projection for every possible exact-depth old constituent. -/
theorem sardianProjectionFiniteFamilyBoundaryScale_spec
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r)
    {z : RealEuclidean n}
    (hz : z ∈ sardianProjectionBoundaryTruncation A r⁻¹) :
    ∃ c ∈ sardianProjectionBoundaryTruncation A r⁻¹,
      z ∈ Metric.ball c (r / 8) ∧
      ∃ a : RealEuclidean n, ∃ hidden : RealEuclidean 1,
        a ∈ Metric.ball c (r / 8) ∧
        realEuclideanAppend a hidden ∈ frontier (closure A) ∧
        ‖realEuclideanAppend a hidden‖ <
          (sardianProjectionFiniteFamilyBoundaryScale
            hG hsmooth old B hB r)⁻¹ ∧
        ∀ piece ∈ old.family.constituents,
          ∀ epsilon : RealEuclidean
              ((old.commonHiddenArity + 1) + 1),
            old.modulus.IsBounded epsilon →
            epsilon 0 =
                sardianProjectionFiniteFamilyBoundaryScale
                  hG hsmooth old B hB r →
              realEuclideanTakeLeft ''
                  sardianProjectionOldTupleFiber
                    (sardianConstituentExactDepthExtension
                      hG hsmooth piece.hiddenArity_le piece.constituent)
                    (Metric.ball c (r / 2))
                    (CharbonnelModulus.parameterTail epsilon) ≠
                Metric.ball c (r / 2) := by
  let hexistence :=
    exists_sardianProjectionBoundaryCoverScale A
      (sardianProjectionFamilyBoundaryThreshold
        hG hsmooth old r hr)
      hr hB
      (fun c _hc ↦
        sardianProjectionFamilyBoundaryThreshold_pos
          hG hsmooth old hr c)
  let selectedScale : ℝ := Classical.choose hexistence
  have hspec := (Classical.choose_spec hexistence).2.2.2 z hz
  have hscaleEq :
      sardianProjectionFiniteFamilyBoundaryScale
          hG hsmooth old B hB r = selectedScale := by
    simp only [sardianProjectionFiniteFamilyBoundaryScale, dif_pos hr,
      selectedScale, hexistence]
  obtain ⟨c, hcK, hzc, a, hidden, ha, hfrontier, hnorm, hscaleExtra⟩ :=
    hspec
  refine ⟨c, hcK, hzc, a, hidden, ha, hfrontier, ?_, ?_⟩
  · simpa only [hscaleEq] using hnorm
  intro piece hpiece epsilon hepsilon hepsilonZero
  apply sardianProjectionPieceBoundaryThreshold_spec
    hG hsmooth old hr hcK.1 piece hpiece epsilon hepsilon
  rw [hepsilonZero, hscaleEq]
  exact hscaleExtra.trans_le
    (sardianProjectionFamilyBoundaryThreshold_le_piece
      hG hsmooth old hr c piece hpiece)

end AbelFormalization
