import AbelFormalization.LionLemma4CriticalLocus
import AbelFormalization.LionRegularZeroSectionLeaf

/-!
# The finite regular-minor cover in Lion's Lemma 4

Assume `p + q < n`.  Lion chooses `n - p - q` coordinate coefficients of
the critical form `theta_a`.  Appending the chosen coefficients to the old
defining tuple gives `n - p` equations.  On the locus where their derivative
has full rank, their common zero section is therefore a carpeted leaf of
codimension `n - p`.

This file makes that finite family of leaves explicit.  The remaining input
from Lion's generic-parameter argument is isolated as its precise pointwise
consequence: at each point of the critical trace, some chosen coefficient
tuple makes the appended derivative surjective.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- A choice, with order, of the `n - p - q` coordinate coefficients of
Lion's critical form.  This is a finite type.  Repeated choices are harmless:
they can never satisfy the full-rank condition used below. -/
abbrev CriticalCoefficientSelection (n q p : ℕ) :=
  Fin (n - p - q) → (Fin ((q + p) + 1) ↪ Fin n)

/-- The tuple `h` formed from a choice of `n - p - q` coefficients of
`theta_a`. -/
def selectedCriticalCoefficientTuple
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ)
    (selection : CriticalCoefficientSelection n q p) :
    RealEuclidean n → RealEuclidean (n - p - q) :=
  fun x i ↦ L.criticalCoefficient g center height (selection i) x

/-- Every coordinate of a selected critical-coefficient tuple remains in
the geometric family. -/
theorem selectedCriticalCoefficientTuple_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (selection : CriticalCoefficientSelection n q p) :
    FunctionTupleInFamily G
      (L.selectedCriticalCoefficientTuple g center height selection) := by
  intro i
  exact L.criticalCoefficient_mem hG hderiv g hg center hheight (selection i)

/-- Under Lion's dimension inequality, appending `n - p - q` coefficients
to the `q` old equations gives exactly codimension `n - p`. -/
theorem criticalCoefficientLeaf_codimension
    (hdim : p + q < n) :
    q + (n - p - q) = n - p := by
  omega

private theorem carrier_castCodimension
    {r s : ℕ} (e : r = s) (K : LionCarpetedLeaf G n r) :
    (cast (congrArg (LionCarpetedLeaf G n) e) K).carrier = K.carrier := by
  cases e
  rfl

/-- The uncast regular zero-section leaf associated with one coefficient
selection.  Its displayed codimension is definitionally
`q + (n - p - q)`. -/
def selectedCriticalCoefficientLeafRaw
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (selection : CriticalCoefficientSelection n q p) :
    LionCarpetedLeaf G n (q + (n - p - q)) :=
  L.regularZeroSectionLeaf hG hsmooth hderiv
    (L.selectedCriticalCoefficientTuple g center height selection)
    (L.selectedCriticalCoefficientTuple_mem
      hG hderiv g hg center hheight selection)

/-- One member of Lion's finite regular-minor cover, presented at its exact
source codimension `n - p`. -/
def selectedCriticalCoefficientLeaf
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (selection : CriticalCoefficientSelection n q p) :
    LionCarpetedLeaf G n (n - p) :=
  cast (congrArg (LionCarpetedLeaf G n)
      (criticalCoefficientLeaf_codimension hdim))
    (L.selectedCriticalCoefficientLeafRaw
      hG hsmooth hderiv g hg center hheight selection)

/-- The generic-parameter conclusion used at this exact point in Lion's
proof: at every point of `S_a`, some `n - p - q` critical coefficients,
together with the old equations, have full-rank derivative. -/
def HasCriticalTraceRegularCoefficientSelection
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) : Prop :=
  ∀ x ∈ L.criticalTrace g center height,
    ∃ selection : CriticalCoefficientSelection n q p,
      Function.Surjective
        (fderiv ℝ
          (L.definingTupleAppend
            (L.selectedCriticalCoefficientTuple
              g center height selection)) x)

/-- A critical-trace point at which the selected tuple has full appended
rank belongs to the corresponding regular zero-section leaf. -/
theorem mem_selectedCriticalCoefficientLeaf_of_mem_criticalTrace
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (selection : CriticalCoefficientSelection n q p)
    {x : RealEuclidean n}
    (hx : x ∈ L.criticalTrace g center height)
    (hsurj : Function.Surjective
      (fderiv ℝ
        (L.definingTupleAppend
          (L.selectedCriticalCoefficientTuple
            g center height selection)) x)) :
    x ∈ (L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).carrier := by
  have hxcarrier : x ∈ L.carrier := hx.1.1
  have hcoeff : ∀ cols : Fin ((q + p) + 1) ↪ Fin n,
      L.criticalCoefficient g center height cols x = 0 :=
    (L.criticalMinorSum_eq_zero_iff g center height x).1 hx.2
  have htuplezero :
      L.selectedCriticalCoefficientTuple g center height selection x = 0 := by
    funext i
    exact hcoeff (selection i)
  have hxraw : x ∈ (L.selectedCriticalCoefficientLeafRaw
      hG hsmooth hderiv g hg center hheight selection).carrier := by
    rw [selectedCriticalCoefficientLeafRaw,
      L.regularZeroSectionLeaf_carrier hG hsmooth hderiv
        (L.selectedCriticalCoefficientTuple g center height selection)
        (L.selectedCriticalCoefficientTuple_mem
          hG hderiv g hg center hheight selection)]
    exact ⟨hxcarrier, htuplezero, hsurj⟩
  unfold selectedCriticalCoefficientLeaf
  rw [carrier_castCodimension
    (criticalCoefficientLeaf_codimension hdim)
    (L.selectedCriticalCoefficientLeafRaw
      hG hsmooth hderiv g hg center hheight selection)]
  exact hxraw

/-- Only finitely many regular zero-section leaves arise from the possible
coefficient selections. -/
theorem finite_range_selectedCriticalCoefficientLeaf
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n) :
    (Set.range fun selection : CriticalCoefficientSelection n q p ↦
      L.selectedCriticalCoefficientLeaf
        hG hsmooth hderiv g hg center hheight hdim selection).Finite :=
  Set.finite_range _

/-- The exact pointwise rank-selection consequence of transversality gives
Lion's finite cover of the critical trace by codimension `n - p` leaves. -/
theorem criticalTrace_subset_iUnion_selectedCriticalCoefficientLeaf_carrier
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (hselection :
      L.HasCriticalTraceRegularCoefficientSelection g center height) :
    L.criticalTrace g center height ⊆
      ⋃ selection : CriticalCoefficientSelection n q p,
        (L.selectedCriticalCoefficientLeaf
          hG hsmooth hderiv g hg center hheight hdim selection).carrier := by
  intro x hx
  obtain ⟨selection, hsurj⟩ := hselection x hx
  exact Set.mem_iUnion.2 ⟨selection,
    L.mem_selectedCriticalCoefficientLeaf_of_mem_criticalTrace
      hG hsmooth hderiv g hg center hheight hdim selection hx hsurj⟩

end LionCarpetedLeaf

end AbelFormalization
