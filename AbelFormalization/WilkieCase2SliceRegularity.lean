import AbelFormalization.Wilkie28ExceptionalMathlibOnly
import AbelFormalization.WilkieRegularSliceLinearBridge
import AbelFormalization.SmoothGeometricFamily
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Case 2: regularity and geometry of an attained coordinate slice

The exceptional-value condition makes the augmented derivative regular at
*every* point of the selected level, not merely at the point used to select
the value.  The first theorem isolates this direct consequence of the
definition.  The second theorem transports regularity through a fixed
coordinate insertion, and records nonemptiness, boundedness, and openness of
the ball slice.  Its coordinate-insertion premises are stated at precisely
the derivative and kernel-range identities needed by the chain rule.

The tuple lemmas at the end prove the two algebraic insertion identities for
`Fin.insertNth`.  They can be used when specializing the slice theorem to
visible Euclidean coordinates.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Avoiding the exceptional value makes the augmented derivative surjective
at every attained point of the corresponding fiber slice. -/
theorem wilkie28_augmented_surjective_of_not_exceptional
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K) (b : ℝ)
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet F f a)
    {x : E} (hFx : F x = a) (hfx : f x = b) :
    Function.Surjective
      (fun v : E ↦ (fderiv ℝ F x v, fderiv ℝ f x v)) := by
  by_contra hsingular
  exact hb ⟨x, hFx, hfx, hsingular⟩

/-- The actual fiber after inserting a fixed visible coordinate and
restricting to an ambient ball. -/
def wilkieCase2BallSliceFiber
    {E E' K : Type*} [PseudoMetricSpace E]
    (F : E → K) (a : K) (insert : E' → E)
    (center : E) (radius : ℝ) : Set E' :=
  {y | F (insert y) = a ∧ insert y ∈ Metric.ball center radius}

/-- Analytic and metric content of the Case 2 coordinate slice.  The
`hkernel` premise is the derivative-level coordinate-insertion identity:
every zero-pivot direction is in the range of `direction`.  The `hcover`
premise is its value-level counterpart, while `drop` gives a boundedness
transport without requiring an inverse on the entire ambient space. -/
theorem wilkie_case2_ball_slice_regular_nonempty_bounded
    {E E' K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K) (b : ℝ)
    (center : E) (radius : ℝ)
    (insert : E' → E) (direction : E' →L[ℝ] E)
    (drop : E →L[ℝ] E')
    (hFdiff : ∀ x : E, DifferentiableAt ℝ F x)
    (hregular : ∀ x : E, F x = a →
      Function.Surjective (fderiv ℝ F x))
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet F f a)
    (hfixed : ∀ y : E', f (insert y) = b)
    (hinsert : ∀ y : E', HasFDerivAt insert direction y)
    (hkernel : ∀ y : E', ∀ v : E,
      fderiv ℝ f (insert y) v = 0 →
      ∃ w : E', direction w = v)
    (hcover : ∀ x : E, f x = b → ∃ y : E', insert y = x)
    (hdrop : ∀ y : E', drop (insert y) = y)
    (x : E) (hxF : F x = a)
    (hxBall : x ∈ Metric.ball center radius) (hxf : f x = b) :
    (∀ y ∈ wilkieCase2BallSliceFiber F a insert center radius,
      Function.Surjective (fderiv ℝ (F ∘ insert) y)) ∧
    (wilkieCase2BallSliceFiber F a insert center radius).Nonempty ∧
    Bornology.IsBounded
      (wilkieCase2BallSliceFiber F a insert center radius) ∧
    IsOpen (insert ⁻¹' Metric.ball center radius) := by
  let X : Set E :=
    {z | F z = a ∧ z ∈ Metric.ball center radius}
  let Y : Set E' := wilkieCase2BallSliceFiber F a insert center radius
  have hXbounded : Bornology.IsBounded X :=
    Metric.isBounded_ball.subset (by
      intro z hz
      exact hz.2)
  have hYsubsetDrop : Y ⊆ drop '' X := by
    intro y hy
    exact ⟨insert y, hy, hdrop y⟩
  have hYbounded : Bornology.IsBounded Y :=
    (drop.lipschitzWith.isBounded_image hXbounded).subset hYsubsetDrop
  have hYnonempty : Y.Nonempty := by
    obtain ⟨y, hy⟩ := hcover x hxf
    refine ⟨y, ?_⟩
    change F (insert y) = a ∧ insert y ∈ Metric.ball center radius
    rw [hy]
    exact ⟨hxF, hxBall⟩
  have hinsertContinuous : Continuous insert := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hinsert y).continuousAt
  refine ⟨?_, hYnonempty, hYbounded,
    Metric.isOpen_ball.preimage hinsertContinuous⟩
  intro y hy
  have haug : Function.Surjective
      (fun v : E ↦
        (fderiv ℝ F (insert y) v, fderiv ℝ f (insert y) v)) :=
    wilkie28_augmented_surjective_of_not_exceptional
      F f a b hb hy.1 (hfixed y)
  have hrestricted : Function.Surjective
      (fun w : E' ↦ fderiv ℝ F (insert y) (direction w)) :=
    surjective_restricted_map_of_surjective_augmented
      (fderiv ℝ F (insert y)) (fderiv ℝ f (insert y))
      direction (0 : ℝ) haug (hkernel y)
  have hchain : fderiv ℝ (F ∘ insert) y =
      (fderiv ℝ F (insert y)).comp direction :=
    ((hFdiff (insert y)).hasFDerivAt.comp y (hinsert y)).fderiv
  rw [hchain]
  exact hrestricted

/-- At a fixed pivot, deleting the pivot coordinates recovers the inserted
tuple. -/
theorem fin_removeNth_insertNth_fixed
    {m : ℕ} (i : Fin (m + 1)) (b : ℝ) (u : Fin m → ℝ) :
    i.removeNth (Fin.insertNth (α := fun _ ↦ ℝ) i b u) = u := by
  funext j
  exact Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) i b u j

/-- A tuple with fixed pivot value is in the range of insertion.  This is
the exact value-level premise `hcover` for a visible-coordinate slice. -/
theorem fin_insertNth_covers_fixed_pivot
    {m : ℕ} (i : Fin (m + 1)) (b : ℝ)
    (v : Fin (m + 1) → ℝ) (hv : v i = b) :
    ∃ u : Fin m → ℝ, Fin.insertNth i b u = v := by
  refine ⟨i.removeNth v, ?_⟩
  exact ((Fin.eq_insertNth_iff).mpr ⟨hv, rfl⟩).symm

/-- Every zero-pivot direction is in the range of zero insertion.  This is
the tuple algebra behind the derivative-level premise `hkernel`. -/
theorem fin_insertNth_zero_covers_zero_pivot
    {m : ℕ} (i : Fin (m + 1))
    (v : Fin (m + 1) → ℝ) (hv : v i = 0) :
    ∃ u : Fin m → ℝ, Fin.insertNth i 0 u = v := by
  exact fin_insertNth_covers_fixed_pivot i 0 v hv

/-- Insert the fixed value in one visible coordinate, retaining all hidden
coordinates.  The product presentation avoids a source-column permutation
while proving the slice regularity itself. -/
def wilkieCase2VisibleInsert {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ) :
    ((Fin m → ℝ) × (Fin q → ℝ)) →
      ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) :=
  fun y ↦ (Fin.insertNth i b y.1, y.2)

/-- The linear direction map of `wilkieCase2VisibleInsert`. -/
def wilkieCase2VisibleDirectionLinear {m q : ℕ}
    (i : Fin (m + 1)) :
    ((Fin m → ℝ) × (Fin q → ℝ)) →ₗ[ℝ]
      ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) where
  toFun y := (Fin.insertNth i 0 y.1, y.2)
  map_add' y z := by
    apply Prod.ext
    · funext j
      refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp
    · rfl
  map_smul' c y := by
    apply Prod.ext
    · funext j
      refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp
    · rfl

/-- All spaces are finite-dimensional real normed spaces, so the algebraic
zero-coordinate insertion is automatically continuous. -/
def wilkieCase2VisibleDirection {m q : ℕ}
    (i : Fin (m + 1)) :
    ((Fin m → ℝ) × (Fin q → ℝ)) →L[ℝ]
      ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) :=
  (wilkieCase2VisibleDirectionLinear (q := q) i).toContinuousLinearMap

/-- Delete the chosen visible coordinate. -/
def wilkieCase2VisibleDropLinear {m q : ℕ}
    (i : Fin (m + 1)) :
    ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) →ₗ[ℝ]
      ((Fin m → ℝ) × (Fin q → ℝ)) where
  toFun x := (i.removeNth x.1, x.2)
  map_add' x y := by
    apply Prod.ext
    · funext j
      rfl
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · funext j
      rfl
    · rfl

/-- Continuous-linear coordinate deletion transports boundedness from the
original ball fiber to the sliced fiber. -/
def wilkieCase2VisibleDrop {m q : ℕ}
    (i : Fin (m + 1)) :
    ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) →L[ℝ]
      ((Fin m → ℝ) × (Fin q → ℝ)) :=
  (wilkieCase2VisibleDropLinear (q := q) i).toContinuousLinearMap

@[simp]
theorem wilkieCase2VisibleDrop_insert {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (y : (Fin m → ℝ) × (Fin q → ℝ)) :
    wilkieCase2VisibleDrop i (wilkieCase2VisibleInsert i b y) = y := by
  apply Prod.ext
  · exact fin_removeNth_insertNth_fixed i b y.1
  · rfl

@[simp]
theorem wilkieCase2VisibleInsert_pivot {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (y : (Fin m → ℝ) × (Fin q → ℝ)) :
    (wilkieCase2VisibleInsert i b y).1 i = b := by
  simp [wilkieCase2VisibleInsert]

/-- The fixed-coordinate insertion is affine with the stated Fréchet
derivative at every point. -/
theorem wilkieCase2VisibleInsert_hasFDerivAt {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (y : (Fin m → ℝ) × (Fin q → ℝ)) :
    HasFDerivAt (wilkieCase2VisibleInsert i b)
      (wilkieCase2VisibleDirection i) y := by
  let offset : (Fin (m + 1) → ℝ) × (Fin q → ℝ) :=
    (Fin.insertNth i b 0, 0)
  have hmap : wilkieCase2VisibleInsert i b =
      (fun z ↦ offset + wilkieCase2VisibleDirection i z) := by
    funext z
    apply Prod.ext
    · funext j
      refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;>
        simp [offset, wilkieCase2VisibleInsert,
          wilkieCase2VisibleDirection,
          wilkieCase2VisibleDirectionLinear]
    · simp [offset, wilkieCase2VisibleInsert,
        wilkieCase2VisibleDirection,
        wilkieCase2VisibleDirectionLinear]
  rw [hmap]
  exact (wilkieCase2VisibleDirection i).hasFDerivAt.const_add offset

/-- The pivot evaluation is itself a continuous linear map; its Fréchet
derivative therefore equals pivot evaluation at every point. -/
def wilkieCase2VisiblePivotLinear {m q : ℕ}
    (i : Fin (m + 1)) :
    ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) →ₗ[ℝ] ℝ where
  toFun x := x.1 i
  map_add' x y := rfl
  map_smul' c x := rfl

def wilkieCase2VisiblePivot {m q : ℕ}
    (i : Fin (m + 1)) :
    ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) →L[ℝ] ℝ :=
  (wilkieCase2VisiblePivotLinear (q := q) i).toContinuousLinearMap

theorem wilkieCase2VisiblePivot_fderiv {m q : ℕ}
    (i : Fin (m + 1))
    (x : (Fin (m + 1) → ℝ) × (Fin q → ℝ)) :
    fderiv ℝ (fun z : (Fin (m + 1) → ℝ) × (Fin q → ℝ) ↦ z.1 i) x =
      wilkieCase2VisiblePivot i :=
  (wilkieCase2VisiblePivot i).hasFDerivAt.fderiv

/-- The derivative-level coordinate-insertion range identity required by
the regular-slice bridge. -/
theorem wilkieCase2VisibleDirection_covers_pivot_kernel {m q : ℕ}
    (i : Fin (m + 1))
    (v : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
    (hv : wilkieCase2VisiblePivot i v = 0) :
    ∃ w : (Fin m → ℝ) × (Fin q → ℝ),
      wilkieCase2VisibleDirection i w = v := by
  have hv' : v.1 i = 0 := hv
  obtain ⟨u, hu⟩ :=
    fin_insertNth_zero_covers_zero_pivot i v.1 hv'
  refine ⟨(u, v.2), ?_⟩
  apply Prod.ext
  · exact hu
  · rfl

/-- The value-level insertion range identity required to transfer an
attained good coordinate value to a nonempty slice. -/
theorem wilkieCase2VisibleInsert_covers_pivot {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (x : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
    (hx : x.1 i = b) :
    ∃ y : (Fin m → ℝ) × (Fin q → ℝ),
      wilkieCase2VisibleInsert i b y = x := by
  obtain ⟨u, hu⟩ := fin_insertNth_covers_fixed_pivot i b x.1 hx
  refine ⟨(u, x.2), ?_⟩
  apply Prod.ext
  · exact hu
  · rfl

/-- Concrete visible-coordinate specialization: a regular fiber point in an
ambient ball with an attained good pivot value produces a nonempty bounded
regular slice, and the inserted part of the ball is open in the lower-arity
source.  The coordinate algebra and affine derivative are discharged above. -/
theorem wilkie_case2_visible_ball_slice_regular_nonempty_bounded
    {m q : ℕ} {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → K)
    (a : K) (i : Fin (m + 1)) (b : ℝ)
    (center : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
    (radius : ℝ)
    (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (hregular : ∀ x, F x = a →
      Function.Surjective (fderiv ℝ F x))
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet
      F (fun x ↦ x.1 i) a)
    (x : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
    (hxF : F x = a)
    (hxBall : x ∈ Metric.ball center radius)
    (hxPivot : x.1 i = b) :
    (∀ y ∈ wilkieCase2BallSliceFiber F a
        (wilkieCase2VisibleInsert i b) center radius,
      Function.Surjective
        (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y)) ∧
    (wilkieCase2BallSliceFiber F a
      (wilkieCase2VisibleInsert i b) center radius).Nonempty ∧
    Bornology.IsBounded
      (wilkieCase2BallSliceFiber F a
        (wilkieCase2VisibleInsert i b) center radius) ∧
    IsOpen ((wilkieCase2VisibleInsert i b) ⁻¹'
      Metric.ball center radius) := by
  have hfixed (y : (Fin m → ℝ) × (Fin q → ℝ)) :
      (wilkieCase2VisibleInsert i b y).1 i = b :=
    wilkieCase2VisibleInsert_pivot i b y
  have hinsertion (y : (Fin m → ℝ) × (Fin q → ℝ)) :
      HasFDerivAt (wilkieCase2VisibleInsert i b)
        (wilkieCase2VisibleDirection i) y :=
    wilkieCase2VisibleInsert_hasFDerivAt i b y
  have hkernel (y : (Fin m → ℝ) × (Fin q → ℝ))
      (v : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
      (hv : fderiv ℝ
          (fun z : (Fin (m + 1) → ℝ) × (Fin q → ℝ) ↦ z.1 i)
          (wilkieCase2VisibleInsert i b y) v = 0) :
      ∃ w : (Fin m → ℝ) × (Fin q → ℝ),
        wilkieCase2VisibleDirection i w = v := by
    rw [wilkieCase2VisiblePivot_fderiv] at hv
    exact wilkieCase2VisibleDirection_covers_pivot_kernel i v hv
  have hcover (z : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
      (hz : z.1 i = b) :
      ∃ y : (Fin m → ℝ) × (Fin q → ℝ),
        wilkieCase2VisibleInsert i b y = z :=
    wilkieCase2VisibleInsert_covers_pivot i b z hz
  have hdrop (y : (Fin m → ℝ) × (Fin q → ℝ)) :
      wilkieCase2VisibleDrop i (wilkieCase2VisibleInsert i b y) = y :=
    wilkieCase2VisibleDrop_insert i b y
  exact wilkie_case2_ball_slice_regular_nonempty_bounded
    F (fun z ↦ z.1 i) a b center radius
    (wilkieCase2VisibleInsert i b)
    (wilkieCase2VisibleDirection i)
    (wilkieCase2VisibleDrop i)
    hFdiff hregular hb hfixed hinsertion hkernel hcover hdrop
    x hxF hxBall hxPivot

end AbelFormalization
