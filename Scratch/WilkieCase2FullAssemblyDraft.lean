import AbelFormalization.WilkieCase2CombinatorialDescent
import AbelFormalization.WilkieCase2SliceRegularity
import AbelFormalization.WilkieCase2FlatJacobianInsertion
import AbelFormalization.Wilkie28ExceptionalWS5Reduction

/-!
# Wilkie Corollary 2.9, Case 2: visible-cylinder slice bridge

Printed page 405 uses a ball `U` in the visible coordinates and the full
restricted fiber `F⁻¹ {a} ∩ π⁻¹ U`.  It does not restrict the hidden
coordinates to an ambient ball.  The visible-cylinder slice below therefore
assumes boundedness of that full restricted fiber.  Its boundedness cannot
follow from boundedness of `U` alone.

The first theorem stages the exact regular, attained, bounded slice.  The
second derives a good attained coordinate from the WS5 unary consequence and
the Theorem 2.8 smooth singular-witness selection, with the exceptional-set
membership stated explicitly.  No axiom or sorry is used.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The source-shaped restricted fiber over a visible target. -/
def wilkieCase2VisibleCylinderFiber {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (Fin m → ℝ)) :
    Set ((Fin m → ℝ) × (Fin q → ℝ)) :=
  {x | F x = a ∧ x.1 ∈ U}

/-- Fixing one visible coordinate in the source-shaped cylinder. -/
def wilkieCase2VisibleCylinderSliceFiber {m q : ℕ}
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (Fin (m + 1) → ℝ))
    (i : Fin (m + 1)) (b : ℝ) :
    Set ((Fin m → ℝ) × (Fin q → ℝ)) :=
  {y | F (wilkieCase2VisibleInsert i b y) = a ∧
    y.1 ∈ (Fin.insertNth i b) ⁻¹' U}

/-- A Theorem 2.8 good coordinate value attained in the bounded original
fiber makes the lower-arity visible-cylinder fiber regular, nonempty, and
bounded.  The sliced visible domain is open. -/
theorem wilkie_case2_visible_cylinder_slice_regular_nonempty_bounded
    {m q : ℕ}
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (Fin (m + 1) → ℝ))
    (hUopen : IsOpen U)
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F a U))
    (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (i : Fin (m + 1)) (b : ℝ)
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet
      F (fun x ↦ x.1 i) a)
    (x : (Fin (m + 1) → ℝ) × (Fin q → ℝ))
    (hx : x ∈ wilkieCase2VisibleCylinderFiber F a U)
    (hxPivot : x.1 i = b) :
    (∀ y ∈ wilkieCase2VisibleCylinderSliceFiber F a U i b,
      Function.Surjective
        (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y)) ∧
    (wilkieCase2VisibleCylinderSliceFiber F a U i b).Nonempty ∧
    Bornology.IsBounded
      (wilkieCase2VisibleCylinderSliceFiber F a U i b) ∧
    IsOpen ((Fin.insertNth i b) ⁻¹' U) := by
  let X := wilkieCase2VisibleCylinderFiber F a U
  let Y := wilkieCase2VisibleCylinderSliceFiber F a U i b
  have hYsubsetDrop : Y ⊆ (wilkieCase2VisibleDrop i) '' X := by
    intro y hy
    refine ⟨wilkieCase2VisibleInsert i b y, ?_,
      wilkieCase2VisibleDrop_insert i b y⟩
    change F (wilkieCase2VisibleInsert i b y) = a ∧
      (wilkieCase2VisibleInsert i b y).1 ∈ U
    change F (wilkieCase2VisibleInsert i b y) = a ∧
      y.1 ∈ (Fin.insertNth i b) ⁻¹' U at hy
    simpa only [wilkieCase2VisibleInsert, Set.mem_preimage] using hy
  have hYbounded : Bornology.IsBounded Y :=
    ((wilkieCase2VisibleDrop i).lipschitzWith.isBounded_image hbounded).subset
      hYsubsetDrop
  have hYnonempty : Y.Nonempty := by
    obtain ⟨y, hy⟩ :=
      wilkieCase2VisibleInsert_covers_pivot i b x hxPivot
    refine ⟨y, ?_⟩
    change F (wilkieCase2VisibleInsert i b y) = a ∧
      (wilkieCase2VisibleInsert i b y).1 ∈ U
    change F x = a ∧ x.1 ∈ U at hx
    rw [hy]
    exact hx
  have hinsertionContinuous :
      Continuous (wilkieCase2_coordinateInsert i b) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (wilkieCase2_coordinateInsert_hasFDerivAt i b v).continuousAt
  have hU'sOpen : IsOpen ((Fin.insertNth i b) ⁻¹' U) := by
    change IsOpen ((wilkieCase2_coordinateInsert i b) ⁻¹' U)
    exact hUopen.preimage hinsertionContinuous
  refine ⟨?_, hYnonempty, hYbounded, hU'sOpen⟩
  intro y hy
  have hyF : F (wilkieCase2VisibleInsert i b y) = a := hy.1
  have haug : Function.Surjective
      (fun v : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) ↦
        (fderiv ℝ F (wilkieCase2VisibleInsert i b y) v,
         fderiv ℝ (fun z : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) ↦
           z.1 i) (wilkieCase2VisibleInsert i b y) v)) :=
    wilkie28_augmented_surjective_of_not_exceptional
      F (fun z ↦ z.1 i) a b hb hyF
      (wilkieCase2VisibleInsert_pivot i b y)
  have hrestricted : Function.Surjective
      (fun w : ((Fin m → ℝ) × (Fin q → ℝ)) ↦
        fderiv ℝ F (wilkieCase2VisibleInsert i b y)
          (wilkieCase2VisibleDirection i w)) := by
    apply surjective_restricted_map_of_surjective_augmented
      (fderiv ℝ F (wilkieCase2VisibleInsert i b y))
      (fderiv ℝ (fun z : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) ↦
        z.1 i) (wilkieCase2VisibleInsert i b y))
      (wilkieCase2VisibleDirection i) (0 : ℝ) haug
    intro v hv
    rw [wilkieCase2VisiblePivot_fderiv] at hv
    exact wilkieCase2VisibleDirection_covers_pivot_kernel i v hv
  have hchain : fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y =
      (fderiv ℝ F (wilkieCase2VisibleInsert i b y)).comp
        (wilkieCase2VisibleDirection i) :=
    ((hFdiff (wilkieCase2VisibleInsert i b y)).hasFDerivAt.comp y
      (wilkieCase2VisibleInsert_hasFDerivAt i b y)).fderiv
  rw [hchain]
  exact hrestricted

/-- The 2.8/WS5 choice step on the source-shaped fiber.  Membership of the
singular-value set is the derivative-closure result; smooth witness selection
is the remaining source input. -/
theorem wilkie_case2_visible_cylinder_exists_good_slice_of_WS5_selection
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {m q : ℕ}
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (Fin (m + 1) → ℝ))
    (hUopen : IsOpen U)
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F a U))
    (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (hregular : ∀ x, F x = a →
      Function.Surjective (fderiv ℝ F x))
    (hvisible : ((fun x ↦ x.1) ''
      wilkieCase2VisibleCylinderFiber F a U).Infinite)
    (hBmem : ∀ i : Fin (m + 1),
      {v : RealEuclidean 1 |
        v 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet
          F (fun x ↦ x.1 i) a} ∈ C 1)
    (hselection : ∀ i : Fin (m + 1),
      Wilkie28MathlibOnly.SmoothSingularWitnessSelection
        F (fun x ↦ x.1 i) a) :
    ∃ (i : Fin (m + 1)) (b : ℝ)
      (x : (Fin (m + 1) → ℝ) × (Fin q → ℝ)),
      x ∈ wilkieCase2VisibleCylinderFiber F a U ∧
      x.1 i = b ∧
      (∀ y ∈ wilkieCase2VisibleCylinderSliceFiber F a U i b,
        Function.Surjective
          (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y)) ∧
      (wilkieCase2VisibleCylinderSliceFiber F a U i b).Nonempty ∧
      Bornology.IsBounded
        (wilkieCase2VisibleCylinderSliceFiber F a U i b) ∧
      IsOpen ((Fin.insertNth i b) ⁻¹' U) := by
  have hbad (i : Fin (m + 1)) :
      (Wilkie28MathlibOnly.exceptionalParameterSet
        F (fun x ↦ x.1 i) a).Finite := by
    apply wilkie28_exceptionalCoordinateValues_finite_of_WS5_and_selection
      hC F (fun x ↦ x.1 i) a hFdiff
    · intro x
      change DifferentiableAt ℝ (wilkieCase2VisiblePivot i) x
      exact (wilkieCase2VisiblePivot i).differentiableAt
    · exact hregular
    · exact hBmem i
    · exact hselection i
  obtain ⟨i, x, hx, hxGood⟩ :=
    exists_fiber_point_with_good_visible_coordinate
      (fun z : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) ↦ z.1)
      hvisible
      (fun i ↦ Wilkie28MathlibOnly.exceptionalParameterSet
        F (fun z ↦ z.1 i) a) hbad
  obtain ⟨hreg, hnonempty, hsBounded, hsOpen⟩ :=
    wilkie_case2_visible_cylinder_slice_regular_nonempty_bounded
      F a U hUopen hbounded hFdiff i (x.1 i) hxGood x hx rfl
  exact ⟨i, x.1 i, x, hx, rfl, hreg, hnonempty, hsBounded, hsOpen⟩

end AbelFormalization
