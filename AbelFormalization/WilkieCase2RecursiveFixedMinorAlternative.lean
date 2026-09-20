import AbelFormalization.WilkieCase2VisibleCylinderChoice
import AbelFormalization.WilkieCase2ProductFlatEquiv
import AbelFormalization.WilkieFiniteVisibleProjectionCase
import AbelFormalization.WilkieZeroVisibleVerticalMinor
import AbelFormalization.WilkieVerticalMinorMissingProjectionInterval
import AbelFormalization.WilkieCase2CylinderMinorIntervalLift
import AbelFormalization.WilkieCase2HiddenMinorCast

/-!
# Recursive Case 2 fixed-minor alternative

`wilkieCase2RecursiveAlternative` is the invariant that survives every
visible-coordinate slice: either a fixed selected minor takes an initial
squared interval on the current restricted fiber, or the fixed hidden-column
minor is nonzero at a point of that fiber. The final projection fork is
proved below.

The visible-cylinder choice has to retain the attained good-value condition
to prove global regularity of the sliced map; regularity only on the restricted
cylinder is insufficient for the next Case 1 or vertical-fork application.
The hidden-column square identity is supplied by the maintained cast bridge.
The conditional recursion assumes WS5 exceptional-set membership and smooth
singular-witness selection for every coordinate map at each arity. A further
reachable-stage specialization can restrict these to affine descendants of
the original geometric-family map.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Flat presentation of a product-coordinate map. -/
def wilkieCase2Flatten {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q) :
    RealEuclidean (m + q) → RealEuclidean q :=
  F ∘ (wilkieCase2ProductFlatEquiv m q).symm

/-- The two certificates which are preserved through Case 2 descent. -/
def wilkieCase2RecursiveAlternative {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (RealEuclidean m)) : Prop :=
  (∃ cols : Fin q ↪ Fin (m + q), ∃ η : ℝ,
    0 < η ∧ Set.Icc (0 : ℝ) η ⊆
      (fun z ↦ (standardJacobianColumnMinor
        (wilkieCase2Flatten F) cols z) ^ 2) ''
        wilkieFiberOver (wilkieCase2Flatten F) a U) ∨
  (∃ z ∈ wilkieFiberOver (wilkieCase2Flatten F) a U,
    standardJacobianColumnMinor (wilkieCase2Flatten F)
      (Fin.natAddEmb m) z ≠ 0)

/-- The left projection of visible-first concatenation. -/
theorem wilkieCase2Flatten_takeLeft {m q : ℕ}
    (y : ((Fin m → ℝ) × (Fin q → ℝ))) :
    realEuclideanTakeLeft (wilkieCase2ProductFlatEquiv m q y) = y.1 := by
  funext i
  exact wilkieCase2ProductFlatEquiv_visible y i

/-- Literal equivalence of the source-shaped cylinder in product and flat
coordinates. -/
theorem wilkieCase2Flatten_cylinder_image {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (RealEuclidean m)) :
    (wilkieCase2ProductFlatEquiv m q) ''
        wilkieCase2VisibleCylinderFiber F a U =
      wilkieFiberOver (wilkieCase2Flatten F) a U := by
  let E := wilkieCase2ProductFlatEquiv m q
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change F y = a ∧ y.1 ∈ U at hy
    change F (E.symm (E y)) = a ∧
      realEuclideanTakeLeft (E y) ∈ U
    refine ⟨by simpa only [E.symm_apply_apply] using hy.1, ?_⟩
    rw [show realEuclideanTakeLeft (E y) = y.1 from
      wilkieCase2Flatten_takeLeft y]
    exact hy.2
  · intro hz
    refine ⟨E.symm z, ?_, E.apply_symm_apply z⟩
    change F (E.symm z) = a ∧ (E.symm z).1 ∈ U
    change F (E.symm z) = a ∧ realEuclideanTakeLeft z ∈ U at hz
    have htake := wilkieCase2Flatten_takeLeft (E.symm z)
    rw [E.apply_symm_apply] at htake
    exact ⟨hz.1, htake.symm ▸ hz.2⟩

/-- Transfer regularity of a product map to its flat presentation. -/
theorem wilkieCase2Flatten_regular
    {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (hFdiff : ∀ y, DifferentiableAt ℝ F y)
    (a : RealEuclidean q)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y)) :
    ∀ z, wilkieCase2Flatten F z = a →
      Function.Surjective (fderiv ℝ (wilkieCase2Flatten F) z) := by
  let E := wilkieCase2ProductFlatEquiv m q
  intro z hz
  let y := E.symm z
  have hchain : fderiv ℝ (wilkieCase2Flatten F) z =
      (fderiv ℝ F y).comp
        (E.symm : RealEuclidean (m + q) →L[ℝ]
          ((Fin m → ℝ) × (Fin q → ℝ))) := by
    change fderiv ℝ (F ∘ E.symm) z =
      (fderiv ℝ F y).comp
        (E.symm : RealEuclidean (m + q) →L[ℝ]
          ((Fin m → ℝ) × (Fin q → ℝ)))
    exact ((hFdiff y).hasFDerivAt.comp z E.symm.hasFDerivAt).fderiv
  intro target
  obtain ⟨v, hv⟩ := hregular y hz target
  refine ⟨E v, ?_⟩
  rw [hchain]
  change (fderiv ℝ F y) (E.symm (E v)) = target
  rw [E.symm_apply_apply]
  exact hv

/-- Flattening commutes with the fixed visible-coordinate slice. -/
theorem wilkieCase2Flatten_slice_eq {m q : ℕ}
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ) :
    wilkieCase2Flatten (F ∘ wilkieCase2VisibleInsert i b) =
      (wilkieCase2Flatten F) ∘ wilkieCase2FlatCastInsert i b := by
  exact (wilkieCase2_flat_slice_map_eq F i b).symm

/-- The visible images agree in product and flat presentations. -/
theorem wilkieCase2Flatten_visible_image {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (RealEuclidean m)) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F) a U =
      (fun y : (Fin m → ℝ) × (Fin q → ℝ) ↦ y.1) ''
        wilkieCase2VisibleCylinderFiber F a U := by
  rw [← wilkieCase2Flatten_cylinder_image]
  ext u
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, hzu⟩
    exact ⟨y, hy, (wilkieCase2Flatten_takeLeft y).symm.trans hzu⟩
  · rintro ⟨y, hy, hyu⟩
    exact ⟨wilkieCase2ProductFlatEquiv m q y,
      ⟨y, hy, rfl⟩, (wilkieCase2Flatten_takeLeft y).trans hyu⟩

/-- Good values make the *whole* sliced level map regular, including points
outside the restricted visible cylinder. -/
theorem wilkieCase2VisibleInsert_globalRegular_of_good
    {m q : ℕ}
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (i : Fin (m + 1)) (b : ℝ)
    (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet
      F (fun x ↦ x.1 i) a) :
    ∀ y, F (wilkieCase2VisibleInsert i b y) = a →
      Function.Surjective
        (fderiv ℝ (F ∘ wilkieCase2VisibleInsert i b) y) := by
  intro y hyF
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

/-- Affine coordinate insertion preserves convexity of the visible target.
The open slice can therefore still be used as a connected target in the final
vertical-minor fork. -/
theorem wilkieCase2VisibleSlice_convex
    {m : ℕ} (U : Set (RealEuclidean (m + 1)))
    (hU : Convex ℝ U) (i : Fin (m + 1)) (b : ℝ) :
    Convex ℝ ((Fin.insertNth i b) ⁻¹' U) := by
  rw [convex_iff_add_mem]
  intro x hx y hy α β hα hβ hsum
  have hinsertion : Fin.insertNth i b (α • x + β • y) =
      α • Fin.insertNth i b x + β • Fin.insertNth i b y := by
    funext j
    refine Fin.succAboveCases i ?_ (fun t ↦ ?_) j
    · simp only [Fin.insertNth_apply_same, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      calc
        b = (α + β) * b := by rw [hsum]; ring
        _ = α * b + β * b := by ring
    · simp only [Fin.insertNth_apply_succAbove, Pi.add_apply,
        Pi.smul_apply]
  change Fin.insertNth i b (α • x + β • y) ∈ U
  rw [hinsertion]
  exact hU hx hy hα hβ hsum

/-- The concrete visible-coordinate insertion is affine, hence smooth. -/
theorem wilkieCase2VisibleInsert_contDiff
    {m q : ℕ} (i : Fin (m + 1)) (b : ℝ) :
    ContDiff ℝ 1 (wilkieCase2VisibleInsert (q := q) i b) := by
  let offset : (Fin (m + 1) → ℝ) × (Fin q → ℝ) :=
    (Fin.insertNth i b 0, 0)
  have hmap : wilkieCase2VisibleInsert i b =
      (fun z ↦ offset + wilkieCase2VisibleDirection i z) := by
    funext z
    apply Prod.ext
    · funext j
      refine Fin.succAboveCases i ?_ (fun t ↦ ?_) j <;>
        simp [offset, wilkieCase2VisibleInsert,
          wilkieCase2VisibleDirection,
          wilkieCase2VisibleDirectionLinear]
    · simp [offset, wilkieCase2VisibleInsert,
        wilkieCase2VisibleDirection,
        wilkieCase2VisibleDirectionLinear]
  rw [hmap]
  exact contDiff_const.add (wilkieCase2VisibleDirection i).contDiff

/-- Conditional fixed-minor assembly for every visible arity.  `hBmem` is
the WS5 membership of each Theorem 2.8 exceptional unary set encountered by
the recursive slicing; `hselection` is the smooth singular-witness selection.
The hidden-column cast and `C¹` stability of affine slices are proved by
maintained/local analytic lemmas. -/
theorem wilkieCase2_recursive_fixedMinorAlternative
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {q : ℕ} (hq : 0 < q)
    (hBmem : ∀ (m : ℕ)
      (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
      (a : RealEuclidean q) (i : Fin (m + 1)),
      {v : RealEuclidean 1 |
        v 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet
          F (fun x ↦ x.1 i) a} ∈ C 1)
    (hselection : ∀ (m : ℕ)
      (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
      (a : RealEuclidean q) (i : Fin (m + 1)),
      Wilkie28MathlibOnly.SmoothSingularWitnessSelection
        F (fun x ↦ x.1 i) a) :
    ∀ (m : ℕ)
      (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
      (a : RealEuclidean q) (U : Set (RealEuclidean m)),
      ContDiff ℝ 1 F → IsOpen U → Convex ℝ U →
      (∀ y, F y = a → Function.Surjective (fderiv ℝ F y)) →
      Bornology.IsBounded (wilkieCase2VisibleCylinderFiber F a U) →
      (wilkieCase2VisibleCylinderFiber F a U).Nonempty →
      wilkieCase2RecursiveAlternative F a U := by
  intro m
  induction m with
  | zero =>
      intro F a U hF hUopen hUconvex hregular hbounded hnonempty
      obtain ⟨y, hy⟩ := hnonempty
      let E := wilkieCase2ProductFlatEquiv 0 q
      let H := wilkieCase2Flatten F
      have hz : E y ∈ wilkieFiberOver H a U := by
        rw [← wilkieCase2Flatten_cylinder_image]
        exact ⟨y, hy, rfl⟩
      have hFdiff : ∀ w, DifferentiableAt ℝ F w :=
        fun w ↦ (hF.differentiable (by simp)).differentiableAt
      have hH : ContDiff ℝ 1 H := hF.comp E.symm.contDiff
      have hHdiff : DifferentiableAt ℝ H (E y) :=
        (hH.differentiable (by simp)).differentiableAt
      have hHregular := wilkieCase2Flatten_regular F hFdiff a hregular
      right
      exact ⟨E y, hz,
        wilkieZeroVisible_verticalMinor_ne_zero_of_regular
          hHdiff (hHregular (E y) hz.1)⟩
  | succ m ih =>
      intro F a U hF hUopen hUconvex hregular hbounded hnonempty
      let E := wilkieCase2ProductFlatEquiv (m + 1) q
      let H := wilkieCase2Flatten F
      let X := wilkieCase2VisibleCylinderFiber F a U
      have hFdiff : ∀ w, DifferentiableAt ℝ F w :=
        fun w ↦ (hF.differentiable (by simp)).differentiableAt
      have hH : ContDiff ℝ 1 H := hF.comp E.symm.contDiff
      have hHdiff : ∀ z ∈ wilkieFiberOver H a U,
          DifferentiableAt ℝ H z := by
        intro z _
        exact (hH.differentiable (by simp)).differentiableAt
      have hHregular := wilkieCase2Flatten_regular F hFdiff a hregular
      have hHbounded : Bornology.IsBounded (wilkieFiberOver H a U) := by
        rw [← wilkieCase2Flatten_cylinder_image]
        exact E.lipschitzWith.isBounded_image hbounded
      obtain ⟨y, hy⟩ := hnonempty
      have hz : E y ∈ wilkieFiberOver H a U := by
        rw [← wilkieCase2Flatten_cylinder_image]
        exact ⟨y, hy, rfl⟩
      by_cases hfinite : ((fun w : ((Fin (m + 1) → ℝ) ×
          (Fin q → ℝ)) ↦ w.1) '' X).Finite
      · have hfiniteFlat :
            (realEuclideanTakeLeft '' wilkieFiberOver H a U).Finite := by
          rw [wilkieCase2Flatten_visible_image]
          exact hfinite
        obtain ⟨cols, η, hη, hinterval⟩ :=
          wilkieFiniteVisibleImage_sameMinor_squared_interval
            (Nat.succ_pos m) hH a hUopen hHregular hHbounded
            hfiniteFlat hz
        left
        exact ⟨cols, η, hη, hinterval⟩
      · have hinfinite : ((fun w : ((Fin (m + 1) → ℝ) ×
            (Fin q → ℝ)) ↦ w.1) '' X).Infinite := hfinite
        have hbad (i : Fin (m + 1)) :
            (Wilkie28MathlibOnly.exceptionalParameterSet
              F (fun w ↦ w.1 i) a).Finite := by
          apply wilkie28_exceptionalCoordinateValues_finite_of_WS5_and_selection
            hC F (fun w ↦ w.1 i) a hFdiff
          · intro w
            change DifferentiableAt ℝ (wilkieCase2VisiblePivot i) w
            exact (wilkieCase2VisiblePivot i).differentiableAt
          · exact hregular
          · exact hBmem m F a i
          · exact hselection m F a i
        obtain ⟨i, x, hx, hb⟩ :=
          exists_fiber_point_with_good_visible_coordinate
            (fun w : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) ↦ w.1)
            hinfinite
            (fun i ↦ Wilkie28MathlibOnly.exceptionalParameterSet
              F (fun w ↦ w.1 i) a) hbad
        let b := x.1 i
        let F' := F ∘ wilkieCase2VisibleInsert i b
        let U' : Set (RealEuclidean m) :=
          (wilkieCase2_coordinateInsert i b) ⁻¹' U
        obtain ⟨_, hnonempty', hbounded', hUopen'⟩ :=
          wilkie_case2_visible_cylinder_slice_regular_nonempty_bounded
            F a U hUopen hbounded hFdiff i b hb x hx rfl
        have hF' : ContDiff ℝ 1 F' :=
          hF.comp (wilkieCase2VisibleInsert_contDiff i b)
        have hUconvex' : Convex ℝ U' :=
          wilkieCase2VisibleSlice_convex U hUconvex i b
        have hregular' : ∀ w, F' w = a →
            Function.Surjective (fderiv ℝ F' w) :=
          wilkieCase2VisibleInsert_globalRegular_of_good
            F a i b hFdiff hb
        have hbounded'' : Bornology.IsBounded
            (wilkieCase2VisibleCylinderFiber F' a U') := by
          simpa only [F', U', wilkieCase2VisibleCylinderFiber,
            wilkieCase2VisibleCylinderSliceFiber,
            wilkieCase2VisibleInsert, wilkieCase2_coordinateInsert,
            Function.comp_apply, Set.mem_preimage] using hbounded'
        have hnonempty'' :
            (wilkieCase2VisibleCylinderFiber F' a U').Nonempty := by
          simpa only [F', U', wilkieCase2VisibleCylinderFiber,
            wilkieCase2VisibleCylinderSliceFiber,
            wilkieCase2VisibleInsert, wilkieCase2_coordinateInsert,
            Function.comp_apply, Set.mem_preimage] using hnonempty'
        have hUopen'' : IsOpen U' := hUopen'
        have hrec := ih F' a U' hF' hUopen'' hUconvex'
          hregular' hbounded'' hnonempty''
        rcases hrec with ⟨cols, η, hη, hinterval⟩ | ⟨z, hz', hminor'⟩
        · have hsliceEq := wilkieCase2Flatten_slice_eq F i b
          have hinterval' : Set.Icc (0 : ℝ) η ⊆
              (fun v ↦ (standardJacobianColumnMinor
                (H ∘ wilkieCase2FlatCastInsert i b) cols v) ^ 2) ''
                wilkieFiberOver (H ∘ wilkieCase2FlatCastInsert i b)
                  a (wilkieCase2VisibleCylinderSlice i b U) := by
            simpa only [H, F', U', wilkieCase2VisibleCylinderSlice,
              wilkieCase2Flatten_slice_eq] using hinterval
          obtain ⟨_, hη', hlift⟩ :=
            wilkieCase2_cylinderSliceMinor_squared_interval_lift
              H a i b U hUopen cols (Equiv.refl (Fin q))
              hHdiff hη hinterval'
          left
          exact ⟨cols.trans (wilkieCase2CylinderColumnInsert (q := q) i),
            η, hη', hlift⟩
        · have hzLower : z ∈
              wilkieFiberOver (H ∘ wilkieCase2FlatCastInsert i b)
                a (wilkieCase2VisibleCylinderSlice i b U) := by
            simpa only [H, F', U', wilkieCase2VisibleCylinderSlice,
              wilkieCase2Flatten_slice_eq] using hz'
          have hzParent : wilkieCase2FlatCastInsert i b z ∈
              wilkieFiberOver H a U :=
            wilkieCase2CylinderFiber_insert_image_subset H a i b U
              ⟨z, hzLower, rfl⟩
          have hminorLower : standardJacobianColumnMinor
              (H ∘ wilkieCase2FlatCastInsert i b)
              (Fin.natAddEmb m) z ≠ 0 := by
            simpa only [H, F', wilkieCase2Flatten_slice_eq] using hminor'
          have hminorParent : standardJacobianColumnMinor H
              (Fin.natAddEmb (m + 1))
              (wilkieCase2FlatCastInsert i b z) ≠ 0 :=
            wilkieCase2_flatVerticalMinor_ne_zero_insert
              H i b z (hHdiff _ hzParent) hminorLower
          right
          exact ⟨wilkieCase2FlatCastInsert i b z,
            hzParent, hminorParent⟩

/-- A certificate for the fixed hidden-column minor yields Wilkie's final
projection-or-interval fork over a convex visible target. -/
theorem wilkieCase2RecursiveAlternative_finalFork
    {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (RealEuclidean m))
    (hF : ContDiff ℝ 1 (wilkieCase2Flatten F))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ z, wilkieCase2Flatten F z = a →
      Function.Surjective (fderiv ℝ (wilkieCase2Flatten F) z))
    (hbounded : Bornology.IsBounded
      (wilkieFiberOver (wilkieCase2Flatten F) a U))
    (halt : wilkieCase2RecursiveAlternative F a U) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F) a U = U ∨
      ∃ cols : Fin q ↪ Fin (m + q), ∃ η : ℝ,
        0 < η ∧ Set.Icc (0 : ℝ) η ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F) a U := by
  rcases halt with hinterval | ⟨x, hx, hvertical⟩
  · exact Or.inr hinterval
  by_cases hfull : realEuclideanTakeLeft ''
      wilkieFiberOver (wilkieCase2Flatten F) a U = U
  · exact Or.inl hfull
  right
  have himageSubset : realEuclideanTakeLeft ''
      wilkieFiberOver (wilkieCase2Flatten F) a U ⊆ U := by
    rintro u ⟨z, hz, rfl⟩
    exact hz.2
  have hmissedX : ∃ u ∈ U,
      u ∉ realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F) a U := by
    by_contra hnone
    have hUsubset : U ⊆ realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F) a U := by
      intro u hu
      by_contra hnot
      exact hnone ⟨u, hu, hnot⟩
    exact hfull (Set.Subset.antisymm himageSubset hUsubset)
  have hcomponentSubset :
      wilkieFiberComponent (wilkieCase2Flatten F) a U x ⊆
        wilkieFiberOver (wilkieCase2Flatten F) a U :=
    connectedComponentIn_subset _ _
  have hmissedComponent : ∃ u ∈ U,
      u ∉ realEuclideanTakeLeft ''
        wilkieFiberComponent (wilkieCase2Flatten F) a U x := by
    obtain ⟨u, huU, huMiss⟩ := hmissedX
    refine ⟨u, huU, ?_⟩
    intro huImage
    obtain ⟨z, hzComp, hzu⟩ := huImage
    exact huMiss ⟨z, hcomponentSubset hzComp, hzu⟩
  obtain ⟨η, hη, hsmall⟩ :=
    wilkieVerticalMinor_squared_interval_of_missed_projection
      hF a hUconvex.isPreconnected hUopen hregular hbounded
      hx hvertical hmissedComponent
  refine ⟨Fin.natAddEmb m, η, hη, ?_⟩
  intro t ht
  obtain ⟨z, hzComp, hzt⟩ := hsmall ht
  exact ⟨z, hcomponentSubset hzComp, hzt⟩

end AbelFormalization
