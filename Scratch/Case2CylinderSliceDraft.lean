import AbelFormalization.WilkieCase2ProductFlatEquiv
import AbelFormalization.WilkieCase2VisibleCylinderChoice
import AbelFormalization.WilkieVerticalMinorProjectionFork

/-!
# Literal visible-cylinder slice for Wilkie Case 2

Unlike the ambient-ball slice, this draft keeps the original visible open set
`U` and the bounded restricted fiber `wilkieFiberOver F a U`.  The good value
condition is expressed for `F` in product coordinates, where the maintained
visible insertion and its derivative are available.  `wilkieCase2ProductFlatEquiv`
returns the inserted points to the original flat fiber.

Source-only draft: the root agent owns the compiler pass.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The open set left in the visible source after fixing coordinate `i`. -/
def wilkieCase2VisibleCylinderDomain {m : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (U : Set (RealEuclidean (m + 1))) : Set (RealEuclidean m) :=
  (wilkieCase2_coordinateInsert i b) ⁻¹' U

/-- The literal one-coordinate section of the restricted level fiber. -/
def wilkieCase2FlatCylinderSliceFiber {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (i : Fin (m + 1)) (b : ℝ) :
    Set (RealEuclidean m × RealEuclidean k) :=
  {y | F (wilkieCase2ProductFlatEquiv (m + 1) k
      (wilkieCase2VisibleInsert i b y)) = a ∧
    y.1 ∈ wilkieCase2VisibleCylinderDomain i b U}

/-- The visible projection of the flattened product is its first block. -/
theorem wilkieCase2ProductFlatEquiv_takeLeft {n k : ℕ}
    (z : RealEuclidean n × RealEuclidean k) :
    realEuclideanTakeLeft (wilkieCase2ProductFlatEquiv n k z) = z.1 := by
  simp only [wilkieCase2ProductFlatEquiv,
    realEuclideanAppendContinuousLinearEquiv_apply,
    realEuclideanTakeLeft_append]

/-- The flat-F slice is the maintained product-cylinder
slice for the pulled-back map.  This is the compatibility point with
`WilkieCase2VisibleCylinderChoice`. -/
theorem wilkieCase2FlatCylinderSliceFiber_eq_productChoice {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (i : Fin (m + 1)) (b : ℝ) :
    wilkieCase2FlatCylinderSliceFiber F a U i b =
      wilkieCase2VisibleCylinderSliceFiber
        (F ∘ wilkieCase2ProductFlatEquiv (m + 1) k) a U i b := by
  ext y
  simp only [wilkieCase2FlatCylinderSliceFiber,
    wilkieCase2VisibleCylinderSliceFiber,
    wilkieCase2VisibleCylinderDomain,
    wilkieCase2_coordinateInsert, Set.mem_setOf_eq,
    Set.mem_preimage, Function.comp_apply]

/-- Boundedness of the literal original flat fiber is enough for the
original product cylinder used by the maintained good-value choice theorem. -/
theorem wilkieCase2_productCylinder_bounded_of_flatFiber_bounded {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U)) :
    Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber
        (F ∘ wilkieCase2ProductFlatEquiv (m + 1) k) a U) := by
  let E := wilkieCase2ProductFlatEquiv (m + 1) k
  have hsubset :
      wilkieCase2VisibleCylinderFiber (F ∘ E) a U ⊆
        E.symm '' wilkieFiberOver F a U := by
    intro z hz
    have hzX : E z ∈ wilkieFiberOver F a U := by
      change F (E z) = a ∧ realEuclideanTakeLeft (E z) ∈ U
      refine ⟨hz.1, ?_⟩
      rw [wilkieCase2ProductFlatEquiv_takeLeft]
      exact hz.2
    exact ⟨E z, hzX, E.symm_apply_apply z⟩
  exact (E.symm.lipschitzWith.isBounded_image hbounded).subset hsubset

/-- An open visible cylinder stays open after fixing one visible coordinate.
The hidden coordinates play no part in this openness claim. -/
theorem wilkieCase2VisibleCylinderDomain_isOpen {m k : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (U : Set (RealEuclidean (m + 1))) (hU : IsOpen U) :
    IsOpen (wilkieCase2VisibleCylinderDomain i b U) := by
  have hInsert : Continuous (wilkieCase2VisibleInsert (q := k) i b) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (wilkieCase2VisibleInsert_hasFDerivAt i b y).continuousAt
  have hPair : Continuous
      (fun u : RealEuclidean m => (u, (0 : RealEuclidean k))) :=
    continuous_id.prodMk continuous_const
  have hVisible : Continuous
      (wilkieCase2_coordinateInsert i b) := by
    change Continuous (fun u : RealEuclidean m =>
      (wilkieCase2VisibleInsert (q := k) i b (u, 0)).1)
    exact continuous_fst.comp (hInsert.comp hPair)
  exact hU.preimage hVisible

/-- The inserted image of the literal cylinder section lies in the *same*
restricted flat fiber.  This inclusion is the needed certificate-lift
interface; it does not enlarge `U` to an ambient source ball. -/
theorem wilkieCase2FlatCylinderSliceFiber_inserted_subset {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (i : Fin (m + 1)) (b : ℝ) :
    (wilkieCase2ProductFlatEquiv (m + 1) k ∘
      wilkieCase2VisibleInsert i b) ''
        wilkieCase2FlatCylinderSliceFiber F a U i b ⊆
      wilkieFiberOver F a U := by
  rintro z ⟨y, hy, rfl⟩
  change F (wilkieCase2ProductFlatEquiv (m + 1) k
      (wilkieCase2VisibleInsert i b y)) = a ∧
    realEuclideanTakeLeft (wilkieCase2ProductFlatEquiv (m + 1) k
      (wilkieCase2VisibleInsert i b y)) ∈ U
  refine ⟨hy.1, ?_⟩
  rw [wilkieCase2ProductFlatEquiv_takeLeft]
  simpa only [wilkieCase2VisibleCylinderDomain,
    wilkieCase2_coordinateInsert, wilkieCase2VisibleInsert,
    Set.mem_preimage] using hy.2

/-- An attained fixed-coordinate point of the original restricted fiber
gives a nonempty section.  Coordinate deletion then transports the original
fiber's boundedness to the section. -/
theorem wilkieCase2FlatCylinderSliceFiber_nonempty_bounded {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (i : Fin (m + 1)) (b : ℝ)
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    (x : RealEuclidean (m + 1) × RealEuclidean k)
    (hx : wilkieCase2ProductFlatEquiv (m + 1) k x ∈
      wilkieFiberOver F a U)
    (hpivot : x.1 i = b) :
    (wilkieCase2FlatCylinderSliceFiber F a U i b).Nonempty ∧
    Bornology.IsBounded (wilkieCase2FlatCylinderSliceFiber F a U i b) := by
  have hxF : F (wilkieCase2ProductFlatEquiv (m + 1) k x) = a := hx.1
  have hxU : x.1 ∈ U := by
    have h : realEuclideanTakeLeft
        (wilkieCase2ProductFlatEquiv (m + 1) k x) ∈ U := hx.2
    simpa only [wilkieCase2ProductFlatEquiv_takeLeft] using h
  have hnonempty :
      (wilkieCase2FlatCylinderSliceFiber F a U i b).Nonempty := by
    obtain ⟨y, hy⟩ := wilkieCase2VisibleInsert_covers_pivot i b x hpivot
    refine ⟨y, ?_⟩
    have hyVisible : wilkieCase2_coordinateInsert i b y.1 = x.1 :=
      congrArg Prod.fst hy
    change F (wilkieCase2ProductFlatEquiv (m + 1) k
        (wilkieCase2VisibleInsert i b y)) = a ∧
      wilkieCase2_coordinateInsert i b y.1 ∈ U
    rw [hy, hyVisible]
    exact ⟨hxF, hxU⟩
  let E := wilkieCase2ProductFlatEquiv (m + 1) k
  let D : RealEuclidean ((m + 1) + k) →L[ℝ]
      (RealEuclidean m × RealEuclidean k) :=
    (wilkieCase2VisibleDrop i).comp
      (E.symm : RealEuclidean ((m + 1) + k) →L[ℝ]
        (RealEuclidean (m + 1) × RealEuclidean k))
  have hsubset :
      wilkieCase2FlatCylinderSliceFiber F a U i b ⊆
        D '' wilkieFiberOver F a U := by
    intro y hy
    refine ⟨E (wilkieCase2VisibleInsert i b y), ?_, ?_⟩
    · exact wilkieCase2FlatCylinderSliceFiber_inserted_subset
        F a U i b ⟨y, hy, rfl⟩
    · change wilkieCase2VisibleDrop i
        (E.symm (E (wilkieCase2VisibleInsert i b y))) = y
      rw [E.symm_apply_apply]
      exact wilkieCase2VisibleDrop_insert i b y
  exact ⟨hnonempty,
    (D.lipschitzWith.isBounded_image hbounded).subset hsubset⟩

/-- Outside the exceptional parameter set, every point of the literal
cylinder section has a surjective derivative.  The open-set restriction
changes only which points are considered, so the maintained augmented
derivative and insertion-range bridge apply pointwise. -/
theorem wilkieCase2FlatCylinderSliceFiber_regular {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (i : Fin (m + 1)) (b : ℝ)
    (hFdiff : ∀ z : RealEuclidean (m + 1) × RealEuclidean k,
      DifferentiableAt ℝ (F ∘ wilkieCase2ProductFlatEquiv (m + 1) k) z)
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet
      (F ∘ wilkieCase2ProductFlatEquiv (m + 1) k)
      (fun z : RealEuclidean (m + 1) × RealEuclidean k => z.1 i) a) :
    ∀ y ∈ wilkieCase2FlatCylinderSliceFiber F a U i b,
      Function.Surjective
        (fderiv ℝ
          ((F ∘ wilkieCase2ProductFlatEquiv (m + 1) k) ∘
            wilkieCase2VisibleInsert i b) y) := by
  intro y hy
  let G := F ∘ wilkieCase2ProductFlatEquiv (m + 1) k
  have haug : Function.Surjective
      (fun v : RealEuclidean (m + 1) × RealEuclidean k =>
        (fderiv ℝ G (wilkieCase2VisibleInsert i b y) v,
          fderiv ℝ (fun z : RealEuclidean (m + 1) ×
            RealEuclidean k => z.1 i)
              (wilkieCase2VisibleInsert i b y) v)) := by
    exact wilkie28_augmented_surjective_of_not_exceptional
      G (fun z => z.1 i) a b hb hy.1
      (wilkieCase2VisibleInsert_pivot i b y)
  have hkernel (v : RealEuclidean (m + 1) × RealEuclidean k)
      (hv : fderiv ℝ (fun z : RealEuclidean (m + 1) ×
          RealEuclidean k => z.1 i)
            (wilkieCase2VisibleInsert i b y) v = 0) :
      ∃ w : RealEuclidean m × RealEuclidean k,
        wilkieCase2VisibleDirection i w = v := by
    rw [wilkieCase2VisiblePivot_fderiv] at hv
    exact wilkieCase2VisibleDirection_covers_pivot_kernel i v hv
  have hrestricted : Function.Surjective
      (fun w : RealEuclidean m × RealEuclidean k =>
        fderiv ℝ G (wilkieCase2VisibleInsert i b y)
          (wilkieCase2VisibleDirection i w)) :=
    surjective_restricted_map_of_surjective_augmented
      (fderiv ℝ G (wilkieCase2VisibleInsert i b y))
      (fderiv ℝ (fun z : RealEuclidean (m + 1) ×
        RealEuclidean k => z.1 i)
          (wilkieCase2VisibleInsert i b y))
      (wilkieCase2VisibleDirection i) (0 : ℝ) haug hkernel
  have hchain : fderiv ℝ (G ∘ wilkieCase2VisibleInsert i b) y =
      (fderiv ℝ G (wilkieCase2VisibleInsert i b y)).comp
        (wilkieCase2VisibleDirection i) :=
    ((hFdiff (wilkieCase2VisibleInsert i b y)).hasFDerivAt.comp y
      (wilkieCase2VisibleInsert_hasFDerivAt i b y)).fderiv
  rw [hchain]
  exact hrestricted

/-- All four concrete slice facts from Wilkie's visible-cylinder fiber,
without an ambient full-source ball. -/
theorem wilkieCase2VisibleCylinderSlice_data {m k : ℕ}
    (F : RealEuclidean ((m + 1) + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean (m + 1)))
    (i : Fin (m + 1)) (b : ℝ)
    (hU : IsOpen U)
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    (hFdiff : ∀ z : RealEuclidean (m + 1) × RealEuclidean k,
      DifferentiableAt ℝ (F ∘ wilkieCase2ProductFlatEquiv (m + 1) k) z)
    (hb : b ∉ Wilkie28MathlibOnly.exceptionalParameterSet
      (F ∘ wilkieCase2ProductFlatEquiv (m + 1) k)
      (fun z : RealEuclidean (m + 1) × RealEuclidean k => z.1 i) a)
    (x : RealEuclidean (m + 1) × RealEuclidean k)
    (hx : wilkieCase2ProductFlatEquiv (m + 1) k x ∈
      wilkieFiberOver F a U)
    (hpivot : x.1 i = b) :
    IsOpen (wilkieCase2VisibleCylinderDomain i b U) ∧
    (wilkieCase2FlatCylinderSliceFiber F a U i b).Nonempty ∧
    Bornology.IsBounded (wilkieCase2FlatCylinderSliceFiber F a U i b) ∧
    (∀ y ∈ wilkieCase2FlatCylinderSliceFiber F a U i b,
      Function.Surjective
        (fderiv ℝ
          ((F ∘ wilkieCase2ProductFlatEquiv (m + 1) k) ∘
            wilkieCase2VisibleInsert i b) y)) ∧
    (wilkieCase2ProductFlatEquiv (m + 1) k ∘
      wilkieCase2VisibleInsert i b) ''
        wilkieCase2FlatCylinderSliceFiber F a U i b ⊆
      wilkieFiberOver F a U := by
  obtain ⟨hnonempty, hsliceBounded⟩ :=
    wilkieCase2FlatCylinderSliceFiber_nonempty_bounded
      F a U i b hbounded x hx hpivot
  exact ⟨wilkieCase2VisibleCylinderDomain_isOpen (k := k) i b U hU,
    hnonempty, hsliceBounded,
    wilkieCase2FlatCylinderSliceFiber_regular F a U i b hFdiff hb,
    wilkieCase2FlatCylinderSliceFiber_inserted_subset F a U i b⟩

end AbelFormalization
