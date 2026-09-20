import AbelFormalization.LionLeafMorseSard
import AbelFormalization.LionRolleFiberReduction

/-!
# The equal-dimensional Rolle step in Lion's Theorem 7'

When the dimension of a carpeted leaf equals the positive target dimension,
Lion first restricts to the regular locus of the target map and then removes
its final coordinate.  Lemma 5 bounds the points of the full fiber by the
connected components of the resulting one-dimensional partial fiber.  This
file identifies those sets with the carpeted-leaf fibers used by the
Theorem 7' recursion.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The connected-component quotient never has larger extended cardinality
than its underlying space. -/
theorem enatCard_connectedComponents_le_points
    {X : Type*} [TopologicalSpace X] :
    ENat.card (ConnectedComponents X) ≤ ENat.card X := by
  exact ENat.card_le_card_of_injective
    (Function.injective_surjInv ConnectedComponents.surjective_coe)

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
  {n q p : ℕ}

/-- Remove the final coordinate of a positive-dimensional target tuple. -/
def rolleTargetInit
    (g : RealEuclidean n → RealEuclidean (p + 1)) :
    RealEuclidean n → RealEuclidean p :=
  fun x j ↦ g x j.castSucc

/-- Remove the final coordinate of a target value. -/
def rolleValueInit (t : RealEuclidean (p + 1)) : RealEuclidean p :=
  fun j ↦ t j.castSucc

theorem rolleTargetInit_mem
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (hg : FunctionTupleInFamily G g) :
    FunctionTupleInFamily G (rolleTargetInit g) := by
  intro j
  exact hg j.castSucc

/-- The partial fiber in Lion's Lemma 5 is exactly the fiber of the tuple
obtained by deleting the final target coordinate. -/
theorem lionRollePartialFiber_eq_regularLeaf_initFiber
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (hg : FunctionTupleInFamily G g)
    (t : RealEuclidean (p + 1)) :
    lionRollePartialFiber
        (L.regularLeaf hG hsmooth hderiv g hg).U
        (fun i x ↦ (L.regularLeaf hG hsmooth hderiv g hg).equations x i) g t =
      (L.regularLeaf hG hsmooth hderiv g hg).fiber
        (rolleTargetInit g) (rolleValueInit t) := by
  ext x
  rw [mem_lionRollePartialFiber_iff]
  simp only [fiber, carrier, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxU, hxeq, hxg⟩
    refine ⟨⟨hxU, funext hxeq⟩, ?_⟩
    funext j
    exact hxg j
  · rintro ⟨⟨hxU, hxeq⟩, hxg⟩
    refine ⟨hxU, fun i ↦ congrFun hxeq i, ?_⟩
    intro j
    exact congrFun hxg j

/-- Inside the partial fiber, imposing the complete target value is exactly
the ordinary full fiber of the regular leaf. -/
def lionRolleFullFiberInPartial_equiv_regularLeaf_fiber
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (hg : FunctionTupleInFamily G g)
    (t : RealEuclidean (p + 1)) :
    lionRolleFullFiberInPartial
        (L.regularLeaf hG hsmooth hderiv g hg).U
        (fun i x ↦ (L.regularLeaf hG hsmooth hderiv g hg).equations x i) g t ≃
      (L.regularLeaf hG hsmooth hderiv g hg).fiber g t where
  toFun x := by
    have hxpartial :=
      (mem_lionRollePartialFiber_iff
        (U := (L.regularLeaf hG hsmooth hderiv g hg).U)
        (f := fun i x ↦
          (L.regularLeaf hG hsmooth hderiv g hg).equations x i)
        (g := g) (t := t)).mp x.1.property
    refine ⟨x, ?_⟩
    exact ⟨⟨hxpartial.1, funext hxpartial.2.1⟩, x.property⟩
  invFun x := by
    let y : lionRollePartialFiber
        (L.regularLeaf hG hsmooth hderiv g hg).U
        (fun i x ↦ (L.regularLeaf hG hsmooth hderiv g hg).equations x i) g t :=
      ⟨x, by
        exact (mem_lionRollePartialFiber_iff
          (U := (L.regularLeaf hG hsmooth hderiv g hg).U)
          (f := fun i x ↦
            (L.regularLeaf hG hsmooth hderiv g hg).equations x i)
          (g := g) (t := t)).mpr
            ⟨x.property.1.1,
              (fun j ↦ congrFun x.property.1.2 j),
              fun j ↦ congrFun x.property.2 j.castSucc⟩⟩
    exact ⟨y, x.property.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Equal-dimensional branch of Theorem 7'.  At a regular target, the
component count of the full fiber is bounded by the component count of the
regular leaf's fiber after deleting the final target coordinate. -/
theorem enatCard_connectedComponents_fiber_le_initFiber_components
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (hg : FunctionTupleInFamily G g)
    (hdim : q + (p + 1) = n)
    (t : RealEuclidean (p + 1))
    (ht : L.IsRegularTarget g t) :
    ENat.card (ConnectedComponents (L.fiber g t)) ≤
      ENat.card
        (ConnectedComponents
          ((L.regularLeaf hG hsmooth hderiv g hg).fiber
            (rolleTargetInit g) (rolleValueInit t))) := by
  let K := L.regularLeaf hG hsmooth hderiv g hg
  let f : Fin q → RealEuclideanFunction n :=
    fun i x ↦ K.equations x i
  have hf : ∀ x ∈ K.U, ∀ i, ContDiffAt ℝ 2 (f i) x := by
    intro x _hx i
    exact ((hsmooth n (fun y ↦ K.equations y i) (K.equation_mem i)).of_le
      (by norm_num)).contDiffAt
  have hgTwo : ∀ x ∈ K.U, ∀ j,
      ContDiffAt ℝ 2 (fun y ↦ g y j) x := by
    intro x _hx j
    exact ((hsmooth n (fun y ↦ g y j) (hg j)).of_le
      (by norm_num)).contDiffAt
  have hfSubmersion : ∀ x ∈ K.U,
      (constraintFDeriv f x).range = ⊤ := by
    intro x hx
    have hcoord : ∀ i, DifferentiableAt ℝ (fun y ↦ K.equations y i) x := by
      intro i
      exact (hsmooth n (fun y ↦ K.equations y i)
        (K.equation_mem i)).differentiable (by simp) x
    have hderivEq : constraintFDeriv f x = fderiv ℝ K.equations x := by
      symm
      simpa only [f, constraintFDeriv] using fderiv_pi hcoord
    rw [hderivEq, LinearMap.range_eq_top]
    exact K.fderiv_surjective x hx
  have hgLeafFullRank : ∀ x ∈ K.U,
      (lionLeafRestrictedFDeriv f g x).range = ⊤ := by
    intro x hx
    have hfDiff : DifferentiableAt ℝ K.equations x :=
      (K.equations_contDiff hsmooth).differentiable (by simp) x
    have hgDiff : DifferentiableAt ℝ g x := by
      rw [differentiableAt_pi]
      intro j
      exact (hsmooth n (fun y ↦ g y j) (hg j)).differentiable
        (by simp) x
    have hsub : Function.Surjective (fderiv ℝ K.equations x) :=
      K.fderiv_surjective x hx
    have hcoord : ∀ i,
        DifferentiableAt ℝ (fun y ↦ K.equations y i) x := by
      intro i
      exact (hsmooth n (fun y ↦ K.equations y i)
        (K.equation_mem i)).differentiable (by simp) x
    have hconstraintEq : constraintFDeriv f x =
        fderiv ℝ K.equations x := by
      symm
      simpa only [f, constraintFDeriv] using fderiv_pi hcoord
    have hxreg : x ∈ L.regularLocus g := by
      exact hx
    have happend : Function.Surjective
        (fderiv ℝ (K.definingTupleAppend g) x) := by
      change Function.Surjective
        (fderiv ℝ (L.definingTupleAppend g) x)
      exact hxreg.2
    have hrestricted : Function.Surjective
        ((fderiv ℝ g x).comp
          (fderiv ℝ K.equations x).ker.subtypeL) :=
      (K.fderiv_definingTupleAppend_surjective_iff_restrictKer
        g hfDiff hgDiff hsub).mp happend
    rw [LinearMap.range_eq_top]
    rw [lionLeafRestrictedFDeriv_eq_fderiv_comp f g x hgDiff]
    rw [hconstraintEq]
    exact hrestricted
  have hrolle :
      ENat.card (lionRolleFullFiberInPartial K.U f g t) ≤
        ENat.card (ConnectedComponents (lionRollePartialFiber K.U f g t)) := by
    apply enatCard_lionRolleFullFiber_le_partialFiber_components_of_leafFullRank
      (n := n) (q := q) (p := p)
    · omega
    · exact K.isOpen_U
    · exact hf
    · exact hgTwo
    · exact hfSubmersion
    · exact hgLeafFullRank
  have hfullCard :
      ENat.card (lionRolleFullFiberInPartial K.U f g t) =
        ENat.card (K.fiber g t) := by
    exact ENat.card_congr
      (L.lionRolleFullFiberInPartial_equiv_regularLeaf_fiber
        hG hsmooth hderiv g hg t)
  have hpartial : lionRollePartialFiber K.U f g t =
      K.fiber (rolleTargetInit g) (rolleValueInit t) := by
    exact L.lionRollePartialFiber_eq_regularLeaf_initFiber
      hG hsmooth hderiv g hg t
  have hregularFiber : K.fiber g t = L.fiber g t := by
    exact L.regularLeaf_fiber_eq_of_isRegularTarget
      hG hsmooth hderiv g hg t ht
  calc
    ENat.card (ConnectedComponents (L.fiber g t)) ≤
        ENat.card (L.fiber g t) :=
      enatCard_connectedComponents_le_points
    _ = ENat.card (K.fiber g t) := by rw [hregularFiber]
    _ = ENat.card (lionRolleFullFiberInPartial K.U f g t) := hfullCard.symm
    _ ≤ ENat.card (ConnectedComponents (lionRollePartialFiber K.U f g t)) :=
      hrolle
    _ = ENat.card
        (ConnectedComponents
          (K.fiber (rolleTargetInit g) (rolleValueInit t))) := by
      rw [hpartial]

end LionCarpetedLeaf

end AbelFormalization
