import AbelFormalization.MaxwellPseudofunction
import AbelFormalization.MaxwellContDiffInductionGlue

/-!
# Scalar pseudofunction smoothness from the first-order package

This file isolates the differentiability-order induction in Maxwell's
pseudofunction argument.  Its only relation-level analytic input is the
explicit first-order package below: a scalar pseudofunction is represented,
off one closed nowhere-dense family member, by a differentiable total
function, and each of its coordinate partials is represented there by
another scalar pseudofunction in the family.

The package is an assumption.  The theorem proved here iterates it.  At the
successor step the recursively obtained exceptional sets for the partials
are joined to the first-order exceptional set, and the two exact
representations of each derivative relation identify the recursive
representative with the corresponding true partial derivative.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The source-shaped first-order input for scalar pseudofunctions.

The representing functions are total functions on the ambient Euclidean
space.  All representation and differentiability claims are restricted to
the complement of the one exceptional set. -/
def MaxwellScalarFirstOrderPackage (C : EuclideanSetFamily) : Prop :=
  ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U →
      U ∈ C p →
      R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∃ (A0 : Set (RealEuclidean p))
        (f : RealEuclidean p → ℝ)
        (H : Fin p → MaxwellRelation p 1),
        IsClosed A0 ∧
        A0 ∈ C p ∧
        interior A0 = ∅ ∧
        MaxwellRelation.RepresentsOn R (U \ A0)
          (fun x _ ↦ f x) ∧
        (∀ x ∈ U \ A0, DifferentiableAt ℝ f x) ∧
        ∀ i : Fin p,
          H i ∈ C (p + 1) ∧
          IsMaxwellPseudofunctionOn U (H i) ∧
          MaxwellRelation.RepresentsOn (H i) (U \ A0)
            (fun x _ ↦
              fderiv ℝ f x ((Pi.basisFun ℝ (Fin p)) i))

/-- Order-`N` smoothness for scalar pseudofunction relations: outside a
closed empty-interior family member, the relation is exactly represented by
a total scalar function which is `C^N` on the remaining domain. -/
def MaxwellScalarPseudofunctionOrderSmoothness
    (C : EuclideanSetFamily) (N : ℕ) : Prop :=
  ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U →
      U ∈ C p →
      R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∃ (A : Set (RealEuclidean p)) (f : RealEuclidean p → ℝ),
        IsClosed A ∧
        A ∈ C p ∧
        interior A = ∅ ∧
        MaxwellRelation.RepresentsOn R (U \ A)
          (fun x _ ↦ f x) ∧
        ContDiffOn ℝ N f (U \ A)

/-- The source-shaped scalar first-order package iterates to every finite
differentiability order in a Charbonnel closure. -/
theorem maxwellScalarPseudofunctionOrderSmoothness_of_firstOrderPackage
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hfirst : MaxwellScalarFirstOrderPackage (charbonnelClosure S)) :
    ∀ N : ℕ,
      MaxwellScalarPseudofunctionOrderSmoothness
        (charbonnelClosure S) N := by
  intro N
  induction N with
  | zero =>
      intro p hp U R hUopen hUmem hRmem hRpseudo
      obtain ⟨A0, f, H, hA0closed, hA0mem, hA0empty,
        hRrep, hfdiff, _hH⟩ :=
        hfirst hp U R hUopen hUmem hRmem hRpseudo
      refine ⟨A0, f, hA0closed, hA0mem, hA0empty, hRrep, ?_⟩
      apply contDiffOn_zero.mpr
      intro x hx
      exact (hfdiff x hx).continuousAt.continuousWithinAt
  | succ N ih =>
      intro p hp U R hUopen hUmem hRmem hRpseudo
      obtain ⟨A0, f, H, hA0closed, hA0mem, hA0empty,
        hRrep, hfdiff, hH⟩ :=
        hfirst hp U R hUopen hUmem hRmem hRpseudo
      have hrecursive : ∀ i : Fin p,
          ∃ (Ai : Set (RealEuclidean p)) (di : RealEuclidean p → ℝ),
            IsClosed Ai ∧
            Ai ∈ charbonnelClosure S p ∧
            interior Ai = ∅ ∧
            MaxwellRelation.RepresentsOn (H i) (U \ Ai)
              (fun x _ ↦ di x) ∧
            ContDiffOn ℝ N di (U \ Ai) := by
        intro i
        exact ih hp U (H i) hUopen hUmem (hH i).1 (hH i).2.1
      choose A d hAclosed hAmem hAempty hHdrep hdsmooth using hrecursive
      let derivativeSets : Fin 1 → Fin p → Set (RealEuclidean p) :=
        fun _ i ↦ A i
      let bad : Set (RealEuclidean p) :=
        maxwellDerivativeBadSet A0 derivativeSets
      have hbadClosed : IsClosed bad := by
        dsimp only [bad]
        exact isClosed_maxwellDerivativeBadSet hA0closed
          (fun _ i ↦ hAclosed i)
      have hbadEmpty : interior bad = ∅ := by
        dsimp only [bad]
        exact interior_maxwellDerivativeBadSet_eq_empty
          hA0closed hA0empty (fun _ i ↦ hAclosed i)
            (fun _ i ↦ hAempty i)
      have hbadMem : bad ∈ charbonnelClosure S p := by
        dsimp only [bad]
        exact charbonnelClosure_maxwellDerivativeBadSet_mem hp hC hA0mem
          (fun _ i ↦ hAmem i)
      have hcommon_subset_first : U \ bad ⊆ U \ A0 := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        intro hxA0
        apply hx.2
        change x ∈ maxwellDerivativeBadSet A0 derivativeSets
        exact Or.inl hxA0
      have hcommon_subset_derivative : ∀ i : Fin p, U \ bad ⊆ U \ A i := by
        intro i x hx
        refine ⟨hx.1, ?_⟩
        intro hxAi
        apply hx.2
        change x ∈ maxwellDerivativeBadSet A0 derivativeSets
        simp only [maxwellDerivativeBadSet, mem_union, mem_iUnion]
        exact Or.inr ⟨(0 : Fin 1), i, hxAi⟩
      have hd_eq : ∀ x ∈ U \ bad, ∀ i : Fin p,
          d i x =
            fderiv ℝ f x ((Pi.basisFun ℝ (Fin p)) i) := by
        intro x hx i
        have hx0 : x ∈ U \ A0 := hcommon_subset_first hx
        have hxi : x ∈ U \ A i := hcommon_subset_derivative i hx
        have hmem :
            realEuclideanAppend x (fun _ : Fin 1 ↦ d i x) ∈ H i :=
          (hHdrep i x hxi (fun _ : Fin 1 ↦ d i x)).mpr rfl
        have heq :=
          ((hH i).2.2 x hx0 (fun _ : Fin 1 ↦ d i x)).mp hmem
        exact congrFun heq 0
      have hfsmooth : ContDiffOn ℝ (N + 1) f (U \ bad) := by
        apply contDiffOn_succ_of_basis_partials
          (Pi.basisFun ℝ (Fin p)) (hUopen.sdiff hbadClosed)
        · intro x hx
          exact hfdiff x (hcommon_subset_first hx)
        · exact hd_eq
        · intro i
          exact (hdsmooth i).mono (hcommon_subset_derivative i)
      refine ⟨bad, f, hbadClosed, hbadMem, hbadEmpty,
        hRrep.mono hcommon_subset_first, ?_⟩
      simpa [Nat.succ_eq_add_one] using hfsmooth

end AbelFormalization
