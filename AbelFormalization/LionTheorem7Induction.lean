import AbelFormalization.LionRolleFiberReduction
import AbelFormalization.LionCarpetedLeaf
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The induction and counting interface for Lion's Theorem 7'

Lion's proof of Theorem 7' is an induction on `leaf dimension + target
dimension`.  There are exactly four cases: generically empty fibers when the
target dimension is larger, the zero-dimensional base case, Gabrielov
sections when the leaf dimension is larger, and Rolle reduction when the two
positive dimensions agree.

This file records that induction scheme and the cardinal estimates which let
the last two cases compose.  It deliberately does not postulate a theorem
asserting the existence of Gabrielov sections: that differential-topological
construction still requires a formal notion of carpeted leaf.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## The dimension induction in Theorem 7' -/

/-- The strong-induction scheme used in Lion's proof of Theorem 7'.

`P d p` is the desired generic fiber statement for a leaf of dimension `d`
and a target of dimension `p`.  The four hypotheses are, in source order:

* Sard's empty-fiber case `d < p`;
* the zero-dimensional leaf case;
* Gabrielov's finite section family, reducing `d > p` to `(p,p)`;
* Rolle's lemma, reducing `(p,p)` to `(p,p-1)` for positive `p`.

Both recursive calls strictly decrease `d + p`. -/
theorem lionTheorem7_dimensionTarget_induction
    (P : ℕ → ℕ → Prop)
    (hempty : ∀ d p, d < p → P d p)
    (hzero : P 0 0)
    (hsection : ∀ d p, p < d → P p p → P d p)
    (hrolle : ∀ p, 0 < p → P p (p - 1) → P p p) :
    ∀ d p, P d p := by
  intro d p
  induction hsum : d + p using Nat.strong_induction_on generalizing d p with
  | h n ih =>
      by_cases hdp : d < p
      · exact hempty d p hdp
      by_cases hpd : p < d
      · apply hsection d p hpd
        apply ih (p + p)
        · omega
        · rfl
      have hdeq : d = p := Nat.le_antisymm (Nat.le_of_not_gt hpd)
        (Nat.le_of_not_gt hdp)
      subst d
      by_cases hpzero : p = 0
      · subst p
        exact hzero
      apply hrolle p (Nat.pos_of_ne_zero hpzero)
      apply ih (p + (p - 1))
      · omega
      · rfl

/-- An empty generic fiber contributes zero connected components in the
Sard branch of Theorem 7'. -/
theorem enatCard_connectedComponents_eq_zero_of_isEmpty
    {X : Type*} [TopologicalSpace X] [IsEmpty X] :
    ENat.card (ConnectedComponents X) = 0 := by
  rw [ENat.card_eq_zero_iff_empty]
  refine ⟨fun component ↦ ?_⟩
  obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe component
  exact isEmptyElim x

/-- Set-theoretic form of the empty generic-fiber count. -/
@[simp]
theorem enatCard_connectedComponents_empty
    {X : Type*} [TopologicalSpace X] :
    ENat.card (ConnectedComponents (∅ : Set X)) = 0 :=
  enatCard_connectedComponents_eq_zero_of_isEmpty

/-! ## A finite family of sections meeting every component -/

/-- Map a point on one section to the connected component of the ambient
fiber which contains it. -/
def lionSectionComponentMap
    {X I : Type*} [TopologicalSpace X]
    (Point : I → Type*) (embed : ∀ i, Point i → X) :
    (Σ i, Point i) → ConnectedComponents X
  | ⟨i, z⟩ => ConnectedComponents.mk (embed i z)

/-- If the finite section family meets every ambient connected component,
the component map from all section points is surjective. -/
theorem lionSectionComponentMap_surjective
    {X I : Type*} [TopologicalSpace X]
    (Point : I → Type*) (embed : ∀ i, Point i → X)
    (hmeet : ∀ x : X, ∃ i, ∃ z : Point i,
      embed i z ∈ connectedComponent x) :
    Function.Surjective (lionSectionComponentMap Point embed) := by
  intro component
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe component
  obtain ⟨i, z, hz⟩ := hmeet x
  refine ⟨⟨i, z⟩, ?_⟩
  exact ConnectedComponents.coe_eq_coe'.2 hz

/-- The exact finite-sum estimate used after Gabrielov's section lemma.

Each `Point i` is the fiber of one section leaf.  A bound `bound i` for its
cardinality contributes additively, because the dependent sum of all section
fibers maps onto the connected components of the original fiber. -/
theorem enatCard_connectedComponents_le_sum_of_finite_sections
    {X I : Type*} [TopologicalSpace X] [Fintype I]
    (Point : I → Type*) (embed : ∀ i, Point i → X)
    (hmeet : ∀ x : X, ∃ i, ∃ z : Point i,
      embed i z ∈ connectedComponent x)
    (bound : I → ℕ)
    (hbound : ∀ i, ENat.card (Point i) ≤ bound i) :
    ENat.card (ConnectedComponents X) ≤ ∑ i, bound i := by
  have hfinite : ∀ i, Finite (Point i) := by
    intro i
    exact ENat.card_lt_top.mp ((hbound i).trans_lt (by simp))
  let _ (i : I) : Finite (Point i) := hfinite i
  calc
    ENat.card (ConnectedComponents X) ≤ ENat.card (Σ i, Point i) :=
      ENat.card_le_card_of_injective
        (Function.injective_surjInv
          (lionSectionComponentMap_surjective Point embed hmeet))
    _ = Nat.card (Σ i, Point i) := ENat.card_eq_coe_natCard _
    _ = ∑ i, Nat.card (Point i) := by
      norm_cast
      exact Nat.card_sigma
    _ ≤ ∑ i, bound i := by
      norm_cast
      apply Finset.sum_le_sum
      intro i _
      have hi := hbound i
      rw [ENat.card_eq_coe_natCard] at hi
      exact_mod_cast hi

/-- Section counting composed with an arbitrary component reduction on every
section.  In Theorem 7', `hreduce` is Lion's Rolle lemma and `hinduction` is
the induction hypothesis for the target with its final coordinate removed. -/
theorem enatCard_connectedComponents_le_sum_of_section_reductions
    {X I : Type*} [TopologicalSpace X] [Fintype I]
    (Point : I → Type*) (embed : ∀ i, Point i → X)
    (hmeet : ∀ x : X, ∃ i, ∃ z : Point i,
      embed i z ∈ connectedComponent x)
    (Reduced : I → Type*) (bound : I → ℕ)
    (hreduce : ∀ i, ENat.card (Point i) ≤ ENat.card (Reduced i))
    (hinduction : ∀ i, ENat.card (Reduced i) ≤ bound i) :
    ENat.card (ConnectedComponents X) ≤ ∑ i, bound i := by
  apply enatCard_connectedComponents_le_sum_of_finite_sections
    Point embed hmeet bound
  intro i
  exact (hreduce i).trans (hinduction i)

/-! ## Rolle reduction for a finite Gabrielov section family -/

/-- A finite family of equal-dimensional section leaves, each followed by
Lion's Rolle reduction, bounds the components of the original leaf fiber.

The meeting hypothesis is precisely the conclusion of Gabrielov's Lemma 4.
The hypotheses ending in `hfullRank` are precisely those consumed by
`enatCard_lionRolleFullFiber_le_partialFiber_components`.  Thus no global
Theorem 7' conclusion is assumed in this composition lemma. -/
theorem enatCard_connectedComponents_le_sum_of_lionRolleSections
    {I : Type*} [Fintype I] {q p : ℕ}
    {M : Set (RealEuclidean ((q + p) + 1))}
    (U : I → Set (RealEuclidean ((q + p) + 1)))
    (hU : ∀ i, IsOpen (U i))
    (f : I → Fin q → RealEuclideanFunction ((q + p) + 1))
    (g : RealEuclidean ((q + p) + 1) → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1))
    (hf : ∀ i x, x ∈ U i → ∀ j, ContDiffAt ℝ 2 (f i j) x)
    (hg : ∀ i x, x ∈ U i → ∀ j,
      ContDiffAt ℝ 2 (fun y ↦ g y j) x)
    (hfullRank : ∀ i
      (x : lionRollePartialFiber (U i) (f i) g t),
      (constraintFDeriv
        (functionTupleSnoc (lionRolleCombinedConstraints (f i) g t)
          (lionRolleLastEquation g t)) x).range = ⊤)
    (hsub : ∀ i
      (z : lionRolleFullFiberInPartial (U i) (f i) g t),
      ((z : lionRollePartialFiber (U i) (f i) g t) :
        RealEuclidean ((q + p) + 1)) ∈ M)
    (hmeet : ∀ x : M, ∃ i,
      ∃ z : lionRolleFullFiberInPartial (U i) (f i) g t,
        (⟨((z : lionRollePartialFiber (U i) (f i) g t) :
              RealEuclidean ((q + p) + 1)), hsub i z⟩ : M) ∈
          connectedComponent x)
    (bound : I → ℕ)
    (hinduction : ∀ i,
      ENat.card
          (ConnectedComponents
            (lionRollePartialFiber (U i) (f i) g t)) ≤ bound i) :
    ENat.card (ConnectedComponents M) ≤ ∑ i, bound i := by
  let Point : I → Type := fun i ↦
    lionRolleFullFiberInPartial (U i) (f i) g t
  let embed : ∀ i, Point i → M := fun i z ↦
    ⟨((z : lionRollePartialFiber (U i) (f i) g t) :
      RealEuclidean ((q + p) + 1)), hsub i z⟩
  apply enatCard_connectedComponents_le_sum_of_section_reductions
    (X := M) (I := I) Point embed
    (Reduced := fun i ↦
      ConnectedComponents (lionRollePartialFiber (U i) (f i) g t))
    (bound := bound)
  · simpa only [Point, embed] using hmeet
  · intro i
    exact enatCard_lionRolleFullFiber_le_partialFiber_components
      rfl (hU i) (f i) g t (hf i) (hg i) (hfullRank i)
  · exact hinduction

/-! ## The zero-dimensional endpoint -/

/-- `0`-regularity gives the natural-number bound needed at a terminal
zero-dimensional leaf whenever its points inject into a smooth regular fiber
of a square family map. -/
theorem IsZeroRegularFunctionFamily.exists_enatCard_le_of_injective_regularFiber
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hzero : IsZeroRegularFunctionFamily G)
    {Z : Type*} {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n)
    (hF : FunctionTupleInFamily G F) (u : RealEuclidean n)
    (encode : Z → smoothRegularFiber F u)
    (hencode : Function.Injective encode) :
    ∃ N : ℕ, ENat.card Z ≤ N := by
  have hfiniteFiber : (smoothRegularFiber F u).Finite :=
    hzero n F hF u
  let _ : Finite (smoothRegularFiber F u) :=
    Set.finite_coe_iff.mpr hfiniteFiber
  refine ⟨Nat.card (smoothRegularFiber F u), ?_⟩
  exact (ENat.card_le_card_of_injective hencode).trans_eq
    (ENat.card_eq_coe_natCard _)

/-- Finite terminal zero leaves, each encoded by a regular zero-dimensional
fiber, have a finite total cardinal bound.  This is the base-case sum used
after the recursive Gabrielov/Rolle construction. -/
theorem IsZeroRegularFunctionFamily.exists_sum_bound_of_regularFiberEncodings
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hzero : IsZeroRegularFunctionFamily G)
    {I : Type*} [Fintype I]
    (Point : I → Type*) (dimension : I → ℕ)
    (F : ∀ i, RealEuclidean (dimension i) → RealEuclidean (dimension i))
    (hF : ∀ i, FunctionTupleInFamily G (F i))
    (u : ∀ i, RealEuclidean (dimension i))
    (encode : ∀ i, Point i → smoothRegularFiber (F i) (u i))
    (hencode : ∀ i, Function.Injective (encode i)) :
    ∃ bound : I → ℕ,
      (∀ i, ENat.card (Point i) ≤ bound i) ∧
        ENat.card (Σ i, Point i) ≤ ∑ i, bound i := by
  choose bound hbound using fun i ↦
    hzero.exists_enatCard_le_of_injective_regularFiber
      (F i) (hF i) (u i) (encode i) (hencode i)
  refine ⟨bound, hbound, ?_⟩
  have hfinite : ∀ i, Finite (Point i) := by
    intro i
    exact ENat.card_lt_top.mp ((hbound i).trans_lt (by simp))
  let _ (i : I) : Finite (Point i) := hfinite i
  calc
    ENat.card (Σ i, Point i) = Nat.card (Σ i, Point i) :=
      ENat.card_eq_coe_natCard _
    _ = ∑ i, Nat.card (Point i) := by
      norm_cast
      exact Nat.card_sigma
    _ ≤ ∑ i, bound i := by
      norm_cast
      apply Finset.sum_le_sum
      intro i _
      have hi := hbound i
      rw [ENat.card_eq_coe_natCard] at hi
      exact_mod_cast hi

/-- The terminal case of Theorem 7' for an actual finite family of Lion
zero-dimensional leaves.  Each leaf embeds canonically into the smooth
regular zero fiber of its defining square tuple, so `0`-regularity bounds the
whole dependent sum of terminal points. -/
theorem IsZeroRegularFunctionFamily.exists_sum_bound_of_zeroDimensionalLeaves
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hzero : IsZeroRegularFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {I : Type*} [Fintype I]
    (dimension : I → ℕ)
    (L : ∀ i, LionCarpetedLeaf.ZeroDimensional G (dimension i)) :
    ∃ bound : I → ℕ,
      (∀ i, ENat.card (L i).carrier ≤ bound i) ∧
        ENat.card (Σ i, (L i).carrier) ≤ ∑ i, bound i := by
  exact hzero.exists_sum_bound_of_regularFiberEncodings
    (fun i ↦ (L i).carrier) dimension
    (fun i ↦ (L i).equations)
    (fun i ↦ (L i).equations_tuple_mem)
    (fun i ↦ (0 : RealEuclidean (dimension i)))
    (fun i ↦ (L i).regularFiberEmbedding hsmooth)
    (fun i ↦ (L i).regularFiberEmbedding_injective hsmooth)

end AbelFormalization
