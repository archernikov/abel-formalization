import AbelFormalization.RestrictedAllUnboundedPairBranch
import AbelFormalization.RestrictedPairMergeSequenceTransport
import AbelFormalization.RestrictedPairMergeExpressionPullback
import AbelFormalization.RestrictedStrictDifferentiability
import AbelFormalization.RestrictedSourceBasis
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Pulling the all-unbounded pair branch back to one fewer representative

This scratch module specializes the pair-branch geometry to an old source
with `q + 2` representatives.  A distinct old partner of the pivot is written
uniquely as `i.succAbove j'`; the explicit logarithmic pullback then gives an
injective sequence in a source with `q + 1` representatives and one additional
bounded coordinate.
-/

noncomputable section

open Set Filter Function Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

private def emptyRestrictedExpressionTower
    {m p a : ℕ} (D : RestrictedBox p)
    (S : Set (RestrictedSource m p a → ℝ)) :
    RestrictedExpressionTower D S (ell := 0) where
  exponent := fun i ↦ Fin.elim0 i
  exponent_mem_level := fun i ↦ Fin.elim0 i

/-- Base expressions are differentiable at points of the restricted open
base domain.  The positive representative count in this specialization gives
a distinguished coordinate of the finite source basis. -/
private theorem IsAbel.differentiableAt_constraintMap_q_add_two_of_mem_base
    {A : ℝ → ℝ} (hA : IsAbel A) {ι : Type*} [Finite ι]
    {q p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin (q + 2))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := q + 2) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((q + 2) + p) + a) →
      RestrictedSource (q + 2) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    {x : RestrictedSource (q + 2) p a}
    (hx : x ∈ restrictedBaseOpenDomain D R) :
    DifferentiableAt ℝ (constraintMap F) x := by
  let T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := 0) :=
    emptyRestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
  have hxInterior : x ∈ interior
      (restrictedAbelJetDomain (a := a) D representative offset) :=
    restrictedBaseOpenDomain_subset_interior_AbelJetDomain
      D R representative offset hDomain hx
  have hcomponent : ∀ r, HasStrictFDerivAt (F r)
      (fderiv ℝ (F r) x) x := by
    intro r
    apply hA.hasStrictFDerivAt_of_mem_restrictedAbelTower_level_of_mem_interior
      representative offset T 0 (restrictedSourceBasis (q + 2) p a)
        (⟨0, by omega⟩ : Fin (((q + 2) + p) + a))
    · simpa only [T.level_zero] using hF r
    · exact hxInterior
  exact (hasStrictFDerivAt_constraintMap F x hcomponent).differentiableAt

/-- The concrete lower-representative sequence attached to a selected pair
in the `q + 2` all-unbounded branch.

The finite shift removes the initial segment before both selected old
coordinates are positive.  Thus the returned sequence is injective, converges
in its enlarged bounded coordinates to `Fin.snoc w₀ 0`, retains divergence of
all `q + 1` representative coordinates, and eventually consists of regular
zeros of the reindexed pair-merged equation family on the enlarged restricted
base domain. -/
theorem IsAbel.exists_restrictedPairMergePullbackSequence_q_add_two
    {A : ℝ → ℝ} (hA : IsAbel A) {ι : Type*} [Finite ι]
    {q p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin (q + 2))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := q + 2) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((q + 2) + p) + a) →
      RestrictedSource (q + 2) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource (q + 2) p a)
    (w₀ : RestrictedBoxSpace p)
    (i j : Fin (q + 2)) (K k : ℕ)
    (hxinj : Function.Injective x)
    (hxmem : ∀ n, x n ∈
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F))
    (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀))
    (hxrep : ∀ r, Tendsto (fun n ↦ (x n).1.1 r) atTop atTop)
    (hij : i ≠ j)
    (hxi : Tendsto (fun n ↦
      L^[K + k] ((x n).1.1 i) - L^[K] ((x n).1.1 j))
      atTop (nhds 0)) :
    ∃ (j' : Fin (q + 1)) (n₀ : ℕ)
      (y : ℕ → RestrictedSource (q + 1) (p + 1) a),
      i.succAbove j' = j ∧
      (∀ n, y n = restrictedPairMergePullback K k i j' (x (n₀ + n))) ∧
      Function.Injective y ∧
      Fin.snoc w₀ 0 ∈ (restrictedPairMergeBox D).closedBox ∧
      Tendsto (fun n ↦ (y n).1.2) atTop (nhds (Fin.snoc w₀ 0)) ∧
      (∀ r, Tendsto (fun n ↦ (y n).1.1 r) atTop atTop) ∧
      (∀ᶠ n in atTop,
        y n ∈ restrictedBaseOpenDomain (restrictedPairMergeBox D) R) ∧
      ∀ᶠ n in atTop,
        y n ∈ regularZeroSet
          (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
          (constraintMap (restrictedPairMergedEquationFamily K k i j' F)) := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  have hi := hxrep i
  have hj : Tendsto (fun n ↦ (x n).1.1 (i.succAbove j')) atTop atTop := by
    simpa only [hj'] using hxrep j
  obtain ⟨n₀, hyinj, _⟩ :=
    exists_shift_restrictedPairMergePullback_injective K k i j' x hxinj hi hj
  let shift : ℕ → ℕ := fun n ↦ n₀ + n
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat n₀
  let y : ℕ → RestrictedSource (q + 1) (p + 1) a :=
    fun n ↦ restrictedPairMergePullback K k i j' (x (shift n))
  have hzrep : ∀ r, Tendsto (fun n ↦ (x (shift n)).1.1 r) atTop atTop := by
    intro r
    exact (hxrep r).comp hshift
  have hzlim : Tendsto (fun n ↦ (x (shift n)).1.2)
      atTop (nhds w₀) :=
    hxlim.comp hshift
  have hxiPartner : Tendsto (fun n ↦
      L^[K + k] ((x n).1.1 i) -
        L^[K] ((x n).1.1 (i.succAbove j')))
      atTop (nhds 0) := by
    simpa only [hj'] using hxi
  have hzxi : Tendsto (fun n ↦
      L^[K + k] ((x (shift n)).1.1 i) -
        L^[K] ((x (shift n)).1.1 (i.succAbove j')))
      atTop (nhds 0) := by
    change Tendsto ((fun n ↦
      L^[K + k] ((x n).1.1 i) -
        L^[K] ((x n).1.1 (i.succAbove j'))) ∘ shift)
      atTop (nhds 0)
    exact hxiPartner.comp hshift
  have hyxi : Tendsto (fun n ↦
      (restrictedPairMergePullback K k i j' (x (shift n))).1.2
        (Fin.last p)) atTop (nhds 0) := by
    simpa only [restrictedPairMergePullback_box_last] using hzxi
  have hybox : Tendsto (fun n ↦ (y n).1.2)
      atTop (nhds (Fin.snoc w₀ 0)) := by
    exact restrictedPairMergePullback_box_tendsto K k i j'
      (fun n ↦ x (shift n)) w₀ hzlim hzxi
  have hyrep : ∀ r, Tendsto (fun n ↦ (y n).1.1 r) atTop atTop := by
    exact restrictedPairMergePullback_representatives_tendsto_atTop
      K k i j' (fun n ↦ x (shift n)) hzrep
  have hzbox : ∀ n, (x (shift n)).1.2 ∈ D.openBox := by
    intro n
    exact (hxmem (shift n)).1.2
  have hyDomain : ∀ᶠ n in atTop,
      y n ∈ restrictedBaseOpenDomain (restrictedPairMergeBox D) R := by
    exact eventually_restrictedPairMergePullback_mem_baseOpenDomain
      K k i j' (fun n ↦ x (shift n)) D (-1) 1 (by norm_num)
        (by norm_num) (by norm_num) R hzrep hzbox hyxi
  have hzmem : ∀ n, x (shift n) ∈
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) := by
    intro n
    exact hxmem (shift n)
  have hzdiff : ∀ n,
      DifferentiableAt ℝ (constraintMap F) (x (shift n)) := by
    intro n
    exact hA.differentiableAt_constraintMap_q_add_two_of_mem_base
      D representative offset R hDomain F hF (hzmem n).1
  have hyregular : ∀ᶠ n in atTop,
      y n ∈ regularZeroSet
        (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
        (constraintMap (restrictedPairMergedEquationFamily K k i j' F)) := by
    exact eventually_restrictedPairMergePullback_mem_regularZeroSet_baseOpen
      K k i j' D (-1) 1 (by norm_num) R
        (restrictedBaseOpenDomain D R) F (fun n ↦ x (shift n))
        hyDomain (hzrep i) (hzrep (i.succAbove j')) hzmem hzdiff
  refine ⟨j', n₀, y, hj', ?_, ?_, ?_, hybox, hyrep, hyDomain, hyregular⟩
  · intro n
    rfl
  · simpa only [y, shift] using hyinj
  · exact finSnoc_zero_mem_closedBox_snoc D w₀ (-1) 1 (by norm_num)
      hw₀ (by norm_num) (by norm_num)

end AbelFormalization
