import AbelFormalization.RestrictedBoundedReclassificationSlice
import AbelFormalization.RestrictedRepresentativeSubsequence

/-!
# Removing the bounded-representative branch

The outer induction hypothesis makes every bounded slice finite.  Therefore
an injective classified sequence of regular zeros cannot have a bounded
representative coordinate, and all representatives tend to positive infinity.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Under the lower representative-count case, every coordinate of an
injective classified regular-zero sequence tends to positive infinity. -/
theorem IsAbel.restrictedRegularZeroSequence_representatives_tendsto_atTop
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (houter : RestrictedBaseRegularZeroFiniteForRepresentativeCount A m)
    {ι : Type} [Finite ι] {p a : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (hF : ∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource (m + 1) p a)
    (hxinj : Function.Injective x)
    (hxmem : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hclass : ∀ i,
      BddAbove (Set.range (fun n ↦ (x n).1.1 i)) ∨
        Tendsto (fun n ↦ (x n).1.1 i) atTop atTop) :
    ∀ i, Tendsto (fun n ↦ (x n).1.1 i) atTop atTop := by
  intro i
  rcases hclass i with hbounded | hdivergent
  · exfalso
    obtain ⟨C, hC⟩ := hbounded
    let M : ℝ := max (R + 1) (C + 1)
    have hRM : R < M := by
      dsimp only [M]
      exact (lt_add_one R).trans_le (le_max_left _ _)
    have hCM : C < M := by
      dsimp only [M]
      exact (lt_add_one C).trans_le (le_max_right _ _)
    have hfinite := hA.finite_regularZeroSet_base_slice_of_lowerRepresentativeCount
      houter D representative offset R M hRM i hDomain F hF
    have hrangeSubset : Set.range x ⊆
        regularZeroSet
          (restrictedBaseOpenDomain D R ∩ {y | y.1.1 i < M})
          (constraintMap F) := by
      rintro y ⟨n, rfl⟩
      have hxiC : (x n).1.1 i ≤ C := hC ⟨n, rfl⟩
      exact ⟨⟨(hxmem n).1, hxiC.trans_lt hCM⟩,
        (hxmem n).2.1, (hxmem n).2.2⟩
    exact Set.infinite_range_of_injective hxinj (hfinite.subset hrangeSubset)
  · exact hdivergent

/-- An infinite base regular-zero set, normalized by the standard compactness
subsequence, has all representatives tending to positive infinity once the
lower representative-count case is available. -/
theorem IsAbel.exists_restrictedRegularZeroSequence_all_representatives_tendsto
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (houter : RestrictedBaseRegularZeroFiniteForRepresentativeCount A m)
    {ι : Type} [Finite ι] {p a : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (hF : ∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (hZ : (regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)).Infinite) :
    ∃ x : ℕ → RestrictedSource (m + 1) p a,
      ∃ w₀ : RestrictedBoxSpace p,
        Function.Injective x ∧
        (∀ n, x n ∈ regularZeroSet
          (restrictedBaseOpenDomain D R) (constraintMap F)) ∧
        w₀ ∈ D.closedBox ∧
        Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀) ∧
        ∀ i, Tendsto (fun n ↦ (x n).1.1 i) atTop atTop := by
  obtain ⟨x, w₀, hxinj, hxmem, hw₀, hxlim, hclass⟩ :=
    Set.Infinite.exists_classified_restrictedRegularZeroSequence hZ
  exact ⟨x, w₀, hxinj, hxmem, hw₀, hxlim,
    hA.restrictedRegularZeroSequence_representatives_tendsto_atTop
      houter D representative offset R hDomain F hF x hxinj hxmem hclass⟩

end AbelFormalization
