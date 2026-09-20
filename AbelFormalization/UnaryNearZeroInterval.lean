import AbelFormalization.UnaryPieceDecomposition
import Mathlib.Topology.Order.DenselyOrdered

/-!
# A near-zero interval from a finite unary decomposition

This is the elementary one-dimensional consequence of WS5 used twice in
Wilkie 3.10.  If a positive unary set has finitely many point and open
interval/ray pieces and accumulates at zero, one of its pieces contains
every sufficiently small positive real number.  Definability of a radial
or minor range must be supplied separately before applying this theorem.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- An accumulated positive set with finitely many unary pieces contains
a whole interval immediately to the right of zero. -/
theorem UnaryPieceDecomposable.exists_Ioo_zero_subset
    {s : Set ℝ} (hs : UnaryPieceDecomposable s)
    (hpositive : s ⊆ Ioi (0 : ℝ))
    (hzero : (0 : ℝ) ∈ closure s) :
    ∃ η : ℝ, 0 < η ∧ Ioo (0 : ℝ) η ⊆ s := by
  obtain ⟨n, pieces, heq⟩ := hs
  have hpieceSubset (i : Fin n) : (pieces i).carrier ⊆ s := by
    rw [heq]
    intro x hx
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hzeroPiece :
      (0 : ℝ) ∈ ⋃ i : Fin n, closure ((pieces i).carrier) := by
    rw [heq, closure_iUnion_of_finite] at hzero
    exact hzero
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzeroPiece
  have hp : (pieces i).carrier ⊆ Ioi (0 : ℝ) :=
    (hpieceSubset i).trans hpositive
  cases hpiece : pieces i with
  | point a =>
      have ha0 : (0 : ℝ) = a := by
        simpa only [hpiece, UnaryPiece.carrier, closure_singleton,
          mem_singleton_iff] using hi
      have haPositive : 0 < a :=
        hp (by simpa only [hpiece, UnaryPiece.carrier,
          mem_singleton_iff])
      rw [← ha0] at haPositive
      exact (lt_irrefl (0 : ℝ) haPositive).elim
  | bounded a b =>
      rw [hpiece] at hi
      change (0 : ℝ) ∈ closure (Ioo a b) at hi
      by_cases hab : a < b
      · rw [closure_Ioo hab.ne] at hi
        have haLeZero : a ≤ 0 := hi.1
        have hzeroLeB : 0 ≤ b := hi.2
        by_cases haNeg : a < 0
        · have hx : a / 2 ∈ (pieces i).carrier := by
            rw [hpiece]
            change a < a / 2 ∧ a / 2 < b
            constructor <;> linarith
          have hxPos := hp hx
          change 0 < a / 2 at hxPos
          linarith
        · have haZero : a = 0 :=
            le_antisymm haLeZero (le_of_not_gt haNeg)
          have hbPos : 0 < b := by linarith
          refine ⟨b, hbPos, ?_⟩
          intro x hx
          apply hpieceSubset i
          rw [hpiece]
          simpa only [UnaryPiece.carrier, haZero] using hx
      · have hnonempty : Ioo a b = ∅ := by
          ext x
          constructor
          · intro hx
            have hba : b ≤ a := le_of_not_gt hab
            exact (False.elim (by linarith [hx.1, hx.2]))
          · intro hx
            exact hx.elim
        simp only [hnonempty, closure_empty, mem_empty_iff_false] at hi
  | leftRay b =>
      rw [hpiece] at hi
      change (0 : ℝ) ∈ closure (Iio b) at hi
      rw [closure_Iio b] at hi
      change (0 : ℝ) ≤ b at hi
      have hx : (-1 : ℝ) ∈ (pieces i).carrier := by
        rw [hpiece]
        change (-1 : ℝ) < b
        linarith
      have hxPos := hp hx
      change 0 < (-1 : ℝ) at hxPos
      linarith
  | rightRay a =>
      rw [hpiece] at hi
      change (0 : ℝ) ∈ closure (Ioi a) at hi
      rw [closure_Ioi a] at hi
      by_cases haNeg : a < 0
      · have hx : a / 2 ∈ (pieces i).carrier := by
          rw [hpiece]
          change a < a / 2
          linarith
        have hxPos := hp hx
        change 0 < a / 2 at hxPos
        linarith
      · have haZero : a = 0 :=
          le_antisymm hi (le_of_not_gt haNeg)
        refine ⟨1, by norm_num, ?_⟩
        intro x hx
        apply hpieceSubset i
        rw [hpiece]
        change a < x
        rw [haZero]
        exact hx.1
  | whole =>
      have hzeroPositive : (0 : ℝ) ∈ Ioi (0 : ℝ) :=
        hp (by simp only [hpiece, UnaryPiece.carrier,
          mem_univ])
      exact (lt_irrefl (0 : ℝ) hzeroPositive).elim

end AbelFormalization
