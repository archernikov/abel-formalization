import AbelFormalization.Consequences
import AbelFormalization.Definability

/-!
# Reduction of the main theorem to o-minimality

This file isolates the o-minimality clause and proves that it is equivalent to
the full manuscript theorem once the definability and growth results are
available.  The theorem `AbelFormalization.mainTheorem`, assembled later from
the complement pipeline and bounded deep Section 4 induction, proves both
equivalent propositions.
-/

namespace AbelFormalization

/-- The o-minimality clause of the manuscript's main theorem. -/
def OMinimalityClaim : Prop :=
  ∀ A : ℝ → ℝ, IsAbel A → OMinimal A

/-- The other clauses of the proposed main theorem are now established, so
proving the main theorem is equivalent to proving its o-minimality clause. -/
theorem mainTheorem_iff_ominimality : MainTheorem ↔ OMinimalityClaim := by
  constructor
  · intro h A hA
    exact (h A hA).1
  · intro h A hA
    exact ⟨h A hA, hA.exponentialDefinable, hA.positiveInverseDefinable,
      hA.isTransexponential⟩

end AbelFormalization
