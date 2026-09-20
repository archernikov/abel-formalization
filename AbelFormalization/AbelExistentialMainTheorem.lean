import AbelFormalization.AbelExistence
import AbelFormalization.WilkieSection4LiteralZeroInduction

/-!
# Existence of the transexponential o-minimal expansion

The independent existence construction supplies an actual instance of the
four Abel hypotheses to which the manuscript's universal main theorem applies.
-/

namespace AbelFormalization

theorem exists_abel_ominimal_expansion :
    ∃ A : ℝ → ℝ, IsAbel A ∧
      OMinimal A ∧ ExponentialDefinable A ∧
        PositiveInverseDefinable A (inverse A) ∧
          IsTransexponential (inverse A) := by
  obtain ⟨A, hA⟩ := exists_isAbel
  exact ⟨A, hA, mainTheorem A hA⟩

end AbelFormalization
