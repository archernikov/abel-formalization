import AbelFormalization.AbelExistentialMainTheorem
import Lean.Util.CollectAxioms

/-! An independent, expanded check of the four existence requirements. -/

set_option autoImplicit false

namespace DraftExistenceAudit

theorem expanded_exists_abel :
    ∃ A : ℝ → ℝ,
      (∀ x : ℝ, 0 < x → AnalyticAt ℝ A x) ∧
      (∀ x : ℝ, 0 < x → 0 < deriv A x) ∧
      A 1 = 0 ∧
      (∀ x : ℝ, 0 < x → A (Real.exp x - 1) = A x + 1) := by
  obtain ⟨A, hA⟩ := AbelFormalization.exists_isAbel
  exact ⟨A, hA.analytic, hA.deriv_pos, hA.normalized, hA.abel⟩

end DraftExistenceAudit

#check AbelFormalization.exists_analytic_invariant_density
#check AbelFormalization.exists_isAbel
#check AbelFormalization.exists_abel_ominimal_expansion
#print axioms AbelFormalization.exists_isAbel
#print axioms AbelFormalization.exists_abel_ominimal_expansion
#print axioms DraftExistenceAudit.expanded_exists_abel

open Lean Elab Command in
run_elab do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``AbelFormalization.exists_analytic_invariant_density,
      ``AbelFormalization.exists_isAbel,
      ``AbelFormalization.exists_abel_ominimal_expansion,
      ``DraftExistenceAudit.expanded_exists_abel] do
    for axiomName in (← collectAxioms name) do
      unless permitted.contains axiomName do
        throwError "{name} uses forbidden axiom {axiomName}"
  logInfo "PASS: unconditional Abel existence and existential main theorem; only standard kernel axioms."
