import AbelFormalization.WilkieSection4LiteralZeroInduction
import Lean.Util.CollectAxioms

/-!
Executable correspondence check for `omin.tex`, version 29, lines 64–68 and
111–141. The conclusion below spells out the hypotheses, the interpreted
structure, ordinary interval sets, first-order definability, inverse identities,
and growth quantifiers independently of the project's proposition aliases.
This checks the conditional main theorem; it does not construct an Abel function.
-/

set_option autoImplicit false

namespace DraftStatementAudit

/-- The interpretation displayed in the draft, with ordinary real operations. -/
@[instance_reducible] noncomputable def paperStructure (A : ℝ → ℝ) :
    AbelFormalization.abelLanguage.Structure ℝ where
  funMap
    | .add, x => x 0 + x 1
    | .mul, x => x 0 * x 1
    | .c0, x => A (1 + (x 0) ^ 2)
  RelMap
    | .lt, x => x 0 < x 1

example (A : ℝ → ℝ) :
    paperStructure A = AbelFormalization.abelStructure A := rfl

/-- The four bundled assumptions are exactly the draft's local hypotheses. -/
theorem hypotheses_iff (A : ℝ → ℝ) :
    AbelFormalization.IsAbel A ↔
      (∀ x : ℝ, 0 < x → AnalyticAt ℝ A x) ∧
      (∀ x : ℝ, 0 < x → 0 < deriv A x) ∧
      A 1 = 0 ∧
      (∀ x : ℝ, 0 < x → A (Real.exp x - 1) = A x + 1) := by
  constructor
  · intro h
    exact ⟨h.analytic, h.deriv_pos, h.normalized, h.abel⟩
  · rintro ⟨ha, hd, hn, he⟩
    exact ⟨ha, hd, hn, he⟩

/-- The proved theorem yields the literal conditional statement, with an actual
two-sided positive inverse and no geometric or finiteness premises. -/
theorem expanded_main_theorem
    (A : ℝ → ℝ)
    (ha : ∀ x : ℝ, 0 < x → AnalyticAt ℝ A x)
    (hd : ∀ x : ℝ, 0 < x → 0 < deriv A x)
    (hn : A 1 = 0)
    (he : ∀ x : ℝ, 0 < x → A (Real.exp x - 1) = A x + 1) :
    letI := paperStructure A
    (∀ s : Set ℝ,
      (Set.univ : Set ℝ).Definable₁ AbelFormalization.abelLanguage s →
      ∃ (n : ℕ) (pieces : Fin n → Set ℝ),
        s = ⋃ i, pieces i ∧
        ∀ i,
          (∃ a : ℝ, pieces i = {a}) ∨
          (∃ a b : ℝ, pieces i = Set.Ioo a b) ∨
          (∃ b : ℝ, pieces i = Set.Iio b) ∨
          (∃ a : ℝ, pieces i = Set.Ioi a) ∨
          pieces i = Set.univ) ∧
    (Set.univ : Set ℝ).Definable₂ AbelFormalization.abelLanguage
      {p : ℝ × ℝ | p.2 = Real.exp p.1} ∧
    ∃ T : ℝ → ℝ,
      (∀ t : ℝ, 0 < T t ∧ A (T t) = t) ∧
      (∀ x : ℝ, 0 < x → T (A x) = x) ∧
      (Set.univ : Set ℝ).Definable₂ AbelFormalization.abelLanguage
        {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = T p.1} ∧
      (∀ k : ℕ, ∃ s_k : ℝ,
        ∀ s : ℝ, s_k < s → (Real.exp^[k]) s < T s) := by
  let hA : AbelFormalization.IsAbel A := ⟨ha, hd, hn, he⟩
  obtain ⟨homin, hexp, hinv, hgrowth⟩ := AbelFormalization.mainTheorem A hA
  refine ⟨?_, hexp, AbelFormalization.inverse A,
    (fun t => ⟨hA.inverse_pos t, hA.apply_inverse t⟩),
    (fun x hx => hA.inverse_apply hx), hinv, hgrowth⟩
  intro s hs
  obtain ⟨n, pieces, hpieces⟩ := homin s hs
  refine ⟨n, fun i => (pieces i).carrier, hpieces, ?_⟩
  intro i
  cases hpiece : pieces i with
  | point a =>
      exact Or.inl ⟨a, by simp only [hpiece, AbelFormalization.UnaryPiece.carrier]⟩
  | bounded a b =>
      exact Or.inr (Or.inl ⟨a, b, by simp only [hpiece, AbelFormalization.UnaryPiece.carrier]⟩)
  | leftRay b =>
      exact Or.inr (Or.inr (Or.inl ⟨b, by simp only [hpiece, AbelFormalization.UnaryPiece.carrier]⟩))
  | rightRay a =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a, by simp only [hpiece, AbelFormalization.UnaryPiece.carrier]⟩)))
  | whole =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (by simp only [hpiece, AbelFormalization.UnaryPiece.carrier]))))

end DraftStatementAudit

#print AbelFormalization.IsAbel
#print AbelFormalization.MainTheorem
#check AbelFormalization.mainTheorem
#print axioms AbelFormalization.mainTheorem
#print axioms DraftStatementAudit.expanded_main_theorem

open Lean Elab Command in
run_elab do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``AbelFormalization.mainTheorem,
      ``DraftStatementAudit.expanded_main_theorem] do
    for axiomName in (← collectAxioms name) do
      unless permitted.contains axiomName do
        throwError "{name} uses forbidden axiom {axiomName}"
  logInfo "PASS: expanded draft statement, with only standard kernel axioms."
