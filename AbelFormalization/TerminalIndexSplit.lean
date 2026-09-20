import AbelFormalization.TerminalGlobalStirling
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false

/-!
# Splitting one terminal derivative block from the global variables

For a chosen block `b`, the global variable type is explicitly equivalent to
`Keep b ⊕ Fin (d b)`, where `Keep b` contains all other derivative blocks and
all retained variables.  The induced polynomial algebra equivalence lets the
one-block derivations be transported without adjoining duplicate variables.
-/

noncomputable section

namespace AbelFormalization

universe u v w

/-- Derivative variables belonging to blocks other than `b`. -/
abbrev TerminalOtherBlockIndex
    (Block : Type v) (d : Block → ℕ) (b : Block) :=
  Σ c : {c : Block // c ≠ b}, Fin (d c.1)

/-- All variables retained when the derivative block `b` is split off. -/
abbrev TerminalBlockKeepIndex
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block) :=
  TerminalOtherBlockIndex Block d b ⊕ Time

/-- Forward map that places the chosen block on the right summand. -/
def terminalSplitIndexTo
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block) :
    CentralPolynomialIndex Block d Time →
      TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b) := by
  classical
  intro x
  rcases x with x | t
  · rcases x with ⟨c, r⟩
    by_cases h : c = b
    · subst c
      exact Sum.inr r
    · exact Sum.inl (Sum.inl ⟨⟨c, h⟩, r⟩)
  · exact Sum.inl (Sum.inr t)

/-- Inverse map that reinserts the chosen block into the global sigma type. -/
def terminalSplitIndexFrom
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block) :
    TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b) →
      CentralPolynomialIndex Block d Time
  | Sum.inl (Sum.inl ⟨c, r⟩) => Sum.inl ⟨c.1, r⟩
  | Sum.inl (Sum.inr t) => Sum.inr t
  | Sum.inr r => Sum.inl ⟨b, r⟩

@[simp]
theorem terminalSplitIndexFrom_to
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block)
    (x : CentralPolynomialIndex Block d Time) :
    terminalSplitIndexFrom Block d Time b
        (terminalSplitIndexTo Block d Time b x) = x := by
  classical
  rcases x with x | t
  · rcases x with ⟨c, r⟩
    by_cases h : c = b
    · subst c
      simp [terminalSplitIndexTo, terminalSplitIndexFrom]
    · simp [terminalSplitIndexTo, terminalSplitIndexFrom, h]
  · simp [terminalSplitIndexTo, terminalSplitIndexFrom]

@[simp]
theorem terminalSplitIndexTo_from
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block)
    (x : TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) :
    terminalSplitIndexTo Block d Time b
        (terminalSplitIndexFrom Block d Time b x) = x := by
  classical
  rcases x with x | r
  · rcases x with x | t
    · rcases x with ⟨c, r⟩
      simp [terminalSplitIndexTo, terminalSplitIndexFrom, c.property]
    · simp [terminalSplitIndexTo, terminalSplitIndexFrom]
  · simp [terminalSplitIndexTo, terminalSplitIndexFrom]

/-- The actual equivalence between the global index and a one-block index. -/
def terminalSplitIndexEquiv
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block) :
    CentralPolynomialIndex Block d Time ≃
      TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b) where
  toFun := terminalSplitIndexTo Block d Time b
  invFun := terminalSplitIndexFrom Block d Time b
  left_inv := terminalSplitIndexFrom_to Block d Time b
  right_inv := terminalSplitIndexTo_from Block d Time b

section Rename

variable (R : Type u) [CommSemiring R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block)

/-- Renaming along the split-index equivalence. -/
def terminalSplitRenameEquiv :
    CentralPolynomial R Block d Time ≃ₐ[R]
      MvPolynomial (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R :=
  MvPolynomial.renameEquiv R (terminalSplitIndexEquiv Block d Time b)

@[simp]
theorem terminalSplitRenameEquiv_C (a : R) :
    terminalSplitRenameEquiv R Block d Time b (MvPolynomial.C a) =
      MvPolynomial.C a := by
  simp [terminalSplitRenameEquiv]

@[simp]
theorem terminalSplitRenameEquiv_X_sameBlock (r : Fin (d b)) :
    terminalSplitRenameEquiv R Block d Time b
        (MvPolynomial.X
          (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X (Sum.inr r) := by
  classical
  simp [terminalSplitRenameEquiv, terminalSplitIndexEquiv,
    terminalSplitIndexTo]

@[simp]
theorem terminalSplitRenameEquiv_X_otherBlock
    (c : Block) (hcb : c ≠ b) (r : Fin (d c)) :
    terminalSplitRenameEquiv R Block d Time b
        (MvPolynomial.X
          (Sum.inl ⟨c, r⟩ : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X
        (Sum.inl (Sum.inl ⟨⟨c, hcb⟩, r⟩)) := by
  classical
  simp [terminalSplitRenameEquiv, terminalSplitIndexEquiv,
    terminalSplitIndexTo, hcb]

@[simp]
theorem terminalSplitRenameEquiv_X_time (t : Time) :
    terminalSplitRenameEquiv R Block d Time b
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X (Sum.inl (Sum.inr t)) := by
  simp [terminalSplitRenameEquiv, terminalSplitIndexEquiv,
    terminalSplitIndexTo]

@[simp]
theorem terminalSplitRenameEquiv_symm_X_sameBlock (r : Fin (d b)) :
    (terminalSplitRenameEquiv R Block d Time b).symm
        (MvPolynomial.X (Sum.inr r)) =
      MvPolynomial.X
        (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time) := by
  simp [terminalSplitRenameEquiv, terminalSplitIndexEquiv,
    terminalSplitIndexFrom]

@[simp]
theorem terminalSplitRenameEquiv_symm_X_otherBlock
    (c : {c : Block // c ≠ b}) (r : Fin (d c.1)) :
    (terminalSplitRenameEquiv R Block d Time b).symm
        (MvPolynomial.X (Sum.inl (Sum.inl ⟨c, r⟩))) =
      MvPolynomial.X
        (Sum.inl ⟨c.1, r⟩ : CentralPolynomialIndex Block d Time) := by
  simp [terminalSplitRenameEquiv, terminalSplitIndexEquiv,
    terminalSplitIndexFrom]

@[simp]
theorem terminalSplitRenameEquiv_symm_X_time (t : Time) :
    (terminalSplitRenameEquiv R Block d Time b).symm
        (MvPolynomial.X (Sum.inl (Sum.inr t))) =
      MvPolynomial.X
        (Sum.inr t : CentralPolynomialIndex Block d Time) := by
  simp [terminalSplitRenameEquiv, terminalSplitIndexEquiv,
    terminalSplitIndexFrom]

end Rename

/-- The positive axis displacement in one block. -/
def terminalBlockAxis
    (Block : Type v) (b : Block) (k : ℕ) : TerminalMultidegree Block := by
  classical
  exact Finsupp.single b k

@[simp]
theorem terminalBlockAxis_apply_same
    (Block : Type v) (b : Block) (k : ℕ) :
    terminalBlockAxis Block b k b = k := by
  classical
  simp [terminalBlockAxis]

end AbelFormalization
