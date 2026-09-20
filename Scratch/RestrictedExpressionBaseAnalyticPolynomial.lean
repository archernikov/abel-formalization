import AbelFormalization.PolynomialGraphLift
import AbelFormalization.RestrictedAbelJets
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial representatives for the restricted expression base

The coefficient ring is the algebra of functions analytic near the closed
bounded box.  The polynomial variables are, in order, the unrestricted
auxiliary coordinates, the positive/unbounded `s` coordinates, and all named
shifted Abel jets.  Although the last indexing type may be infinite, every
multivariate polynomial uses only finitely many of those jet variables.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Symbols occurring in a polynomial representative of an element of the
restricted expression base: auxiliary variables, `s` variables, and named
shifted Abel jets. -/
abbrev RestrictedBasePolynomialSymbol (ι : Type*) (m a : ℕ) :=
  Fin a ⊕ (Fin m ⊕ (ι × ℕ))

/-- The value of one polynomial symbol at a restricted source point. -/
def restrictedBasePolynomialSymbolValue
    (A : ℝ → ℝ) {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (x : RestrictedSource m p a) :
    RestrictedBasePolynomialSymbol ι m a → ℝ
  | Sum.inl k => x.2 k
  | Sum.inr (Sum.inl i) => x.1.1 i
  | Sum.inr (Sum.inr kr) =>
      restrictedAbelJet A (representative kr.1)
        (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2 x

/-- Evaluate a polynomial representative on the original restricted source.
Analytic coefficients are evaluated at the bounded coordinate `w = x.1.2`;
the polynomial variables are evaluated by
`restrictedBasePolynomialSymbolValue`. -/
def restrictedBasePolynomialValue
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    RestrictedSource m p a → ℝ :=
  fun x =>
    MvPolynomial.eval₂
      (subalgebraPointEval
        (RestrictedBox.analyticNearClosedBoxSubalgebra D) x.1.2)
      (restrictedBasePolynomialSymbolValue A representative offset x) P

@[simp]
theorem restrictedBasePolynomialValue_C
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedBasePolynomialValue A D representative offset
        (MvPolynomial.C b) =
      restrictedBoxCoefficientPullback (m := m) (a := a)
        (b : RestrictedBoxSpace p → ℝ) := by
  funext x
  simp [restrictedBasePolynomialValue, restrictedBoxCoefficientPullback]

@[simp]
theorem restrictedBasePolynomialValue_X_aux
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (k : Fin a) :
    restrictedBasePolynomialValue A D representative offset
        (MvPolynomial.X (Sum.inl k)) =
      restrictedAuxCoordinate (m := m) (p := p) k := by
  funext x
  simp [restrictedBasePolynomialValue,
    restrictedBasePolynomialSymbolValue, restrictedAuxCoordinate]

@[simp]
theorem restrictedBasePolynomialValue_X_s
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin m) :
    restrictedBasePolynomialValue A D representative offset
        (MvPolynomial.X (Sum.inr (Sum.inl i))) =
      restrictedSCoordinate (p := p) (a := a) i := by
  funext x
  simp [restrictedBasePolynomialValue,
    restrictedBasePolynomialSymbolValue, restrictedSCoordinate]

@[simp]
theorem restrictedBasePolynomialValue_X_jet
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (kr : ι × ℕ) :
    restrictedBasePolynomialValue (a := a) A D representative offset
        (MvPolynomial.X (Sum.inr (Sum.inr kr))) =
      restrictedAbelJet (a := a) A (representative kr.1)
        (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2 := by
  funext x
  simp [restrictedBasePolynomialValue,
    restrictedBasePolynomialSymbolValue]

@[simp]
theorem restrictedBasePolynomialValue_add
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (P Q : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    restrictedBasePolynomialValue A D representative offset (P + Q) =
      restrictedBasePolynomialValue A D representative offset P +
        restrictedBasePolynomialValue A D representative offset Q := by
  funext x
  simp [restrictedBasePolynomialValue]

@[simp]
theorem restrictedBasePolynomialValue_mul
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (P Q : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    restrictedBasePolynomialValue A D representative offset (P * Q) =
      restrictedBasePolynomialValue A D representative offset P *
        restrictedBasePolynomialValue A D representative offset Q := by
  funext x
  simp [restrictedBasePolynomialValue]

@[simp]
theorem restrictedBasePolynomialValue_C_algebraMap
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (r : ℝ) :
    restrictedBasePolynomialValue A D representative offset
        (MvPolynomial.C
          (algebraMap ℝ
            (RestrictedBox.analyticNearClosedBoxSubalgebra D) r)) =
      algebraMap ℝ (RestrictedSource m p a → ℝ) r := by
  funext x
  simp [restrictedBasePolynomialValue]

/-- Every element of the restricted Abel expression base is the value of one
multivariate polynomial whose coefficients are analytic near the closed box.
The polynomial itself supplies the required finiteness: its `vars` is a
finite set even when `ι` is infinite. -/
theorem exists_restrictedBasePolynomialValue_eq_of_mem
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {f : RestrictedSource m p a → ℝ}
    (hf : f ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    ∃ P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
        (RestrictedBox.analyticNearClosedBoxSubalgebra D),
      restrictedBasePolynomialValue A D representative offset P = f := by
  change f ∈ Algebra.adjoin ℝ
    (restrictedFixedGenerators D ∪
      restrictedAbelJetGenerators (a := a) A representative offset) at hf
  refine Algebra.adjoin_induction
    (p := fun g _ =>
      ∃ P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
        restrictedBasePolynomialValue A D representative offset P = g)
    ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with hfixed | hjet
    · change g ∈
        (Set.range (restrictedSCoordinate (m := m) (p := p) (a := a)) ∪
          Set.range (restrictedAuxCoordinate (m := m) (p := p) (a := a))) ∪
            Set.range (fun b :
                RestrictedBox.analyticNearClosedBoxSubalgebra D =>
              restrictedBoxCoefficientPullback (m := m) (a := a)
                (b : RestrictedBoxSpace p → ℝ)) at hfixed
      rcases hfixed with (hsaux | hcoeff)
      · rcases hsaux with hs | haux
        · rcases hs with ⟨i, rfl⟩
          exact ⟨MvPolynomial.X (Sum.inr (Sum.inl i)),
            restrictedBasePolynomialValue_X_s
              A D representative offset i⟩
        · rcases haux with ⟨k, rfl⟩
          exact ⟨MvPolynomial.X (Sum.inl k),
            restrictedBasePolynomialValue_X_aux
              A D representative offset k⟩
      · rcases hcoeff with ⟨b, rfl⟩
        exact ⟨MvPolynomial.C b,
          restrictedBasePolynomialValue_C A D representative offset b⟩
    · change g ∈ Set.range (fun kr : ι × ℕ =>
        restrictedAbelJet A (representative kr.1)
          (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2) at hjet
      rcases hjet with ⟨kr, rfl⟩
      exact ⟨MvPolynomial.X (Sum.inr (Sum.inr kr)),
        restrictedBasePolynomialValue_X_jet
          (a := a) A D representative offset kr⟩
  · intro r
    exact ⟨MvPolynomial.C
        (algebraMap ℝ
          (RestrictedBox.analyticNearClosedBoxSubalgebra D) r),
      restrictedBasePolynomialValue_C_algebraMap
        A D representative offset r⟩
  · intro g h hgmem hhmem hg hh
    rcases hg with ⟨P, hP⟩
    rcases hh with ⟨Q, hQ⟩
    refine ⟨P + Q, ?_⟩
    rw [restrictedBasePolynomialValue_add, hP, hQ]
  · intro g h hgmem hhmem hg hh
    rcases hg with ⟨P, hP⟩
    rcases hh with ⟨Q, hQ⟩
    refine ⟨P * Q, ?_⟩
    rw [restrictedBasePolynomialValue_mul, hP, hQ]

end AbelFormalization
