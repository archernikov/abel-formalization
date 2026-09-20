import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false

/-!
# The actual coordinates in the paper's rank lemma

The source retains the product layout `((s,w),y)`. The coefficient
argument is `w`; the independent polynomial symbols are `y,s,V(s,w)`.
The arbitrary function `V` is only assumed smooth on the open projection
of the source domain onto `(s,w)`.
-/

noncomputable section

open Set
open scoped ContDiff

namespace AbelFormalization

abbrev PaperRankRealSpace (n : ℕ) := Fin n → ℝ

abbrev PaperRankParameterSpace (m p : ℕ) :=
  PaperRankRealSpace m × PaperRankRealSpace p

abbrev PaperRankSource (m p a : ℕ) :=
  PaperRankParameterSpace m p × PaperRankRealSpace a

abbrev PaperRankRetainedSymbols (m b : ℕ) := Fin m ⊕ Fin b

abbrev PaperRankSymbols (m a b : ℕ) := Fin a ⊕ PaperRankRetainedSymbols m b

/-- The actual coefficient variables in the source `((s,w),y)`. -/
def paperRankCoefficientArgument (m p a : ℕ) :
    PaperRankSource m p a → PaperRankRealSpace p :=
  fun x => x.1.2

/-- The retained symbol values are exactly `s,V(s,w)`. -/
def paperRankRetainedArgument {m p a b : ℕ}
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (x : PaperRankSource m p a) : PaperRankRetainedSymbols m b → ℝ :=
  Sum.elim x.1.1 (V x.1)

/-- The complete independent symbol assignment is exactly `y,s,V(s,w)`. -/
def paperRankSymbolArgument {m p a b : ℕ}
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (x : PaperRankSource m p a) : PaperRankSymbols m a b → ℝ :=
  Sum.elim x.2 (Sum.elim x.1.1 (V x.1))

@[simp]
theorem paperRankCoefficientArgument_apply (m p a : ℕ) (x : PaperRankSource m p a) :
    paperRankCoefficientArgument m p a x = x.1.2 := rfl

@[simp]
theorem paperRankSymbolArgument_aux {m p a b : ℕ}
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (x : PaperRankSource m p a) (i : Fin a) :
    paperRankSymbolArgument V x (Sum.inl i) = x.2 i := rfl

@[simp]
theorem paperRankSymbolArgument_free {m p a b : ℕ}
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (x : PaperRankSource m p a) (i : Fin m) :
    paperRankSymbolArgument V x (Sum.inr (Sum.inl i)) = x.1.1 i := rfl

@[simp]
theorem paperRankSymbolArgument_smooth {m p a b : ℕ}
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (x : PaperRankSource m p a) (i : Fin b) :
    paperRankSymbolArgument V x (Sum.inr (Sum.inr i)) = V x.1 i := rfl

/-- Restricting the full symbol assignment gives exactly the retained
assignment, with no change of coordinates on the source. -/
theorem paperRankSymbolArgument_comp_inr {m p a b : ℕ}
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (x : PaperRankSource m p a) :
    paperRankSymbolArgument V x ∘ Sum.inr = paperRankRetainedArgument V x := rfl

/-- The coefficient argument is a composition of linear coordinate
projections and is differentiable everywhere. -/
theorem differentiable_paperRankCoefficientArgument (m p a : ℕ) :
    Differentiable ℝ (paperRankCoefficientArgument m p a) := by
  exact (differentiable_fst :
    Differentiable ℝ (fun x : PaperRankSource m p a => x.1)).snd

theorem differentiableAt_paperRankCoefficientArgument (m p a : ℕ)
    (x : PaperRankSource m p a) :
    DifferentiableAt ℝ (paperRankCoefficientArgument m p a) x :=
  differentiable_paperRankCoefficientArgument m p a x

theorem differentiableOn_paperRankCoefficientArgument (m p a : ℕ)
    (Ω : Set (PaperRankSource m p a)) :
    DifferentiableOn ℝ (paperRankCoefficientArgument m p a) Ω :=
  (differentiable_paperRankCoefficientArgument m p a).differentiableOn

/-- The domain on which the paper assumes smoothness of `V` is open. -/
theorem isOpen_paperRankParameterProjection {m p a : ℕ}
    {Ω : Set (PaperRankSource m p a)} (hΩ : IsOpen Ω) :
    IsOpen (Prod.fst '' Ω) :=
  isOpenMap_fst Ω hΩ

/-- Smoothness on the open projected domain gives an ordinary derivative
at each actual projected source point. -/
theorem differentiableAt_paperRankSmoothFunction {m p a b : ℕ}
    {Ω : Set (PaperRankSource m p a)} (hΩ : IsOpen Ω)
    {V : PaperRankParameterSpace m p → PaperRankRealSpace b}
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω))
    {x : PaperRankSource m p a} (hx : x ∈ Ω) :
    DifferentiableAt ℝ V x.1 := by
  have hproj : IsOpen (Prod.fst '' Ω) := isOpen_paperRankParameterProjection hΩ
  have hxproj : x.1 ∈ Prod.fst '' Ω := ⟨x, hx, rfl⟩
  exact ((contDiffOn_infty.mp hV 1).differentiableOn_one).differentiableAt
    (hproj.mem_nhds hxproj)

/-- The retained symbol argument is differentiable at every point of the
original open source domain for the paper's arbitrary smooth `V`. -/
theorem differentiableAt_paperRankRetainedArgument {m p a b : ℕ}
    {Ω : Set (PaperRankSource m p a)} (hΩ : IsOpen Ω)
    {V : PaperRankParameterSpace m p → PaperRankRealSpace b}
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω))
    {x : PaperRankSource m p a} (hx : x ∈ Ω) :
    DifferentiableAt ℝ (paperRankRetainedArgument (a := a) V) x := by
  have hS : DifferentiableAt ℝ (fun t : PaperRankSource m p a => t.1.1) x :=
    (differentiableAt_fst :
      DifferentiableAt ℝ (fun t : PaperRankSource m p a => t.1) x).fst
  have hVcomp : DifferentiableAt ℝ (fun t : PaperRankSource m p a => V t.1) x :=
    (differentiableAt_paperRankSmoothFunction hΩ hV hx).comp x differentiableAt_fst
  apply differentiableAt_pi.mpr
  intro i
  cases i with
  | inl i => exact differentiableAt_pi.mp hS i
  | inr i => exact differentiableAt_pi.mp hVcomp i

/-- The full symbol assignment `y,s,V(s,w)` is differentiable at every
source point, with no restriction on the values or range of `V`. -/
theorem differentiableAt_paperRankSymbolArgument {m p a b : ℕ}
    {Ω : Set (PaperRankSource m p a)} (hΩ : IsOpen Ω)
    {V : PaperRankParameterSpace m p → PaperRankRealSpace b}
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω))
    {x : PaperRankSource m p a} (hx : x ∈ Ω) :
    DifferentiableAt ℝ (paperRankSymbolArgument V) x := by
  have hY : DifferentiableAt ℝ (fun t : PaperRankSource m p a => t.2) x :=
    differentiableAt_snd
  have hretained := differentiableAt_paperRankRetainedArgument hΩ hV hx
  apply differentiableAt_pi.mpr
  intro i
  cases i with
  | inl i => exact differentiableAt_pi.mp hY i
  | inr i => exact differentiableAt_pi.mp hretained i

theorem differentiableOn_paperRankRetainedArgument {m p a b : ℕ}
    {Ω : Set (PaperRankSource m p a)} (hΩ : IsOpen Ω)
    {V : PaperRankParameterSpace m p → PaperRankRealSpace b}
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω)) :
    DifferentiableOn ℝ (paperRankRetainedArgument (a := a) V) Ω := by
  intro x hx
  exact (differentiableAt_paperRankRetainedArgument hΩ hV hx).differentiableWithinAt

/-- The paper's smoothness assumption supplies the symbol-map hypothesis
of the genuine finite-polynomial chain rule on all of `Ω`. -/
theorem differentiableOn_paperRankSymbolArgument {m p a b : ℕ}
    {Ω : Set (PaperRankSource m p a)} (hΩ : IsOpen Ω)
    {V : PaperRankParameterSpace m p → PaperRankRealSpace b}
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω)) :
    DifferentiableOn ℝ (paperRankSymbolArgument V) Ω := by
  intro x hx
  exact (differentiableAt_paperRankSymbolArgument hΩ hV hx).differentiableWithinAt

end AbelFormalization
