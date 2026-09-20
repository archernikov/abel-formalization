import AbelFormalization.AbelNumeratorSystemPresentation
import AbelFormalization.RestrictedAbelJets

/-!
# Restricted graph systems for finite Abel numerator tuples

A common polynomial presentation is lifted to the restricted source with one
positive `s` coordinate per selected affine Abel-jet argument and the original
variables placed in the unrestricted auxiliary block.  The graph equations
are `s_j - 1 - ell_j(x)^2`.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

set_option maxRecDepth 10000 in
/-- Polynomial evaluation of functions already in a subalgebra stays in that
subalgebra. -/
theorem mvPolynomial_eval_functions_mem_subalgebra
    {X σ : Type*} (B : Subalgebra ℝ (X → ℝ))
    (v : σ → X → ℝ) (hv : ∀ i, v i ∈ B)
    (P : MvPolynomial σ ℝ) :
    (fun x ↦ MvPolynomial.eval (fun i ↦ v i x) P) ∈ B := by
  let vB : σ → B := fun i ↦ ⟨v i, hv i⟩
  let q : B := MvPolynomial.aeval vB P
  have hq : (q : X → ℝ) ∈ B := q.property
  convert hq using 1
  funext x
  let e : B →+* ℝ := subalgebraPointEval B x
  have heval := MvPolynomial.eval₂_comp_left
    e (algebraMap ℝ B) vB P
  have hcoeff : e.comp (algebraMap ℝ B) = RingHom.id ℝ := by
    ext c
    rfl
  have hval : e ∘ vB = fun i ↦ v i x := by
    funext i
    rfl
  change MvPolynomial.eval (fun i ↦ v i x) P = e q
  change MvPolynomial.eval (fun i ↦ v i x) P =
    e (MvPolynomial.aeval vB P)
  rw [MvPolynomial.aeval_def]
  unfold MvPolynomial.eval
  rw [← hcoeff, ← hval]
  exact heval.symm

/-- The unique zero-dimensional bounded box used by the final graph lift. -/
def abelNumeratorGraphEmptyBox : RestrictedBox 0 where
  lower := Fin.elim0
  upper := Fin.elim0
  lower_lt_upper := fun i ↦ Fin.elim0 i

/-- The zero analytic offset for every selected graph coordinate. -/
def abelNumeratorGraphZeroOffset {b : ℕ} (_j : Fin b) :
    RestrictedBox.analyticNearClosedBoxSubalgebra
      abelNumeratorGraphEmptyBox :=
  ⟨fun _ ↦ 0, abelNumeratorGraphEmptyBox.analyticNearClosedBox_zero⟩

namespace AbelNumeratorSystemPolynomialPresentation

variable {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F)

/-- The restricted source used for the numerator graph lift: selected Abel
arguments are the `s` coordinates, there are no bounded coordinates, and the
original variables are unrestricted auxiliary coordinates. -/
abbrev RestrictedGraphSource :=
  RestrictedSource P.generatorCount 0 n

/-- Special Abel-jet generators with identity representatives and zero
bounded offsets. -/
def restrictedGraphJetGenerators :
    Set (P.RestrictedGraphSource → ℝ) :=
  restrictedAbelJetGenerators (a := n) A (fun j ↦ j)
    abelNumeratorGraphZeroOffset

/-- The corresponding restricted expression base. -/
def restrictedGraphBase : Subalgebra ℝ (P.RestrictedGraphSource → ℝ) :=
  restrictedExpressionBase abelNumeratorGraphEmptyBox
    P.restrictedGraphJetGenerators

/-- Each polynomial variable as a function on the restricted graph source. -/
def restrictedGraphVariable :
    Fin n ⊕ Fin P.generatorCount → P.RestrictedGraphSource → ℝ
  | Sum.inl i => restrictedAuxCoordinate i
  | Sum.inr j => restrictedAbelJet A j (abelNumeratorGraphZeroOffset j)
      (P.derivativeOrder j)

/-- The lifted numerator row, polynomial in auxiliary coordinates and selected
Abel jets at the free `s` coordinates. -/
def restrictedLiftedNumerator (i : Fin n) : P.RestrictedGraphSource → ℝ :=
  fun y ↦ MvPolynomial.eval (fun z ↦ P.restrictedGraphVariable z y)
    (P.polynomial i)

/-- The affine argument evaluated on the unrestricted auxiliary block. -/
def restrictedAffineArgument (j : Fin P.generatorCount) :
    P.RestrictedGraphSource → ℝ :=
  fun y ↦ P.argument j y.2

/-- The graph value `1 + ell_j(x)^2` for every selected Abel argument. -/
def graphValue (x : RealEuclidean n) : RealEuclidean P.generatorCount :=
  fun j ↦ 1 + (P.argument j x) ^ 2

/-- Embed an original point into the restricted graph source. -/
def graphSource (x : RealEuclidean n) : P.RestrictedGraphSource :=
  ((P.graphValue x, Fin.elim0), x)

/-- Equations cutting out all selected argument graphs. -/
def restrictedGraphEquation (j : Fin P.generatorCount) :
    P.RestrictedGraphSource → ℝ :=
  fun y ↦ restrictedSCoordinate j y - 1 - (P.restrictedAffineArgument j y) ^ 2

/-- The augmented square family, with graph rows followed by lifted numerator
rows. -/
def restrictedAugmentedEquationFamily :
    Fin (P.generatorCount + n) → P.RestrictedGraphSource → ℝ :=
  Fin.addCases P.restrictedGraphEquation P.restrictedLiftedNumerator

/-- Every lifted polynomial variable belongs to the restricted base. -/
theorem restrictedGraphVariable_mem (z : Fin n ⊕ Fin P.generatorCount) :
    P.restrictedGraphVariable z ∈ P.restrictedGraphBase := by
  rcases z with i | j
  · exact restrictedAuxCoordinate_mem_base abelNumeratorGraphEmptyBox
      P.restrictedGraphJetGenerators i
  · apply specialGenerator_mem_base abelNumeratorGraphEmptyBox
    exact ⟨(j, P.derivativeOrder j), rfl⟩

/-- Every lifted numerator row lies in the restricted expression base. -/
theorem restrictedLiftedNumerator_mem (i : Fin n) :
    P.restrictedLiftedNumerator i ∈ P.restrictedGraphBase := by
  exact mvPolynomial_eval_functions_mem_subalgebra P.restrictedGraphBase
    P.restrictedGraphVariable P.restrictedGraphVariable_mem (P.polynomial i)

/-- Every pulled affine argument lies in the restricted expression base. -/
theorem restrictedAffineArgument_mem (j : Fin P.generatorCount) :
    P.restrictedAffineArgument j ∈ P.restrictedGraphBase := by
  have hpoly := mvPolynomial_eval_functions_mem_subalgebra
    P.restrictedGraphBase
    (fun i ↦ restrictedAuxCoordinate (m := P.generatorCount) (p := 0) i)
    (fun i ↦ restrictedAuxCoordinate_mem_base
      abelNumeratorGraphEmptyBox P.restrictedGraphJetGenerators i)
    (affinePolynomial (P.argument j))
  convert hpoly using 1
  funext y
  exact (eval_affinePolynomial (P.argument j) y.2).symm

/-- Every argument graph equation lies in the restricted expression base. -/
theorem restrictedGraphEquation_mem (j : Fin P.generatorCount) :
    P.restrictedGraphEquation j ∈ P.restrictedGraphBase := by
  have hs := restrictedSCoordinate_mem_base abelNumeratorGraphEmptyBox
    P.restrictedGraphJetGenerators j
  have hone := P.restrictedGraphBase.algebraMap_mem (1 : ℝ)
  have ha := P.restrictedAffineArgument_mem j
  have h := P.restrictedGraphBase.sub_mem
    (P.restrictedGraphBase.sub_mem hs hone)
    (P.restrictedGraphBase.pow_mem ha 2)
  convert h using 1
  funext y
  rfl

/-- Every row of the augmented square system lies in one restricted base. -/
theorem restrictedAugmentedEquationFamily_mem
    (e : Fin (P.generatorCount + n)) :
    P.restrictedAugmentedEquationFamily e ∈ P.restrictedGraphBase := by
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) e
  · simpa [restrictedAugmentedEquationFamily] using
      P.restrictedGraphEquation_mem j
  · simpa [restrictedAugmentedEquationFamily] using
      P.restrictedLiftedNumerator_mem i

/-- Each graph equation vanishes at the canonical graph source. -/
@[simp]
theorem restrictedGraphEquation_graphSource
    (j : Fin P.generatorCount) (x : RealEuclidean n) :
    P.restrictedGraphEquation j (P.graphSource x) = 0 := by
  change (1 + (P.argument j x) ^ 2) - 1 - (P.argument j x) ^ 2 = 0
  ring

/-- A selected restricted Abel jet at the graph source is the corresponding
`C_r` generator value. -/
@[simp]
theorem restrictedGraphVariable_graphSource_inr
    (j : Fin P.generatorCount) (x : RealEuclidean n) :
    P.restrictedGraphVariable (Sum.inr j) (P.graphSource x) =
      Cr A (P.derivativeOrder j) (P.argument j x) := by
  change iteratedDeriv (P.derivativeOrder j) A
      ((1 + (P.argument j x) ^ 2) + 0) =
    iteratedDeriv (P.derivativeOrder j) A (1 + (P.argument j x) ^ 2)
  rw [add_zero]

/-- Lifted numerator rows recover the original numerator system on the graph. -/
@[simp]
theorem restrictedLiftedNumerator_graphSource
    (i : Fin n) (x : RealEuclidean n) :
    P.restrictedLiftedNumerator i (P.graphSource x) = F i x := by
  rw [restrictedLiftedNumerator]
  rw [← P.eval_eq i x]
  apply congrArg (fun v ↦ MvPolynomial.eval v (P.polynomial i))
  funext z
  rcases z with k | j
  · rfl
  · exact P.restrictedGraphVariable_graphSource_inr j x

/-- Exact value of every augmented row on the canonical graph. -/
theorem restrictedAugmentedEquationFamily_graphSource
    (e : Fin (P.generatorCount + n)) (x : RealEuclidean n) :
    P.restrictedAugmentedEquationFamily e (P.graphSource x) =
      Fin.addCases (fun _ ↦ 0) (fun i ↦ F i x) e := by
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) e
  · simp [restrictedAugmentedEquationFamily]
  · simp [restrictedAugmentedEquationFamily]

end AbelNumeratorSystemPolynomialPresentation

end AbelFormalization
