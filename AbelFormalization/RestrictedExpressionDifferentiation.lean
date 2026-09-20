import AbelFormalization.DifferentiallyClosedTower
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Differentiating restricted expression towers

Analytic coefficient functions, source coordinates, and the permitted special
generators are the generators of the manuscript's base expression algebra.
This file proves the derivative rules for the fixed generators and packages
the remaining Abel-jet rule as an explicit hypothesis.  It then invokes the
generic exponential-tower theorem to obtain closure under every coordinate
direction at every tower level.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The cylinder over the closed bounded box.  Analytic coefficient
representatives are differentiable throughout this set. -/
def restrictedClosedBoxCylinder {m p a : ℕ} (D : RestrictedBox p) :
    Set (RestrictedSource m p a) :=
  {x | x.1.2 ∈ D.closedBox}

/-- The continuous linear projection from a restricted source to its bounded
box coordinates. -/
def restrictedBoxProjectionCLM {m p a : ℕ} :
    RestrictedSource m p a →L[ℝ] RestrictedBoxSpace p :=
  (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (RestrictedBoxSpace p)).comp
    (ContinuousLinearMap.fst ℝ
      ((Fin m → ℝ) × RestrictedBoxSpace p) (Fin a → ℝ))

@[simp]
theorem restrictedBoxProjectionCLM_apply {m p a : ℕ}
    (x : RestrictedSource m p a) :
    restrictedBoxProjectionCLM x = x.1.2 :=
  rfl

/-- Continuous linear form selecting one positive/unbounded source
coordinate. -/
def restrictedSCoordinateCLM {m p a : ℕ} (i : Fin m) :
    RestrictedSource m p a →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (RestrictedBoxSpace p)).comp
      (ContinuousLinearMap.fst ℝ
        ((Fin m → ℝ) × RestrictedBoxSpace p) (Fin a → ℝ)))

@[simp]
theorem restrictedSCoordinateCLM_apply {m p a : ℕ} (i : Fin m)
    (x : RestrictedSource m p a) : restrictedSCoordinateCLM i x = x.1.1 i :=
  rfl

/-- Continuous linear form selecting one unrestricted auxiliary source
coordinate. -/
def restrictedAuxCoordinateCLM {m p a : ℕ} (i : Fin a) :
    RestrictedSource m p a →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.snd ℝ
      ((Fin m → ℝ) × RestrictedBoxSpace p) (Fin a → ℝ))

@[simp]
theorem restrictedAuxCoordinateCLM_apply {m p a : ℕ} (i : Fin a)
    (x : RestrictedSource m p a) : restrictedAuxCoordinateCLM i x = x.2 i :=
  rfl

/-- Directional derivative of an analytic coefficient representative. -/
def RestrictedBox.directionalDerivative {p : ℕ} (D : RestrictedBox p)
    (v : RestrictedBoxSpace p)
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    RestrictedBox.analyticNearClosedBoxSubalgebra D :=
  ⟨fun w ↦ fderiv ℝ (f : RestrictedBoxSpace p → ℝ) w v, by
    change D.AnalyticNearClosedBox
      (fun w ↦ fderiv ℝ (f : RestrictedBoxSpace p → ℝ) w v)
    rw [D.analyticNearClosedBox_iff]
    exact (ContinuousLinearMap.apply ℝ ℝ v).comp_analyticOnNhd
      (D.analyticNearClosedBox_iff.mp f.property).fderiv⟩

/-- An analytic box coefficient pulled back to the full source has the
expected derivative along any fixed source direction. -/
theorem hasDirectionalDerivOn_restrictedBoxCoefficientPullback
    {m p a : ℕ} (D : RestrictedBox p)
    (v : RestrictedSource m p a)
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    HasDirectionalDerivOn (restrictedClosedBoxCylinder (m := m) (a := a) D) v
      (restrictedBoxCoefficientPullback (m := m) (a := a)
        (f : RestrictedBoxSpace p → ℝ))
      (restrictedBoxCoefficientPullback (m := m) (a := a)
        (D.directionalDerivative v.1.2 f : RestrictedBoxSpace p → ℝ)) := by
  intro x hx
  have hfan : AnalyticAt ℝ (f : RestrictedBoxSpace p → ℝ) x.1.2 :=
    (D.analyticNearClosedBox_iff.mp f.property) x.1.2 hx
  have hcomp := hfan.differentiableAt.hasFDerivAt.comp x
    (restrictedBoxProjectionCLM (m := m) (p := p) (a := a)).hasFDerivAt
  have heq : restrictedBoxCoefficientPullback (m := m) (a := a)
      (f : RestrictedBoxSpace p → ℝ) =
      (f : RestrictedBoxSpace p → ℝ) ∘
        restrictedBoxProjectionCLM (m := m) (p := p) (a := a) := by
    rfl
  constructor
  · rw [heq]
    exact hcomp.differentiableAt
  · have hfd := hcomp.fderiv
    have happ := congrArg
      (fun L : RestrictedSource m p a →L[ℝ] ℝ ↦ L v) hfd
    rw [heq]
    simpa [RestrictedBox.directionalDerivative,
      restrictedBoxCoefficientPullback] using happ

/-- The `s_i` coordinate derivative is the corresponding component of the
direction vector. -/
theorem hasDirectionalDerivOn_restrictedSCoordinate
    {m p a : ℕ} (D : RestrictedBox p)
    (v : RestrictedSource m p a) (i : Fin m) :
    HasDirectionalDerivOn (restrictedClosedBoxCylinder (m := m) (a := a) D) v
      (restrictedSCoordinate (p := p) (a := a) i)
      (fun _ ↦ v.1.1 i) := by
  intro x hx
  have heq : restrictedSCoordinate (p := p) (a := a) i =
      restrictedSCoordinateCLM (p := p) (a := a) i := by
    rfl
  constructor
  · rw [heq]
    exact (restrictedSCoordinateCLM (p := p) (a := a) i).differentiableAt
  · rw [heq, ContinuousLinearMap.fderiv]
    rfl

/-- The unrestricted auxiliary-coordinate derivative is the corresponding
component of the direction vector. -/
theorem hasDirectionalDerivOn_restrictedAuxCoordinate
    {m p a : ℕ} (D : RestrictedBox p)
    (v : RestrictedSource m p a) (i : Fin a) :
    HasDirectionalDerivOn (restrictedClosedBoxCylinder (m := m) (a := a) D) v
      (restrictedAuxCoordinate (m := m) (p := p) i)
      (fun _ ↦ v.2 i) := by
  intro x hx
  have heq : restrictedAuxCoordinate (m := m) (p := p) i =
      restrictedAuxCoordinateCLM (m := m) (p := p) i := by
    rfl
  constructor
  · rw [heq]
    exact (restrictedAuxCoordinateCLM (m := m) (p := p) i).differentiableAt
  · rw [heq, ContinuousLinearMap.fderiv]
    rfl

/-- The input needed from the chosen special generators.  In the intended
application these are Abel jets, and the field records the chain-rule
successor-jet formula for the chosen direction. -/
def SpecialGeneratorsDirectionallyClosed
    {m p a : ℕ} (D : RestrictedBox p)
    (S : Set (RestrictedSource m p a → ℝ))
    (Omega : Set (RestrictedSource m p a))
    (v : RestrictedSource m p a) : Prop :=
  ∀ f ∈ S, ∃ df : RestrictedSource m p a → ℝ,
    df ∈ restrictedExpressionBase D S ∧
      HasDirectionalDerivOn Omega v f df

/-- The base restricted-expression algebra is closed under differentiation
once the explicitly supplied special generators are. -/
theorem directionallyClosedOn_restrictedExpressionBase
    {m p a : ℕ} (D : RestrictedBox p)
    (S : Set (RestrictedSource m p a → ℝ))
    (Omega : Set (RestrictedSource m p a))
    (v : RestrictedSource m p a)
    (hOmega : Omega ⊆
      restrictedClosedBoxCylinder (m := m) (a := a) D)
    (hS : SpecialGeneratorsDirectionallyClosed D S Omega v) :
    DirectionallyClosedOn (restrictedExpressionBase D S)
      Omega v := by
  unfold restrictedExpressionBase
  apply directionallyClosedOn_adjoin
  intro f hf
  rcases hf with hf | hf
  · rcases hf with hcoords | hcoeff
    · rcases hcoords with hs | haux
      · rcases hs with ⟨i, rfl⟩
        refine ⟨fun _ ↦ v.1.1 i, ?_,
          (hasDirectionalDerivOn_restrictedSCoordinate D v i).mono hOmega⟩
        exact (Algebra.adjoin ℝ
          (restrictedFixedGenerators D ∪ S)).algebraMap_mem (v.1.1 i)
      · rcases haux with ⟨i, rfl⟩
        refine ⟨fun _ ↦ v.2 i, ?_,
          (hasDirectionalDerivOn_restrictedAuxCoordinate D v i).mono hOmega⟩
        exact (Algebra.adjoin ℝ
          (restrictedFixedGenerators D ∪ S)).algebraMap_mem (v.2 i)
    · rcases hcoeff with ⟨f, rfl⟩
      refine ⟨restrictedBoxCoefficientPullback (m := m) (a := a)
          (D.directionalDerivative v.1.2 f : RestrictedBoxSpace p → ℝ), ?_,
        (hasDirectionalDerivOn_restrictedBoxCoefficientPullback D v f).mono
          hOmega⟩
      exact restrictedBoxCoefficientPullback_mem_base D S
        (D.directionalDerivative v.1.2 f)
  · exact hS f hf

/-- Every level of a restricted exponential tower is closed under the chosen
directional derivative. -/
theorem RestrictedExpressionTower.directionallyClosedOn_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (Omega : Set (RestrictedSource m p a))
    (v : RestrictedSource m p a)
    (hOmega : Omega ⊆
      restrictedClosedBoxCylinder (m := m) (a := a) D)
    (hS : SpecialGeneratorsDirectionallyClosed D S Omega v) (j : ℕ) :
    DirectionallyClosedOn (T.level j)
      Omega v :=
  FiniteExponentialTower.directionallyClosedOn_level T
    (directionallyClosedOn_restrictedExpressionBase D S Omega v hOmega hS) j

end AbelFormalization
