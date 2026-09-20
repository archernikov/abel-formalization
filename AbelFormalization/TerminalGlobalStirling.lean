import AbelFormalization.CentralPolynomialEquiv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option autoImplicit false

/-!
# The global signed-Stirling action and its multigrading

The terminal ideal argument uses the signed-Stirling substitution on every
derivative block while fixing all retained variables.  This file constructs
that global action as an actual algebra equivalence and records the genuine
block multigrading whose block variable of order `r + 1` has weight
`(r + 1) e_b`.
-/

noncomputable section

namespace AbelFormalization

universe u v w

/-- The additive monoid of block multidegrees. -/
abbrev TerminalMultidegree (Block : Type v) := Block →₀ ℕ

/-- The manuscript's multigrading: a block variable indexed by `r : Fin d`
has positive order `r + 1` in its own block, while retained variables have
weight zero. -/
def terminalGlobalWeight (Block : Type v) (d : Block → ℕ) (Time : Type w) :
    CentralPolynomialIndex Block d Time → TerminalMultidegree Block := by
  classical
  exact fun x =>
    match x with
    | Sum.inl ⟨b, r⟩ => Finsupp.single b (r.val + 1)
    | Sum.inr _ => 0

@[simp]
theorem terminalGlobalWeight_block
    (Block : Type v) (d : Block → ℕ) (Time : Type w)
    (b : Block) (r : Fin (d b)) :
    terminalGlobalWeight Block d Time
        (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time) =
      Finsupp.single b (r.val + 1) := by
  simp [terminalGlobalWeight]

@[simp]
theorem terminalGlobalWeight_time
    (Block : Type v) (d : Block → ℕ) (Time : Type w) (t : Time) :
    terminalGlobalWeight Block d Time
        (Sum.inr t : CentralPolynomialIndex Block d Time) = 0 := by
  simp [terminalGlobalWeight]

section GlobalAction

variable (R : Type u) [CommRing R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w)

/-- Projection to one actual block multidegree. -/
def terminalGlobalComponent (degree : TerminalMultidegree Block) :
    CentralPolynomial R Block d Time →ₗ[R]
      CentralPolynomial R Block d Time :=
  MvPolynomial.weightedHomogeneousComponent
    (terminalGlobalWeight Block d Time) degree

open scoped Classical in
@[simp]
theorem terminalGlobalComponent_coeff
    (degree : TerminalMultidegree Block)
    (P : CentralPolynomial R Block d Time)
    (m : CentralPolynomialIndex Block d Time →₀ ℕ) :
    (terminalGlobalComponent R Block d Time degree P).coeff m =
      if Finsupp.weight (terminalGlobalWeight Block d Time) m = degree
      then P.coeff m else 0 := by
  classical
  change
    (MvPolynomial.weightedHomogeneousComponent
      (terminalGlobalWeight Block d Time) degree P).coeff m = _
  exact MvPolynomial.coeff_weightedHomogeneousComponent
    (w := terminalGlobalWeight Block d Time) degree P m

/-- The forward global signed-Stirling homomorphism fixes retained variables. -/
def terminalGlobalStirlingForwardHom :
    CentralPolynomial R Block d Time →ₐ[R]
      CentralPolynomial R Block d Time :=
  centralBlockAffineHom R Block d Time
    (fun b => centralSignedStirlingMatrix R (d b)) (fun _ => 0)

/-- The inverse global homomorphism uses the inverse unitriangular matrices
and again fixes every retained variable. -/
def terminalGlobalStirlingInverseHom :
    CentralPolynomial R Block d Time →ₐ[R]
      CentralPolynomial R Block d Time :=
  centralBlockAffineHom R Block d Time
    (fun b => (centralSignedStirlingMatrix R (d b))⁻¹) (fun _ => 0)

theorem terminalGlobalStirlingForwardHom_comp_inverseHom :
    (terminalGlobalStirlingForwardHom R Block d Time).comp
        (terminalGlobalStirlingInverseHom R Block d Time) =
      AlgHom.id R (CentralPolynomial R Block d Time) := by
  calc
    (terminalGlobalStirlingForwardHom R Block d Time).comp
        (terminalGlobalStirlingInverseHom R Block d Time) =
      centralBlockAffineHom R Block d Time
        (fun b => (centralSignedStirlingMatrix R (d b))⁻¹ *
          centralSignedStirlingMatrix R (d b))
        (fun _ => (0 : R) + 0) :=
      centralBlockAffineHom_comp R Block d Time _ _ _ _
    _ = centralBlockAffineHom R Block d Time
        (fun b => (1 : Matrix (Fin (d b)) (Fin (d b)) R))
        (fun _ => 0) := by
      have hm :
          (fun b => (centralSignedStirlingMatrix R (d b))⁻¹ *
              centralSignedStirlingMatrix R (d b)) =
            (fun b => (1 : Matrix (Fin (d b)) (Fin (d b)) R)) := by
        funext b
        exact centralSignedStirlingMatrix_inv_mul R (d b)
      have hc : (fun _ : Time => (0 : R) + 0) = (fun _ => 0) := by
        funext t
        simp
      rw [hm, hc]
    _ = AlgHom.id R (CentralPolynomial R Block d Time) :=
      centralBlockAffineHom_one_zero R Block d Time

theorem terminalGlobalStirlingInverseHom_comp_forwardHom :
    (terminalGlobalStirlingInverseHom R Block d Time).comp
        (terminalGlobalStirlingForwardHom R Block d Time) =
      AlgHom.id R (CentralPolynomial R Block d Time) := by
  calc
    (terminalGlobalStirlingInverseHom R Block d Time).comp
        (terminalGlobalStirlingForwardHom R Block d Time) =
      centralBlockAffineHom R Block d Time
        (fun b => centralSignedStirlingMatrix R (d b) *
          (centralSignedStirlingMatrix R (d b))⁻¹)
        (fun _ => (0 : R) + 0) :=
      centralBlockAffineHom_comp R Block d Time _ _ _ _
    _ = centralBlockAffineHom R Block d Time
        (fun b => (1 : Matrix (Fin (d b)) (Fin (d b)) R))
        (fun _ => 0) := by
      have hm :
          (fun b => centralSignedStirlingMatrix R (d b) *
              (centralSignedStirlingMatrix R (d b))⁻¹) =
            (fun b => (1 : Matrix (Fin (d b)) (Fin (d b)) R)) := by
        funext b
        exact centralSignedStirlingMatrix_mul_inv R (d b)
      have hc : (fun _ : Time => (0 : R) + 0) = (fun _ => 0) := by
        funext t
        simp
      rw [hm, hc]
    _ = AlgHom.id R (CentralPolynomial R Block d Time) :=
      centralBlockAffineHom_one_zero R Block d Time

/-- The manuscript's global terminal automorphism `J`. -/
def terminalGlobalStirlingEquiv :
    CentralPolynomial R Block d Time ≃ₐ[R]
      CentralPolynomial R Block d Time :=
  AlgEquiv.ofAlgHom
    (terminalGlobalStirlingForwardHom R Block d Time)
    (terminalGlobalStirlingInverseHom R Block d Time)
    (terminalGlobalStirlingForwardHom_comp_inverseHom R Block d Time)
    (terminalGlobalStirlingInverseHom_comp_forwardHom R Block d Time)

@[simp]
theorem terminalGlobalStirlingEquiv_C (a : R) :
    terminalGlobalStirlingEquiv R Block d Time (MvPolynomial.C a) =
      MvPolynomial.C a := by
  simp [terminalGlobalStirlingEquiv, terminalGlobalStirlingForwardHom]

/-- On each derivative block the global action is exactly the signed-Stirling
lower-triangular substitution. -/
@[simp]
theorem terminalGlobalStirlingEquiv_X_block
    (b : Block) (i : Fin (d b)) :
    terminalGlobalStirlingEquiv R Block d Time
        (MvPolynomial.X
          (Sum.inl ⟨b, i⟩ : CentralPolynomialIndex Block d Time)) =
      ∑ j : Fin (d b),
        MvPolynomial.C
          (if j ≤ i then (signedStirling (i.val + 1) (j.val + 1) : R) else 0) *
        MvPolynomial.X
          (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) := by
  simp [terminalGlobalStirlingEquiv, terminalGlobalStirlingForwardHom,
    centralSignedStirlingMatrix]

/-- Every retained variable is fixed by the global terminal action. -/
@[simp]
theorem terminalGlobalStirlingEquiv_X_time (t : Time) :
    terminalGlobalStirlingEquiv R Block d Time
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X
        (Sum.inr t : CentralPolynomialIndex Block d Time) := by
  simp [terminalGlobalStirlingEquiv, terminalGlobalStirlingForwardHom]

@[simp]
theorem terminalGlobalStirlingEquiv_height_map
    (I : Ideal (CentralPolynomial R Block d Time)) :
    (I.map (terminalGlobalStirlingEquiv R Block d Time).toRingHom).height =
      I.height :=
  (terminalGlobalStirlingEquiv R Block d Time).toRingEquiv.height_map I

/-- Closure under the actual multigraded projections. -/
def IsTerminalMultigradedIdeal
    (I : Ideal (CentralPolynomial R Block d Time)) : Prop :=
  ∀ P ∈ I, ∀ degree : TerminalMultidegree Block,
    terminalGlobalComponent R Block d Time degree P ∈ I

/-- Forward invariance under the actual global signed-Stirling action. -/
def IsTerminalGlobalStirlingInvariant
    (I : Ideal (CentralPolynomial R Block d Time)) : Prop :=
  ∀ P ∈ I, terminalGlobalStirlingEquiv R Block d Time P ∈ I

end GlobalAction

end AbelFormalization
