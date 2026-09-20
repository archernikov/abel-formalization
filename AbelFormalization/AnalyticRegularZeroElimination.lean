import AbelFormalization.AnalyticGermFormalJacobian
import AbelFormalization.AnalyticJacobianElimination

/-!
# Elimination at regular zeros of actual analytic-coefficient equations

The contracted ideal is explicit,
and the finite generator representatives are analytic on one neighborhood
of the coefficient origin. The denominator condition in the algebraic
elimination theorem is proved from the actual chain rule and surjectivity
of the actual Fréchet derivative.

The source can be any real normed space. This core assumes analyticity for
all coefficient functions; a finite-support padding wrapper can remove the
irrelevant assumptions outside each polynomial's support.
-/

noncomputable section

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

variable {Keep E : Type*} [Fintype Keep]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact Jacobian elimination ideal has height at least `r` and finite
analytic generator representatives which vanish at every actual regular
zero whose coefficient argument lies in one fixed smaller neighborhood.
There is no additional formal-rank or denominator hypothesis. -/
theorem exists_analyticRegularZeroElimination (p r a : ℕ)
    (P : Fin (r + a) → MvPolynomial (Fin a ⊕ Keep) (RealAnalyticGerm p))
    (coeff : Fin (r + a) → ((Fin a ⊕ Keep) →₀ ℕ) → (Fin p → ℝ) → ℝ)
    (W₀ : Set (Fin p → ℝ)) (hW₀ : IsOpen W₀) (h0W₀ : (0 : Fin p → ℝ) ∈ W₀)
    (hcoeff : ∀ i d, AnalyticOnNhd ℝ (coeff i d) W₀)
    (hrep : ∀ i d, d ∈ (P i).support → (P i).coeff d =
      analyticGermOf (coeff i d) (hcoeff i d 0 h0W₀))
    (Ω : Set E) (hΩ : IsOpen Ω)
    (w : E → Fin p → ℝ) (z : E → (Fin a ⊕ Keep) → ℝ)
    (hw : DifferentiableOn ℝ w Ω) (hz : DifferentiableOn ℝ z Ω) :
    ∃ I : Ideal (MvPolynomial Keep (RealAnalyticGerm p)), ∃ c : ℕ,
      ∃ g : Fin c → MvPolynomial Keep (RealAnalyticGerm p),
      ∃ G : Fin c → (Fin p → ℝ) → MvPolynomial Keep ℝ,
      ∃ W : Set (Fin p → ℝ),
        I = jacobianEliminationIdeal a P (analyticGermFormalDerivations p) ∧
        (r : ℕ∞) ≤ I.height ∧
        Ideal.span (Set.range g) = I ∧
        IsOpen W ∧ (0 : Fin p → ℝ) ∈ W ∧ W ⊆ W₀ ∧
        (∀ j v, (G j v).support ⊆ (g j).support) ∧
        (∀ j e, AnalyticOnNhd ℝ (fun v => (G j v).coeff e) W) ∧
        (∀ j, analyticPolynomialGermHom (0 : Fin p → ℝ) (g j) =
          (G j : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial Keep ℝ))) ∧
        ∀ x ∈ Ω, w x ∈ W →
          polynomialFamilyEvaluation (fun i => (P i).support) coeff w z x = 0 →
          Function.Surjective
            (fderiv ℝ (polynomialFamilyEvaluation (fun i => (P i).support) coeff w z) x) →
          ∀ j, MvPolynomial.eval ((z x) ∘ Sum.inr) (G j (w x)) = 0 := by
  classical
  let PRep : Fin (r + a) → (Fin p → ℝ) → MvPolynomial (Fin a ⊕ Keep) ℝ :=
    fun i => polynomialFromCoefficientRepresentatives (P i).support (coeff i)
  let dRep : (Fin p → ℝ) → MvPolynomial (Fin a ⊕ Keep) ℝ :=
    analyticGermJacobianDenominatorRepresentative P coeff
  have hcoeff0 : ∀ i d, AnalyticAt ℝ (coeff i d) 0 :=
    fun i d => hcoeff i d 0 h0W₀
  have hP : ∀ i, analyticPolynomialGermHom (0 : Fin p → ℝ) (P i) =
      (PRep i : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial (Fin a ⊕ Keep) ℝ)) := by
    intro i
    exact analyticPolynomialGermHom_eq_coefficientRepresentative
      0 (P i) (coeff i) (hcoeff0 i) (hrep i)
  have hd : analyticPolynomialGermHom (0 : Fin p → ℝ)
        (derivationJacobianDenominator P (analyticGermFormalDerivations p)) =
      (dRep : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial (Fin a ⊕ Keep) ℝ)) :=
    analyticPolynomialGermHom_formalJacobianDenominator P coeff hcoeff0 hrep
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W, hWW₀,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_analyticJacobianElimination p r a P (analyticGermFormalDerivations p)
      PRep dRep hP hd W₀ hW₀ h0W₀
  refine ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W, hWW₀,
    hsupport, hanalytic, hG, ?_⟩
  intro x hx hxW hzero hregular j
  have hwx : DifferentiableAt ℝ w x := hw.differentiableAt (hΩ.mem_nhds hx)
  have hzx : DifferentiableAt ℝ z x := hz.differentiableAt (hΩ.mem_nhds hx)
  have hcoeffx : ∀ i d, d ∈ (P i).support →
      DifferentiableAt ℝ (coeff i d) (w x) := by
    intro i d hd
    exact (hcoeff i d (w x) (hWW₀ hxW)).differentiableAt
  have hpositive := polynomialFamilyFormalJacobian_sumSquares_pos
    (fun i => (P i).support) coeff w z x hwx hzx hcoeffx hregular
  have hdenominator : MvPolynomial.eval (z x) (dRep (w x)) ≠ 0 := by
    change MvPolynomial.eval (z x)
      (analyticGermJacobianDenominatorRepresentative P coeff (w x)) ≠ 0
    rw [eval_analyticGermJacobianDenominatorRepresentative]
    exact ne_of_gt hpositive
  have hPzero : ∀ i, MvPolynomial.eval (z x) (PRep i (w x)) = 0 := by
    intro i
    exact congrFun hzero i
  exact hvanish (w x) hxW (z x) hPzero hdenominator j

end AbelFormalization
