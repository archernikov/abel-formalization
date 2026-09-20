import AbelFormalization.AnalyticGermNoetherian
import AbelFormalization.JacobianEliminationIdeal
import AbelFormalization.PolynomialGermIdealVanishing
import AbelFormalization.PolynomialGermSymbolMaps

set_option autoImplicit false

/-!
# Finite analytic identities for the Jacobian elimination ideal

This is the algebraic and finite-representative part of analytic elimination.
It retains the explicit nonzero-denominator hypothesis: a separate chain-rule
argument must establish that hypothesis at the regular zeros in the paper.
Every polynomial-valued identity holds on one common neighborhood before
any, potentially unbounded, symbol assignment is chosen.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

variable {Keep γ : Type*} [Finite Keep] [Fintype γ]

/-- The actual contracted Jacobian ideal has finite analytic generator
representatives vanishing, on one neighborhood, at every zero of the chosen
original representatives where the chosen denominator is nonzero.

The derivations are arbitrary actual real derivations of the polynomial
ring over the actual analytic germ ring. No evaluation homomorphism on all
analytic germs at nearby points is assumed or constructed. -/
theorem exists_analyticJacobianElimination (p r a : ℕ)
    (P : Fin (r + a) → MvPolynomial (Fin a ⊕ Keep) (RealAnalyticGerm p))
    (D : γ → Derivation ℝ
      (MvPolynomial (Fin a ⊕ Keep) (RealAnalyticGerm p))
      (MvPolynomial (Fin a ⊕ Keep) (RealAnalyticGerm p)))
    (PRep : Fin (r + a) → (Fin p → ℝ) → MvPolynomial (Fin a ⊕ Keep) ℝ)
    (dRep : (Fin p → ℝ) → MvPolynomial (Fin a ⊕ Keep) ℝ)
    (hP : ∀ i, analyticPolynomialGermHom (0 : Fin p → ℝ) (P i) =
      (PRep i : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial (Fin a ⊕ Keep) ℝ)))
    (hd : analyticPolynomialGermHom (0 : Fin p → ℝ)
        (derivationJacobianDenominator P D) =
      (dRep : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial (Fin a ⊕ Keep) ℝ)))
    (W₀ : Set (Fin p → ℝ)) (hW₀ : IsOpen W₀) (h0W₀ : (0 : Fin p → ℝ) ∈ W₀) :
    ∃ I : Ideal (MvPolynomial Keep (RealAnalyticGerm p)), ∃ c : ℕ,
      ∃ g : Fin c → MvPolynomial Keep (RealAnalyticGerm p),
      ∃ G : Fin c → (Fin p → ℝ) → MvPolynomial Keep ℝ,
      ∃ W : Set (Fin p → ℝ),
        I = jacobianEliminationIdeal a P D ∧
        (r : ℕ∞) ≤ I.height ∧
        Ideal.span (Set.range g) = I ∧
        IsOpen W ∧ (0 : Fin p → ℝ) ∈ W ∧ W ⊆ W₀ ∧
        (∀ j w, (G j w).support ⊆ (g j).support) ∧
        (∀ j e, AnalyticOnNhd ℝ (fun w => (G j w).coeff e) W) ∧
        (∀ j, analyticPolynomialGermHom (0 : Fin p → ℝ) (g j) =
          (G j : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial Keep ℝ))) ∧
        ∀ w ∈ W, ∀ z : (Fin a ⊕ Keep) → ℝ,
          (∀ i, MvPolynomial.eval z (PRep i w) = 0) →
          MvPolynomial.eval z (dRep w) ≠ 0 →
          ∀ j, MvPolynomial.eval (z ∘ Sum.inr) (G j w) = 0 := by
  classical
  let I : Ideal (MvPolynomial Keep (RealAnalyticGerm p)) :=
    jacobianEliminationIdeal a P D
  obtain ⟨c, g, G, V, hg, hVopen, h0V, hsupport, hanalytic, hG⟩ :=
    exists_analyticPolynomial_ideal_generators (0 : Fin p → ℝ) I
      I.fg_of_isNoetherianRing
  let f : Fin (r + a + 1) →
      MvPolynomial (Option (Fin a ⊕ Keep)) (RealAnalyticGerm p) :=
    mvPolynomialUnitAugmentedTuple P (derivationJacobianDenominator P D)
  let F : Fin (r + a + 1) → (Fin p → ℝ) →
      MvPolynomial (Option (Fin a ⊕ Keep)) ℝ :=
    fun i w => mvPolynomialUnitAugmentedTuple (fun j => PRep j w) (dRep w) i
  let gFlat : Fin c → MvPolynomial (Option (Fin a ⊕ Keep)) (RealAnalyticGerm p) :=
    fun j => polynomialEliminationRetainedFlat (RealAnalyticGerm p) Keep (Fin a) (g j)
  let GFlat : Fin c → (Fin p → ℝ) → MvPolynomial (Option (Fin a ⊕ Keep)) ℝ :=
    fun j w => MvPolynomial.rename (fun k : Keep => some (Sum.inr k)) (G j w)
  have hF : ∀ i, analyticPolynomialGermHom (0 : Fin p → ℝ) (f i) =
      (F i : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial (Option (Fin a ⊕ Keep)) ℝ)) := by
    intro i
    simpa only [f, F, mvPolynomialUnitAugmentedTuple] using
      analyticPolynomialGermHom_flatUnitAugmentedTuple (0 : Fin p → ℝ)
        P (derivationJacobianDenominator P D) PRep dRep hP hd i
  have hGFlat : ∀ j, analyticPolynomialGermHom (0 : Fin p → ℝ) (gFlat j) =
      (GFlat j : Germ (𝓝 (0 : Fin p → ℝ))
        (MvPolynomial (Option (Fin a ⊕ Keep)) ℝ)) := by
    intro j
    change analyticPolynomialGermHom (0 : Fin p → ℝ)
        (MvPolynomial.rename (fun k : Keep => some (Sum.inr k)) (g j)) = _
    exact analyticPolynomialGermHom_rename_of (0 : Fin p → ℝ)
      (fun k : Keep => some (Sum.inr k)) (hG j)
  have hmem : ∀ j, gFlat j ∈ Ideal.span (Set.range f) := by
    intro j
    have hgj : g j ∈ I := by
      rw [← hg]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact hgj
  obtain ⟨W, hWopen, h0W, hWV, hvanish⟩ :=
    exists_open_analyticPolynomial_members_vanish (0 : Fin p → ℝ)
      f gFlat F GFlat hF hGFlat hmem (V ∩ W₀) (hVopen.inter hW₀) ⟨h0V, h0W₀⟩
  refine ⟨I, c, g, G, W, rfl, jacobianEliminationIdeal_height a r P D,
    hg, hWopen, h0W, (fun w hw => (hWV hw).2), hsupport, ?_, hG, ?_⟩
  · intro j e w hw
    exact hanalytic j e w (hWV hw).1
  · intro w hw z hz hdz j
    let zInv : ℝ := (MvPolynomial.eval z (dRep w))⁻¹
    let zFull : Option (Fin a ⊕ Keep) → ℝ := fun o => o.elim zInv z
    have haug : ∀ i, MvPolynomial.eval zFull (F i w) = 0 := by
      intro i
      apply mvPolynomialUnitAugmentedTuple_eval_zero (fun k => PRep k w)
        (dRep w) z zInv hz ?_ i
      exact inv_mul_cancel₀ hdz
    have hretained := hvanish w hw zFull haug j
    change MvPolynomial.eval zFull
      (MvPolynomial.rename (fun k : Keep => some (Sum.inr k)) (G j w)) = 0 at hretained
    rw [MvPolynomial.eval_rename] at hretained
    exact hretained

end AbelFormalization
