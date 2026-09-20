import AbelFormalization.RestrictedHermiteJetBlockification

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

universe u v w z

/-- Apply a point-dependent family of ring homomorphisms to a germ. -/
def germPointwiseRingHom
    {E : Type u} {R : Type v} {S : Type w}
    [CommSemiring R] [CommSemiring S]
    (l : Filter E) (f : E → R →+* S) : Germ l R →+* Germ l S where
  toFun g := Germ.map' (fun g x ↦ f x (g x))
    (fun _ _ h ↦ h.mono fun x hx ↦ congrArg (f x) hx) g
  map_zero' := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x ↦ (f x).map_zero
  map_one' := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x ↦ (f x).map_one
  map_add' g h := by
    induction g using Germ.inductionOn with
    | _ g =>
        induction h using Germ.inductionOn with
        | _ h =>
            apply Germ.coe_eq.mpr
            exact Eventually.of_forall fun x ↦ (f x).map_add (g x) (h x)
  map_mul' g h := by
    induction g using Germ.inductionOn with
    | _ g =>
        induction h using Germ.inductionOn with
        | _ h =>
            apply Germ.coe_eq.mpr
            exact Eventually.of_forall fun x ↦ (f x).map_mul (g x) (h x)

@[simp]
theorem germPointwiseRingHom_coe
    {E : Type u} {R : Type v} {S : Type w}
    [CommSemiring R] [CommSemiring S]
    (l : Filter E) (f : E → R →+* S) (g : E → R) :
    germPointwiseRingHom l f (g : Germ l R) =
      ((fun x ↦ f x (g x)) : Germ l S) :=
  rfl

/-- Apply the analytic polynomial-germ map through two nested polynomial
rings. -/
def nestedAnalyticPolynomialGermHom
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Inner : Type w} (x : E) :
    MvPolynomial Outer (MvPolynomial Inner (AnalyticGermAt x)) →+*
      Germ (nhds x) (MvPolynomial Outer (MvPolynomial Inner ℝ)) :=
  (polynomialGermHom (ι := Outer) (R := MvPolynomial Inner ℝ) (nhds x)).comp
    (MvPolynomial.map (analyticPolynomialGermHom (ι := Inner) x))

/-- Pointwise real specialization of a polynomial over the restricted
analytic coefficient algebra. -/
def restrictedAnalyticRealPolynomial
    {p : ℕ} (D : RestrictedBox p) {Symbol : Type v}
    (Q : MvPolynomial Symbol D.analyticNearClosedBoxSubalgebra)
    (w : RestrictedBoxSpace p) : MvPolynomial Symbol ℝ :=
  MvPolynomial.map (subalgebraPointEval D.analyticNearClosedBoxSubalgebra w) Q

/-- The generic-symbol form of
`analyticPolynomialGermHom_restrictedPaperGermPolynomial`. -/
theorem analyticPolynomialGermHom_map_restrictedAnalyticCoefficientGermHom
    {p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    {Symbol : Type v}
    (Q : MvPolynomial Symbol D.analyticNearClosedBoxSubalgebra) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (MvPolynomial.map (restrictedAnalyticCoefficientGermHom D h0D) Q) =
      (restrictedAnalyticRealPolynomial D Q :
        Germ (nhds (0 : RestrictedBoxSpace p))
          (MvPolynomial Symbol ℝ)) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.map_monomial,
        restrictedAnalyticCoefficientGermHom_apply,
        analyticPolynomialGermHom_monomial_of]
      apply Germ.coe_eq.mpr
      exact Eventually.of_forall fun w => by
        simp [restrictedAnalyticRealPolynomial]
  | add P Q hP hQ =>
      calc
        analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
            (MvPolynomial.map
              (restrictedAnalyticCoefficientGermHom D h0D) (P + Q)) =
            analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
                (MvPolynomial.map
                  (restrictedAnalyticCoefficientGermHom D h0D) P) +
              analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
                (MvPolynomial.map
                  (restrictedAnalyticCoefficientGermHom D h0D) Q) := by
          simp
        _ = (restrictedAnalyticRealPolynomial D P :
              Germ (nhds (0 : RestrictedBoxSpace p))
                (MvPolynomial Symbol ℝ)) +
            (restrictedAnalyticRealPolynomial D Q :
              Germ (nhds (0 : RestrictedBoxSpace p))
                (MvPolynomial Symbol ℝ)) := by
          rw [hP, hQ]
        _ = (restrictedAnalyticRealPolynomial D (P + Q) :
              Germ (nhds (0 : RestrictedBoxSpace p))
                (MvPolynomial Symbol ℝ)) := by
          apply Germ.coe_eq.mpr
          exact Eventually.of_forall fun w => by
            simp [restrictedAnalyticRealPolynomial]

/-- The real Hermite jet polynomial obtained by specializing its analytic
offset coefficient at `w`. -/
def paperRankHermiteRealJetPolynomial
    {ι : Type z} {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (w₀ : RestrictedBoxSpace p) (j : Fin S.card) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ :=
  restrictedAnalyticRealPolynomial D
    (paperRankHermiteJetPolynomial D representative offset S
      Active Coeff blockEquiv j) w₀

theorem analyticPolynomialGermHom_paperRankHermiteGermJetPolynomial
    {ι : Type z} {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff) (j : Fin S.card) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (paperRankHermiteGermJetPolynomial D h0D representative offset S
          Active Coeff blockEquiv j) =
      ((fun w₀ => paperRankHermiteRealJetPolynomial D representative offset S
          Active Coeff blockEquiv w₀ j) :
        Germ (nhds (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (SplitClusterBlockSymbol Active Coeff
              (paperRankHermiteBlockDerivativeCount S Active)
              (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ)) := by
  exact analyticPolynomialGermHom_map_restrictedAnalyticCoefficientGermHom
    D h0D (paperRankHermiteJetPolynomial D representative offset S
      Active Coeff blockEquiv j)

/-- Exact compatibility of a chosen rank-polynomial representative with the
flat Hermite blockification. -/
theorem analyticPolynomialGermHom_paperRankHermiteBlockification_of
    {ι : Type z} {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (g : MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RealAnalyticGerm p))
    (G : RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)
    (hG : analyticPolynomialGermHom (0 : RestrictedBoxSpace p) g =
      (G : Germ (nhds (0 : RestrictedBoxSpace p))
        (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (paperRankClusterBlockificationHom (RealAnalyticGerm p)
          Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff)
          blockEquiv
          (paperRankHermiteGermJetPolynomial D h0D representative offset S
            Active Coeff blockEquiv) g) =
      ((fun w₀ =>
          paperRankClusterBlockificationHom ℝ Active Coeff
            (paperRankHermiteBlockDerivativeCount S Active)
            (paperRankHermiteBlockDerivativeCount S Coeff)
            blockEquiv
            (paperRankHermiteRealJetPolynomial D representative offset S
              Active Coeff blockEquiv w₀) (G w₀)) :
        Germ (nhds (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (SplitClusterBlockSymbol Active Coeff
              (paperRankHermiteBlockDerivativeCount S Active)
              (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ)) := by
  let germBlock := paperRankClusterBlockificationHom (RealAnalyticGerm p)
    Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    blockEquiv
    (paperRankHermiteGermJetPolynomial D h0D representative offset S
      Active Coeff blockEquiv)
  let realBlock : RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ →+*
        MvPolynomial
          (SplitClusterBlockSymbol Active Coeff
            (paperRankHermiteBlockDerivativeCount S Active)
            (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ :=
    fun w₀ =>
      (paperRankClusterBlockificationHom ℝ Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)
        blockEquiv
        (paperRankHermiteRealJetPolynomial D representative offset S
          Active Coeff blockEquiv w₀)).toRingHom
  let pointwise := germPointwiseRingHom
    (nhds (0 : RestrictedBoxSpace p)) realBlock
  have hhom :
      (analyticPolynomialGermHom (0 : RestrictedBoxSpace p)).comp
          germBlock.toRingHom =
        pointwise.comp
          (analyticPolynomialGermHom (0 : RestrictedBoxSpace p)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [germBlock, realBlock, pointwise,
        paperRankClusterBlockificationHom,
        analyticPolynomialGermHom, polynomialGermHom]
    · rintro (i | j)
      · simp [germBlock, realBlock, pointwise,
          paperRankClusterBlockificationHom]
      · simp only [RingHom.comp_apply,
          paperRankClusterBlockificationHom_X_jet]
        change analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
            (paperRankHermiteGermJetPolynomial D h0D representative offset S
              Active Coeff blockEquiv j) = _
        rw [analyticPolynomialGermHom_paperRankHermiteGermJetPolynomial]
        rfl
  calc
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (germBlock g) =
        pointwise (analyticPolynomialGermHom
          (0 : RestrictedBoxSpace p) g) :=
      DFunLike.congr_fun hhom g
    _ = pointwise (G : Germ (nhds (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)) := by
      rw [hG]
    _ = _ := rfl

end AbelFormalization
