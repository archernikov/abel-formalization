import AbelFormalization.RestrictedHermiteJetBlockification
import AbelFormalization.RestrictedRankEliminationTraceBoundary
import AbelFormalization.PolynomialGermSymbolMaps

set_option autoImplicit false

/-!
# Rank-generator representatives after Hermite cluster currying

The rank lemma supplies a finite germ-valued generating family `g` and an
actual polynomial-valued analytic representative `G(w)`.  This file proves
that applying the explicit Hermite block substitution and cluster currying to
`G(w)` gives an actual representative of the corresponding transformed germ
generator.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

universe u v w

/-! ## Germs and point-dependent polynomial substitutions -/

/-- Apply a polynomial substitution which may depend pointwise on the germ
parameter.  Eventual equality makes this operation well-defined on germs. -/
def germPointwiseMvPolynomialSubstitutionHom
    {E R σ τ : Type*} [CommSemiring R]
    (l : Filter E) (value : E → σ → MvPolynomial τ R) :
    Germ l (MvPolynomial σ R) →+* Germ l (MvPolynomial τ R) where
  toFun F := Germ.map'
    (fun f x => MvPolynomial.eval₂Hom MvPolynomial.C (value x) (f x))
    (by
      intro f g hfg
      filter_upwards [hfg] with x hx
      rw [hx]) F
  map_zero' := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x => by simp
  map_one' := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x => by simp
  map_add' F G := by
    refine Germ.inductionOn₂ F G ?_
    intro f g
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x => by simp
  map_mul' F G := by
    refine Germ.inductionOn₂ F G ?_
    intro f g
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x => by simp

@[simp]
theorem germPointwiseMvPolynomialSubstitutionHom_coe
    {E R σ τ : Type*} [CommSemiring R]
    (l : Filter E) (value : E → σ → MvPolynomial τ R)
    (F : E → MvPolynomial σ R) :
    germPointwiseMvPolynomialSubstitutionHom l value
        (F : Germ l (MvPolynomial σ R)) =
      ((fun x => MvPolynomial.eval₂Hom MvPolynomial.C
        (value x) (F x)) : Germ l (MvPolynomial τ R)) :=
  rfl

@[simp]
theorem germPointwiseMvPolynomialSubstitutionHom_C_germ
    {E R σ τ : Type*} [CommSemiring R]
    (l : Filter E) (value : E → σ → MvPolynomial τ R)
    (c : Germ l R) :
    germPointwiseMvPolynomialSubstitutionHom l value
        (germMapRingHom l MvPolynomial.C c) =
      germMapRingHom l MvPolynomial.C c := by
  refine Germ.inductionOn c ?_
  intro f
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun x => by simp

/-- Analytic polynomial-valued germs commute with a finite polynomial
substitution when every substituted polynomial has its displayed analytic
representative. -/
theorem analyticPolynomialGermHom_eval₂Hom_of_representatives
    {E σ τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E)
    (value : σ → MvPolynomial τ (AnalyticGermAt x))
    (valueRepresentative : σ → E → MvPolynomial τ ℝ)
    (hvalue : ∀ i, analyticPolynomialGermHom x (value i) =
      (valueRepresentative i : Germ (𝓝 x) (MvPolynomial τ ℝ)))
    (P : MvPolynomial σ (AnalyticGermAt x))
    (F : E → MvPolynomial σ ℝ)
    (hF : analyticPolynomialGermHom x P =
      (F : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    analyticPolynomialGermHom x
        (MvPolynomial.eval₂Hom MvPolynomial.C value P) =
      ((fun y => MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i => valueRepresentative i y) (F y)) :
          Germ (𝓝 x) (MvPolynomial τ ℝ)) := by
  let lhs : MvPolynomial σ (AnalyticGermAt x) →+*
      Germ (𝓝 x) (MvPolynomial τ ℝ) :=
    (analyticPolynomialGermHom (ι := τ) x).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C value)
  let rhs : MvPolynomial σ (AnalyticGermAt x) →+*
      Germ (𝓝 x) (MvPolynomial τ ℝ) :=
    (germPointwiseMvPolynomialSubstitutionHom (𝓝 x)
      (fun y i => valueRepresentative i y)).comp
      (analyticPolynomialGermHom (ι := σ) x)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, analyticPolynomialGermHom, polynomialGermHom]
    · intro i
      simp only [lhs, rhs, RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X']
      change analyticPolynomialGermHom x (value i) =
        germPointwiseMvPolynomialSubstitutionHom (𝓝 x)
          (fun y i => valueRepresentative i y)
          (analyticPolynomialGermHom x (MvPolynomial.X i))
      rw [hvalue i, analyticPolynomialGermHom_X,
        germPointwiseMvPolynomialSubstitutionHom_coe]
      apply Germ.coe_eq.mpr
      exact Eventually.of_forall fun y => by simp
  have h := DFunLike.congr_fun hhom P
  change analyticPolynomialGermHom x
      (MvPolynomial.eval₂Hom MvPolynomial.C value P) =
        germPointwiseMvPolynomialSubstitutionHom (𝓝 x)
          (fun y i => valueRepresentative i y)
          (analyticPolynomialGermHom x P) at h
  rw [hF, germPointwiseMvPolynomialSubstitutionHom_coe] at h
  exact h

/-! ## Analytic-box coefficient specialization -/

/-- Mapping an arbitrary polynomial with analytic-near-box coefficients to
analytic germs is represented by specializing those same coefficients
pointwise. -/
theorem analyticPolynomialGermHom_map_restrictedAnalyticCoefficientGermHom
    {p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    {σ : Type*}
    (P : MvPolynomial σ
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (MvPolynomial.map (restrictedAnalyticCoefficientGermHom D h0D) P) =
      ((fun w => MvPolynomial.map
        (subalgebraPointEval
          (RestrictedBox.analyticNearClosedBoxSubalgebra D) w) P) :
        Germ (𝓝 (0 : RestrictedBoxSpace p)) (MvPolynomial σ ℝ)) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.map_monomial,
        restrictedAnalyticCoefficientGermHom_apply,
        analyticPolynomialGermHom_monomial_of]
      apply Germ.coe_eq.mpr
      exact Eventually.of_forall fun w => by simp [subalgebraPointEval]
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
                  (restrictedAnalyticCoefficientGermHom D h0D) Q) := by simp
        _ = ((fun w => MvPolynomial.map
              (subalgebraPointEval
                (RestrictedBox.analyticNearClosedBoxSubalgebra D) w) P) :
              Germ (𝓝 (0 : RestrictedBoxSpace p)) (MvPolynomial σ ℝ)) +
            ((fun w => MvPolynomial.map
              (subalgebraPointEval
                (RestrictedBox.analyticNearClosedBoxSubalgebra D) w) Q) :
              Germ (𝓝 (0 : RestrictedBoxSpace p)) (MvPolynomial σ ℝ)) := by
          rw [hP, hQ]
        _ = ((fun w => MvPolynomial.map
              (subalgebraPointEval
                (RestrictedBox.analyticNearClosedBoxSubalgebra D) w) (P + Q)) :
              Germ (𝓝 (0 : RestrictedBoxSpace p)) (MvPolynomial σ ℝ)) := by
          apply Germ.coe_eq.mpr
          exact Eventually.of_forall fun w => by simp

/-! ## The real Hermite blockification of a rank representative -/

variable {ι : Type*}

/-- Pointwise real specialization of one explicit Hermite jet polynomial. -/
def paperRankHermiteRealJetPolynomial
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (j : Fin S.card) (z : RestrictedBoxSpace p) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ :=
  MvPolynomial.map
    (subalgebraPointEval
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) z)
    (paperRankHermiteJetPolynomial D representative offset S
      Active Coeff blockEquiv j)

/-- The real specialization is an actual representative of the corresponding
Hermite jet polynomial over analytic germs. -/
theorem analyticPolynomialGermHom_paperRankHermiteGermJetPolynomial
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (j : Fin S.card) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (paperRankHermiteGermJetPolynomial D h0D representative offset S
          Active Coeff blockEquiv j) =
      (paperRankHermiteRealJetPolynomial D representative offset S
        Active Coeff blockEquiv j :
          Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial
              (SplitClusterBlockSymbol Active Coeff
                (paperRankHermiteBlockDerivativeCount S Active)
                (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ)) := by
  exact analyticPolynomialGermHom_map_restrictedAnalyticCoefficientGermHom
    D h0D (paperRankHermiteJetPolynomial D representative offset S
      Active Coeff blockEquiv j)

/-- The germ-valued assignment defining Hermite blockification. -/
def paperRankHermiteGermBlockificationValue
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff) :
    PaperRankRetainedSymbols m S.card →
      MvPolynomial
        (SplitClusterBlockSymbol Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff))
        (RealAnalyticGerm p) :=
  Sum.elim
    (fun i => MvPolynomial.X (Sum.inl (blockEquiv i)))
    (paperRankHermiteGermJetPolynomial D h0D representative offset S
      Active Coeff blockEquiv)

/-- Its literal pointwise real specialization. -/
def paperRankHermiteRealBlockificationValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (z : RestrictedBoxSpace p) :
    PaperRankRetainedSymbols m S.card →
      MvPolynomial
        (SplitClusterBlockSymbol Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ :=
  Sum.elim
    (fun i => MvPolynomial.X (Sum.inl (blockEquiv i)))
    (fun j => paperRankHermiteRealJetPolynomial D representative offset S
      Active Coeff blockEquiv j z)

theorem analyticPolynomialGermHom_paperRankHermiteGermBlockificationValue
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (i : PaperRankRetainedSymbols m S.card) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (paperRankHermiteGermBlockificationValue D h0D representative offset S
          Active Coeff blockEquiv i) =
      ((fun z => paperRankHermiteRealBlockificationValue D representative
          offset S Active Coeff blockEquiv z i) :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (SplitClusterBlockSymbol Active Coeff
              (paperRankHermiteBlockDerivativeCount S Active)
              (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ)) := by
  rcases i with i | j
  · simp [paperRankHermiteGermBlockificationValue,
      paperRankHermiteRealBlockificationValue]
  · exact analyticPolynomialGermHom_paperRankHermiteGermJetPolynomial
      D h0D representative offset S Active Coeff blockEquiv j

/-- Apply the real Hermite blockification pointwise to a rank-generator
representative. -/
def paperRankHermiteRealBlockifiedRepresentative
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (G : RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)
    (z : RestrictedBoxSpace p) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ :=
  paperRankClusterBlockificationHom ℝ Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    blockEquiv
    (fun j => paperRankHermiteRealJetPolynomial D representative offset S
      Active Coeff blockEquiv j z) (G z)

/-- The mapped real rank representative is an actual polynomial-valued
representative of the germ rank generator after Hermite blockification. -/
theorem analyticPolynomialGermHom_paperRankHermiteBlockification_of
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (g : MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RealAnalyticGerm p))
    (G : RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)
    (hG : analyticPolynomialGermHom (0 : RestrictedBoxSpace p) g =
      (G : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (paperRankClusterBlockificationHom (RealAnalyticGerm p)
          Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff)
          blockEquiv
          (paperRankHermiteGermJetPolynomial D h0D representative offset S
            Active Coeff blockEquiv) g) =
      (paperRankHermiteRealBlockifiedRepresentative D representative offset S
        Active Coeff blockEquiv G :
          Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial
              (SplitClusterBlockSymbol Active Coeff
              (paperRankHermiteBlockDerivativeCount S Active)
              (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ)) := by
  change analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (paperRankHermiteGermBlockificationValue D h0D representative offset S
          Active Coeff blockEquiv) g) =
    ((fun z => MvPolynomial.eval₂Hom MvPolynomial.C
      (paperRankHermiteRealBlockificationValue D representative offset S
        Active Coeff blockEquiv z) (G z)) :
      Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial
          (SplitClusterBlockSymbol Active Coeff
            (paperRankHermiteBlockDerivativeCount S Active)
            (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ))
  exact analyticPolynomialGermHom_eval₂Hom_of_representatives
    (0 : RestrictedBoxSpace p)
    (paperRankHermiteGermBlockificationValue D h0D representative offset S
      Active Coeff blockEquiv)
    (fun i z => paperRankHermiteRealBlockificationValue D representative
      offset S Active Coeff blockEquiv z i)
    (analyticPolynomialGermHom_paperRankHermiteGermBlockificationValue
      D h0D representative offset S Active Coeff blockEquiv)
    g G hG

end AbelFormalization
