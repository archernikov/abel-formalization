import AbelFormalization.FiniteAnalyticNestedChangeOfGenerators
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeTail
import AbelFormalization.TerminalGlobalParameterDeformation

/-!
# Coefficientwise evaluation of finite nested analytic representatives

A simultaneous central-transfer source is a polynomial whose coefficients are
themselves polynomials over analytic germs.  Quantitative transfer evaluates
only the finitely many outer coefficients in the support of that source,
whereas `FiniteAnalyticNestedChangeOfGeneratorsData` chooses a representative
of the flattened whole polynomial.  This module proves that the two numeric
evaluations agree eventually along every parameter tending to the germ base
point.

The proof reconstructs the nested polynomial from its literal outer support.
Equality is established as a polynomial-valued germ before any values are
assigned to either family of symbols, so the symbol values may be unbounded.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v w s q

/-! ## Generic flattened representative comparison -/

/-- Flattening a nested monomial separates its outer monomial from its inner
coefficient polynomial. -/
theorem nestedMvPolynomialFlattening_monomial
    {R : Type u} [CommSemiring R]
    {Outer : Type v} {Coeff : Type w}
    (e : Outer →₀ ℕ) (Q : MvPolynomial Coeff R) :
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
        (MvPolynomial.monomial e Q) =
      MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff)
          (MvPolynomial.monomial e 1) *
        MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff) Q := by
  apply (MvPolynomial.sumAlgEquiv R Outer Coeff).injective
  have hinl :
      (MvPolynomial.sumAlgEquiv R Outer Coeff)
          (MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff)
            (MvPolynomial.monomial e 1)) =
        MvPolynomial.monomial e (1 : MvPolynomial Coeff R) := by
    change (((MvPolynomial.sumAlgEquiv R Outer Coeff).toAlgHom.comp
      (MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff)))
        (MvPolynomial.monomial e 1)) = _
    rw [MvPolynomial.sumAlgEquiv_comp_rename_inl]
    simp
  have hinr :
      (MvPolynomial.sumAlgEquiv R Outer Coeff)
          (MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff) Q) =
        MvPolynomial.C Q := by
    change (((MvPolynomial.sumAlgEquiv R Outer Coeff).toAlgHom.comp
      (MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff))) Q) = _
    rw [MvPolynomial.sumAlgEquiv_comp_rename_inr]
    rfl
  simp only [nestedMvPolynomialFlatteningAlgEquiv,
    AlgEquiv.apply_symm_apply, map_mul, hinl, hinr]
  rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/-- Flattening the outer support expansion gives a finite sum in which each
inner coefficient polynomial is visibly separated from the outer monomial. -/
theorem nestedMvPolynomialFlattening_eq_support_sum
    {R : Type u} [CommSemiring R]
    {Outer : Type v} {Coeff : Type w}
    (P : MvPolynomial Outer (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff P =
      ∑ e ∈ P.support,
        MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff)
            (MvPolynomial.monomial e 1) *
          MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff)
            (P.coeff e) := by
  calc
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff P =
        nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
          (∑ e ∈ P.support, MvPolynomial.monomial e (P.coeff e)) := by
      rw [MvPolynomial.support_sum_monomial_coeff]
    _ = ∑ e ∈ P.support,
        nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
          (MvPolynomial.monomial e (P.coeff e)) := by
      simp only [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      exact nestedMvPolynomialFlattening_monomial e (P.coeff e)

/-! ## A coefficientwise central initial polynomial -/

/-- The fixed central polynomial contributed by one normalized source
monomial.  Its coefficient is one; arbitrary source-coefficient values are
inserted only after the least-weight support has been selected. -/
def centralInitialMonomialBasis
    {R : Type u} [CommRing R] {h : ℕ}
    (d : Fin h → ℕ)
    (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) :
    CentralPolynomial R (Fin h) d (Fin h) :=
  centralPolynomialPhi R (Fin h) d (Fin h)
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (Sum.elim (fun _ : Fin h ↦ (1 : MvPolynomial
        (CentralPolynomialIndex (Fin h) d (Fin h)) R)) MvPolynomial.X)
      (MvPolynomial.monomial e 1))

/-- The literal least-weight subset of the support of a central-transfer
source. -/
def centralLeastWeightSupport
    {R : Type u} [CommRing R] {h : ℕ}
    (d : Fin h → ℕ)
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d) R) :=
  P.support.filter fun e ↦
    Finsupp.weight (fun z ↦ toLex
      (centralLaurentWeight (centralTransferShear d) z)) e =
        lexicographicMinimumWeight
          (centralLaurentWeight (centralTransferShear d)) P

/-- Rebuild the canonical central polynomial from arbitrary values assigned
to the finitely many coefficients in the source support. -/
def coefficientwiseCentralPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {h : ℕ}
    (d : Fin h → ℕ)
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d) R)
    (coefficient :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) → S) :
    CentralPolynomial S (Fin h) d (Fin h) :=
  ∑ e ∈ centralLeastWeightSupport d P,
    MvPolynomial.C (coefficient e) * centralInitialMonomialBasis d e

/-- Evaluation of one fixed central monomial basis is the corresponding
normalized source monomial evaluated at the explicit `Phi` source values. -/
theorem eval₂Hom_centralInitialMonomialBasis
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {h : ℕ}
    (c : R →+* S) (d : Fin h → ℕ)
    (z : CentralPolynomialIndex (Fin h) d (Fin h) → S)
    (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) :
    MvPolynomial.eval₂Hom c z (centralInitialMonomialBasis d e) =
      e.prod fun i n ↦ centralTransferPhiSourceValue c z i ^ n := by
  have hcomp :
      (MvPolynomial.eval₂Hom c (centralTransferPhiValue c z)).comp
          (MvPolynomial.eval₂Hom MvPolynomial.C
            (Sum.elim (fun _ : Fin h ↦ (1 : MvPolynomial
              (CentralPolynomialIndex (Fin h) d (Fin h)) R))
              MvPolynomial.X)) =
        MvPolynomial.eval₂Hom c (centralTransferPhiSourceValue c z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      cases i <;> simp [centralTransferPhiSourceValue]
  unfold centralInitialMonomialBasis
  rw [eval₂Hom_centralPolynomialPhi]
  change (((MvPolynomial.eval₂Hom c
    (centralTransferPhiValue c z)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim (fun _ : Fin h ↦ (1 : MvPolynomial
          (CentralPolynomialIndex (Fin h) d (Fin h)) R))
          MvPolynomial.X))) (MvPolynomial.monomial e 1)) = _
  rw [hcomp, MvPolynomial.eval₂Hom_monomial]
  simp

/-- The finite central polynomial evaluates exactly as the coefficientwise
least-weight sum, without requiring the coefficient values to form a ring
homomorphism. -/
theorem eval₂Hom_coefficientwiseCentralPolynomial
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] {h : ℕ}
    (c : S →+* T) (d : Fin h → ℕ)
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d) R)
    (coefficient :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) → S)
    (z : CentralPolynomialIndex (Fin h) d (Fin h) → T) :
    MvPolynomial.eval₂Hom c z
        (coefficientwiseCentralPolynomial d P coefficient) =
      finiteSupportInitialEvaluation
        (centralLaurentWeight (centralTransferShear d)) P
        (fun e ↦ c (coefficient e))
        (centralTransferPhiSourceValue c z) := by
  unfold coefficientwiseCentralPolynomial finiteSupportInitialEvaluation
    centralLeastWeightSupport
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [map_mul, MvPolynomial.eval₂Hom_C,
    eval₂Hom_centralInitialMonomialBasis]

/-- The canonical normalized central polynomial is the preceding finite
coefficientwise construction with its actual source coefficients. -/
theorem centralPolynomialPhi_normalized_eq_coefficientwiseCentralPolynomial
    {R : Type u} [CommRing R] {h : ℕ}
    (d : Fin h → ℕ)
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d) R) :
    centralPolynomialPhi R (Fin h) d (Fin h)
        (centralNormalizedInitialPolynomial (centralTransferShear d) P) =
      coefficientwiseCentralPolynomial d P P.coeff := by
  classical
  have hinitial :
      lexicographicInitialForm
          (centralLaurentWeight (centralTransferShear d)) P =
        ∑ e ∈ centralLeastWeightSupport d P,
          MvPolynomial.monomial e (P.coeff e) := by
    calc
      lexicographicInitialForm
          (centralLaurentWeight (centralTransferShear d)) P =
          ∑ e ∈ (lexicographicInitialForm
            (centralLaurentWeight (centralTransferShear d)) P).support,
              MvPolynomial.monomial e
                ((lexicographicInitialForm
                  (centralLaurentWeight (centralTransferShear d)) P).coeff e) :=
        (MvPolynomial.support_sum_monomial_coeff _).symm
      _ = _ := by
        rw [lexicographicInitialForm_support]
        unfold centralLeastWeightSupport
        apply Finset.sum_congr rfl
        intro e he
        rw [lexicographicInitialForm_coeff]
        exact congrArg (MvPolynomial.monomial e) (if_pos
          (Finset.mem_filter.mp he).2)
  unfold centralNormalizedInitialPolynomial coefficientwiseCentralPolynomial
  rw [hinitial, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _he
  unfold centralInitialMonomialBasis
  simp only [MvPolynomial.eval₂Hom_monomial, map_mul,
    centralPolynomialPhi_C, map_one]
  simp only [one_mul]

/-- `Phi` commutes with an arbitrary map of coefficient rings. -/
theorem map_centralPolynomialPhi
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {Block : Type w} {Time : Type q} {d : Block → ℕ}
    (f : R →+* S) (P : CentralPolynomial R Block d Time) :
    MvPolynomial.map f (centralPolynomialPhi R Block d Time P) =
      centralPolynomialPhi S Block d Time (MvPolynomial.map f P) := by
  let lhs : CentralPolynomial R Block d Time →+*
      CentralPolynomial S Block d Time :=
    (MvPolynomial.map f).comp
      (centralPolynomialPhi R Block d Time).toRingHom
  let rhs : CentralPolynomial R Block d Time →+*
      CentralPolynomial S Block d Time :=
    (centralPolynomialPhi S Block d Time).toRingHom.comp
      (MvPolynomial.map f)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs]
    · intro z
      cases z with
      | inl z =>
          rcases z with ⟨b, i⟩
          simp [lhs, rhs, centralPolynomialPhi_X_block]
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hji : j ≤ i <;> simp [hji]
      | inr t =>
          simp [lhs, rhs, centralPolynomialPhi_X_time]
  exact RingHom.congr_fun hhom P

/-- The fixed monomial basis is natural in its coefficient ring. -/
theorem map_centralInitialMonomialBasis
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {h : ℕ}
    (f : R →+* S) (d : Fin h → ℕ)
    (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) :
    MvPolynomial.map f (centralInitialMonomialBasis (R := R) d e) =
      centralInitialMonomialBasis (R := S) d e := by
  unfold centralInitialMonomialBasis
  rw [map_centralPolynomialPhi]
  congr 1
  simp [MvPolynomial.eval₂Hom_monomial]

/-- Put the q-free central basis back into the full source variables and
then into the left side of a flattened nested polynomial. -/
def flattenedCentralMonomialBasis
    (R : Type u) [CommRing R] (Coeff : Type v) {h : ℕ}
    (d : Fin h → ℕ)
    (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) :
    MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) R :=
  MvPolynomial.rename Sum.inl
    (MvPolynomial.rename Sum.inr
      (centralInitialMonomialBasis (R := R) d e))

/-- The flattened q-free basis is likewise natural in coefficients. -/
theorem map_flattenedCentralMonomialBasis
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (Coeff : Type w) {h : ℕ} (f : R →+* S) (d : Fin h → ℕ)
    (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) :
    MvPolynomial.map f (flattenedCentralMonomialBasis R Coeff d e) =
      flattenedCentralMonomialBasis S Coeff d e := by
  unfold flattenedCentralMonomialBasis
  rw [MvPolynomial.map_rename, MvPolynomial.map_rename,
    map_centralInitialMonomialBasis]

/-- Constant real polynomials are constant polynomial-valued
representatives after passing to analytic germs. -/
theorem analyticPolynomialGermHom_map_algebraMap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type v} (x : E) (P : MvPolynomial I ℝ) :
    analyticPolynomialGermHom x
        (MvPolynomial.map (algebraMap ℝ (AnalyticGermAt x)) P) =
      ((fun _ : E ↦ P) : Germ (𝓝 x) (MvPolynomial I ℝ)) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      rw [MvPolynomial.map_monomial, analyticGerm_algebraMap]
      exact analyticPolynomialGermHom_monomial_of x e
        (fun _ : E ↦ a) analyticAt_const
  | add P Q hP hQ =>
      rw [map_add, map_add, hP, hQ]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Flattening a constant nested coefficient places it in the right
summand. -/
theorem nestedMvPolynomialFlattening_C
    {R : Type u} [CommSemiring R]
    {Outer : Type v} {Coeff : Type w}
    (Q : MvPolynomial Coeff R) :
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff (MvPolynomial.C Q) =
      MvPolynomial.rename Sum.inr Q := by
  apply (MvPolynomial.sumAlgEquiv R Outer Coeff).injective
  simp only [nestedMvPolynomialFlatteningAlgEquiv,
    AlgEquiv.apply_symm_apply]
  change MvPolynomial.C Q =
    (((MvPolynomial.sumAlgEquiv R Outer Coeff).toAlgHom.comp
      (MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff))) Q)
  rw [MvPolynomial.sumAlgEquiv_comp_rename_inr]
  rfl

/-- Flattening a polynomial whose coefficients were inserted as constants
places all its variables in the left summand. -/
theorem nestedMvPolynomialFlattening_map_C
    {R : Type u} [CommSemiring R]
    {Outer : Type v} {Coeff : Type w}
    (P : MvPolynomial Outer R) :
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
        (MvPolynomial.map MvPolynomial.C P) =
      MvPolynomial.rename Sum.inl P := by
  apply (MvPolynomial.sumAlgEquiv R Outer Coeff).injective
  simp only [nestedMvPolynomialFlatteningAlgEquiv,
    AlgEquiv.apply_symm_apply]
  change MvPolynomial.map MvPolynomial.C P =
    (((MvPolynomial.sumAlgEquiv R Outer Coeff).toAlgHom.comp
      (MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff))) P)
  rw [MvPolynomial.sumAlgEquiv_comp_rename_inl]
  rfl

/-- The flattened canonical central generator is a finite sum of supported
source coefficients times fixed q-free real bases. -/
theorem flattenedCentralGenerator_eq_support_sum
    {R : Type u} [CommRing R] {Coeff : Type v} {h : ℕ}
    (d : Fin h → ℕ)
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d)
      (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R
        (ClusterOperationSymbol (Fin h) d) Coeff
        (MvPolynomial.rename Sum.inr
          (centralPolynomialPhi (MvPolynomial Coeff R) (Fin h) d (Fin h)
            (centralNormalizedInitialPolynomial
              (centralTransferShear d) P))) =
      ∑ e ∈ centralLeastWeightSupport d P,
        MvPolynomial.rename Sum.inr (P.coeff e) *
          flattenedCentralMonomialBasis R Coeff d e := by
  rw [centralPolynomialPhi_normalized_eq_coefficientwiseCentralPolynomial]
  unfold coefficientwiseCentralPolynomial flattenedCentralMonomialBasis
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [map_mul, map_mul, MvPolynomial.rename_C,
    nestedMvPolynomialFlattening_C]
  have hb := map_centralInitialMonomialBasis
    (MvPolynomial.C : R →+* MvPolynomial Coeff R) d e
  rw [← hb, ← MvPolynomial.map_rename,
    nestedMvPolynomialFlattening_map_C]


/-- Evaluate a chosen representative of an outer coefficient, extending it
by zero away from the finite support of the nested polynomial. -/
def nestedSupportedCoefficientValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Coeff : Type w} {x : E}
    (P : MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x)))
    (representative : (e : Outer →₀ ℕ) → e ∈ P.support →
      E → MvPolynomial Coeff ℝ)
    {X : Type q} (parameter : X → E)
    (coefficientValue : Coeff → X → ℝ)
    (e : Outer →₀ ℕ) (n : X) : ℝ := by
  classical
  exact
    if he : e ∈ P.support then
      MvPolynomial.eval (fun z ↦ coefficientValue z n)
        (representative e he (parameter n))
    else 0

/-- A q-free flattened central basis may be evaluated at any assignment of
the full source symbols.  Only its restriction to the central summand is
relevant. -/
theorem eval_flattenedCentralMonomialBasis_of_central
    {Coeff : Type v} {h : ℕ} (A : ℝ → ℝ) (d : Fin h → ℕ)
    (u : Fin h → ℝ)
    (outerValue : ClusterOperationSymbol (Fin h) d → ℝ)
    (coefficientValue : Coeff → ℝ)
    (hcentral : ∀ z, outerValue (Sum.inr z) =
      realCentralTransferCentralValue A u d z)
    (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) :
    MvPolynomial.eval (Sum.elim outerValue coefficientValue)
        (flattenedCentralMonomialBasis ℝ Coeff d e) =
      e.prod fun z n ↦ realCentralTransferMainValue A u d z ^ n := by
  have hb := eval₂Hom_centralInitialMonomialBasis
    (RingHom.id ℝ) d (realCentralTransferCentralValue A u d) e
  rw [realCentralTransferMainValue_eq_phiSourceValue
    (R := ℝ) (RingHom.id ℝ) A u d]
  simp only [flattenedCentralMonomialBasis, MvPolynomial.eval_rename,
    Function.comp_apply, Sum.elim_inl]
  have hvalue :
      ((Sum.elim outerValue coefficientValue ∘ Sum.inl) ∘ Sum.inr) =
        realCentralTransferCentralValue A u d := by
    funext z
    exact hcentral z
  rw [hvalue]
  exact hb

/-- Any analytic representative of a flattened canonical central generator
agrees eventually with the coefficientwise least-weight value obtained from
representatives of the original source coefficients.  The outer assignment
is arbitrary on q variables and is constrained only on the q-free central
summand. -/
theorem eventually_flattenedCentralRepresentativeEvaluation_eq_coefficientwise
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Coeff : Type v} {x : E} {h : ℕ}
    (A : ℝ → ℝ) (d : Fin h → ℕ)
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d)
      (MvPolynomial Coeff (AnalyticGermAt x)))
    (representative : E →
      MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) ℝ)
    (hrepresentative :
      analyticPolynomialGermHom x
          (nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
            (ClusterOperationSymbol (Fin h) d) Coeff
            (MvPolynomial.rename Sum.inr
              (centralPolynomialPhi
                (MvPolynomial Coeff (AnalyticGermAt x))
                (Fin h) d (Fin h)
                (centralNormalizedInitialPolynomial
                  (centralTransferShear d) P)))) =
        (representative : Germ (𝓝 x)
          (MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) ℝ)))
    (coefficientRepresentative :
      (e : ClusterOperationSymbol (Fin h) d →₀ ℕ) →
        e ∈ P.support → E → MvPolynomial Coeff ℝ)
    (hcoefficientRepresentative :
      ∀ e (he : e ∈ P.support),
        analyticPolynomialGermHom x (P.coeff e) =
          (coefficientRepresentative e he :
            Germ (𝓝 x) (MvPolynomial Coeff ℝ)))
    {l : Filter ℕ}
    (parameter : ℕ → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : ClusterOperationSymbol (Fin h) d → ℕ → ℝ)
    (coefficientValue : Coeff → ℕ → ℝ)
    (u : Fin h → ℕ → ℝ)
    (hcentral : ∀ n z, outerValue (Sum.inr z) n =
      realCentralTransferCentralValue A (fun i ↦ u i n) d z) :
    ∀ᶠ n in l,
      MvPolynomial.eval
          (Sum.elim (fun z ↦ outerValue z n)
            (fun z ↦ coefficientValue z n))
          (representative (parameter n)) =
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
          A d
          (fun e n ↦ nestedSupportedCoefficientValue P
            coefficientRepresentative parameter coefficientValue e n)
          u P n := by
  classical
  let coefficientPolynomial :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) →
        MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff)
          (AnalyticGermAt x) := fun e ↦
    MvPolynomial.rename Sum.inr (P.coeff e)
  let basisPolynomial :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) →
        MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff)
          (AnalyticGermAt x) := fun e ↦
    flattenedCentralMonomialBasis (AnalyticGermAt x) Coeff d e
  let coefficientRepresentative' :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) → E →
        MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) ℝ :=
    fun e y ↦ if he : e ∈ P.support then
      MvPolynomial.rename Sum.inr (coefficientRepresentative e he y)
    else 0
  let basisRepresentative :
      (ClusterOperationSymbol (Fin h) d →₀ ℕ) → E →
        MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) ℝ :=
    fun e _ ↦ flattenedCentralMonomialBasis ℝ Coeff d e
  have hcoefficient : ∀ e ∈ centralLeastWeightSupport d P,
      analyticPolynomialGermHom x (coefficientPolynomial e) =
        (coefficientRepresentative' e : Germ (𝓝 x)
          (MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) ℝ)) := by
    intro e he
    have heP : e ∈ P.support := (Finset.mem_filter.mp he).1
    have hrename := analyticPolynomialGermHom_rename_of x
      (Sum.inr : Coeff → ClusterOperationSymbol (Fin h) d ⊕ Coeff)
      (hcoefficientRepresentative e heP)
    simpa only [coefficientPolynomial, coefficientRepresentative',
      dif_pos heP] using hrename
  have hbasis : ∀ e ∈ centralLeastWeightSupport d P,
      analyticPolynomialGermHom x (basisPolynomial e) =
        (basisRepresentative e : Germ (𝓝 x)
          (MvPolynomial (ClusterOperationSymbol (Fin h) d ⊕ Coeff) ℝ)) := by
    intro e _he
    rw [show basisPolynomial e =
        flattenedCentralMonomialBasis (AnalyticGermAt x) Coeff d e by rfl]
    rw [← map_flattenedCentralMonomialBasis Coeff
      (algebraMap ℝ (AnalyticGermAt x)) d e]
    simpa only [basisRepresentative] using
      analyticPolynomialGermHom_map_algebraMap x
        (flattenedCentralMonomialBasis ℝ Coeff d e)
  have hpoly := analyticPolynomialIdentity_eventually x
    (centralLeastWeightSupport d P)
    (nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
      (ClusterOperationSymbol (Fin h) d) Coeff
      (MvPolynomial.rename Sum.inr
        (centralPolynomialPhi (MvPolynomial Coeff (AnalyticGermAt x))
          (Fin h) d (Fin h)
          (centralNormalizedInitialPolynomial (centralTransferShear d) P))))
    coefficientPolynomial basisPolynomial representative
    coefficientRepresentative' basisRepresentative hrepresentative
    hcoefficient hbasis (flattenedCentralGenerator_eq_support_sum d P)
  have hpulled : ∀ᶠ n in l,
      representative (parameter n) =
        ∑ e ∈ centralLeastWeightSupport d P,
          coefficientRepresentative' e (parameter n) *
            basisRepresentative e (parameter n) :=
    hparameter.eventually hpoly
  filter_upwards [hpulled] with n hn
  rw [hn]
  unfold ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
    finiteSupportInitialEvaluation centralLeastWeightSupport
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro e he
  have heP : e ∈ P.support := (Finset.mem_filter.mp he).1
  rw [show coefficientRepresentative' e (parameter n) =
      MvPolynomial.rename Sum.inr
        (coefficientRepresentative e heP (parameter n)) by
      simp only [coefficientRepresentative', dif_pos heP]]
  simp only [MvPolynomial.eval_rename, Function.comp_apply, Sum.elim_inr,
    basisRepresentative, nestedSupportedCoefficientValue, dif_pos heP]
  rw [eval_flattenedCentralMonomialBasis_of_central A d
    (fun i ↦ u i n) (fun z ↦ outerValue z n)
    (fun z ↦ coefficientValue z n) (hcentral n) e]
  rfl

/-- A flattened analytic representative evaluates eventually as the
support-local coefficientwise evaluation determined by any representatives
of its actual outer coefficients. -/
theorem eventually_flattenedRepresentativeEvaluation_eq_coefficientwise
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Coeff : Type w} {x : E}
    (P : MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x)))
    (representative : E → MvPolynomial (Outer ⊕ Coeff) ℝ)
    (hrepresentative :
      analyticPolynomialGermHom x
          (nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
            Outer Coeff P) =
        (representative : Germ (𝓝 x) (MvPolynomial (Outer ⊕ Coeff) ℝ)))
    (coefficientRepresentative : (e : Outer →₀ ℕ) →
      e ∈ P.support → E → MvPolynomial Coeff ℝ)
    (hcoefficientRepresentative : ∀ e (he : e ∈ P.support),
      analyticPolynomialGermHom x (P.coeff e) =
        (coefficientRepresentative e he :
          Germ (𝓝 x) (MvPolynomial Coeff ℝ)))
    {X : Type q} {l : Filter X}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : Outer → X → ℝ)
    (coefficientValue : Coeff → X → ℝ) :
    ∀ᶠ n in l,
      MvPolynomial.eval (Sum.elim (fun i ↦ outerValue i n)
          (fun z ↦ coefficientValue z n)) (representative (parameter n)) =
        finiteSupportPolynomialEvaluation P
          (fun e ↦ nestedSupportedCoefficientValue P
            coefficientRepresentative parameter coefficientValue e n)
          (fun i ↦ outerValue i n) := by
  classical
  let outerPolynomial : (Outer →₀ ℕ) →
      MvPolynomial (Outer ⊕ Coeff) (AnalyticGermAt x) := fun e ↦
    MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff)
      (MvPolynomial.monomial e 1)
  let coefficientPolynomial : (Outer →₀ ℕ) →
      MvPolynomial (Outer ⊕ Coeff) (AnalyticGermAt x) := fun e ↦
    MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff) (P.coeff e)
  let outerRepresentative : (Outer →₀ ℕ) → E →
      MvPolynomial (Outer ⊕ Coeff) ℝ := fun e _ ↦
    MvPolynomial.rename (Sum.inl : Outer → Outer ⊕ Coeff)
      (MvPolynomial.monomial e 1)
  let coefficientRepresentative' : (Outer →₀ ℕ) → E →
      MvPolynomial (Outer ⊕ Coeff) ℝ := fun e y ↦
    if he : e ∈ P.support then
      MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff)
        (coefficientRepresentative e he y)
    else 0
  have houter : ∀ e ∈ P.support,
      analyticPolynomialGermHom x (outerPolynomial e) =
        (outerRepresentative e :
          Germ (𝓝 x) (MvPolynomial (Outer ⊕ Coeff) ℝ)) := by
    intro e _he
    have hone : (1 : AnalyticGermAt x) =
        analyticGermOf (fun _ : E ↦ (1 : ℝ)) analyticAt_const := by
      simpa only [map_one] using analyticGerm_algebraMap x 1
    have hmono := analyticPolynomialGermHom_monomial_of x e
      (fun _ : E ↦ (1 : ℝ)) analyticAt_const
    have hmono' : analyticPolynomialGermHom x
          (MvPolynomial.monomial e (1 : AnalyticGermAt x)) =
        ((fun _ : E ↦ MvPolynomial.monomial e (1 : ℝ)) :
          Germ (𝓝 x) (MvPolynomial Outer ℝ)) := by
      rw [hone]
      exact hmono
    have hrename := analyticPolynomialGermHom_rename_of x
      (Sum.inl : Outer → Outer ⊕ Coeff) hmono'
    simpa only [outerPolynomial, outerRepresentative] using hrename
  have hcoefficient : ∀ e ∈ P.support,
      analyticPolynomialGermHom x (coefficientPolynomial e) =
        (coefficientRepresentative' e :
          Germ (𝓝 x) (MvPolynomial (Outer ⊕ Coeff) ℝ)) := by
    intro e he
    rw [show coefficientPolynomial e =
        MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff)
          (P.coeff e) by rfl]
    rw [analyticPolynomialGermHom_rename,
      hcoefficientRepresentative e he]
    change germMapRingHom (𝓝 x)
        (MvPolynomial.rename
          (Sum.inr : Coeff → Outer ⊕ Coeff)).toRingHom
          (coefficientRepresentative e he :
            Germ (𝓝 x) (MvPolynomial Coeff ℝ)) = _
    rw [germMapRingHom_coe]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun y ↦ by
      simp only [coefficientRepresentative', dif_pos he]
      change MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff)
          (coefficientRepresentative e he y) = _
      rfl
  have hpoly := analyticPolynomialIdentity_eventually x P.support
    (nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x) Outer Coeff P)
    outerPolynomial coefficientPolynomial representative outerRepresentative
    coefficientRepresentative' hrepresentative houter hcoefficient
    (nestedMvPolynomialFlattening_eq_support_sum P)
  have hpulled : ∀ᶠ n in l,
      representative (parameter n) =
        ∑ e ∈ P.support,
          outerRepresentative e (parameter n) *
            coefficientRepresentative' e (parameter n) :=
    hparameter.eventually hpoly
  filter_upwards [hpulled] with n hn
  rw [hn]
  simp only [map_sum, map_mul, finiteSupportPolynomialEvaluation]
  apply Finset.sum_congr rfl
  intro e he
  rw [show coefficientRepresentative' e (parameter n) =
      MvPolynomial.rename (Sum.inr : Coeff → Outer ⊕ Coeff)
        (coefficientRepresentative e he (parameter n)) by
      simp only [coefficientRepresentative', dif_pos he]]
  simp only [outerRepresentative, MvPolynomial.eval_rename,
    MvPolynomial.eval_monomial, map_one, one_mul,
    nestedSupportedCoefficientValue, dif_pos he, Function.comp_apply,
    Sum.elim_inl, Sum.elim_inr]
  rw [show
    (Sum.elim (fun i ↦ outerValue i n) (fun z ↦ coefficientValue z n) ∘
      Sum.inr) = (fun z ↦ coefficientValue z n) by
    funext z
    rfl]
  rw [mul_comm]

/-! ## Direct wrappers for finite nested changes -/

/-- Source-value form of the generic comparison theorem. -/
theorem FiniteAnalyticNestedChangeOfGeneratorsData.eventually_sourceValue_eq_coefficientwise
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Coeff : Type w}
    {Source : Type s} {Target : Type q}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
    {target : Target →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    (a : Source)
    (coefficientRepresentative : (e : Outer →₀ ℕ) →
      e ∈ (source a).support → E → MvPolynomial Coeff ℝ)
    (hcoefficientRepresentative : ∀ e (he : e ∈ (source a).support),
      analyticPolynomialGermHom x ((source a).coeff e) =
        (coefficientRepresentative e he :
          Germ (𝓝 x) (MvPolynomial Coeff ℝ)))
    {X : Type q} {l : Filter X}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : Outer → X → ℝ)
    (coefficientValue : Coeff → X → ℝ) :
    ∀ᶠ n in l,
      data.sourceValue parameter outerValue coefficientValue a n =
        finiteSupportPolynomialEvaluation (source a)
          (fun e ↦ nestedSupportedCoefficientValue (source a)
            coefficientRepresentative parameter coefficientValue e n)
          (fun i ↦ outerValue i n) := by
  have h := eventually_flattenedRepresentativeEvaluation_eq_coefficientwise
    (source a) (data.sourceRepresentative a) (data.source_germ_eq a)
    coefficientRepresentative hcoefficientRepresentative parameter hparameter
    outerValue coefficientValue
  filter_upwards [h] with n hn
  change MvPolynomial.eval
      (fun i ↦ Sum.elim outerValue coefficientValue i n)
      (data.sourceRepresentative a (parameter n)) = _
  rw [show (fun i ↦ Sum.elim outerValue coefficientValue i n) =
      Sum.elim (fun i ↦ outerValue i n) (fun z ↦ coefficientValue z n) by
    funext i
    cases i <;> rfl]
  exact hn

/-- Target-value form, used when the canonical transfer sources are the
target family of a displayed-source change of generators. -/
theorem FiniteAnalyticNestedChangeOfGeneratorsData.eventually_targetValue_eq_coefficientwise
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Coeff : Type w}
    {Source : Type s} {Target : Type q}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
    {target : Target →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    (b : Target)
    (coefficientRepresentative : (e : Outer →₀ ℕ) →
      e ∈ (target b).support → E → MvPolynomial Coeff ℝ)
    (hcoefficientRepresentative : ∀ e (he : e ∈ (target b).support),
      analyticPolynomialGermHom x ((target b).coeff e) =
        (coefficientRepresentative e he :
          Germ (𝓝 x) (MvPolynomial Coeff ℝ)))
    {X : Type q} {l : Filter X}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : Outer → X → ℝ)
    (coefficientValue : Coeff → X → ℝ) :
    ∀ᶠ n in l,
      data.targetValue parameter outerValue coefficientValue b n =
        finiteSupportPolynomialEvaluation (target b)
          (fun e ↦ nestedSupportedCoefficientValue (target b)
            coefficientRepresentative parameter coefficientValue e n)
          (fun i ↦ outerValue i n) := by
  have h := eventually_flattenedRepresentativeEvaluation_eq_coefficientwise
    (target b) (data.targetRepresentative b) (data.target_germ_eq b)
    coefficientRepresentative hcoefficientRepresentative parameter hparameter
    outerValue coefficientValue
  filter_upwards [h] with n hn
  change MvPolynomial.eval
      (fun i ↦ Sum.elim outerValue coefficientValue i n)
      (data.targetRepresentative b (parameter n)) = _
  rw [show (fun i ↦ Sum.elim outerValue coefficientValue i n) =
      Sum.elim (fun i ↦ outerValue i n) (fun z ↦ coefficientValue z n) by
    funext i
    cases i <;> rfl]
  exact hn

/-! ## The supported Hermite simultaneous coefficient family -/

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

/-- The representative selected by `SimultaneousSourceCoefficientData` for
one actual outer coefficient of a canonical simultaneous source. -/
def simultaneousSupportedCoefficientRepresentative
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (he : e ∈ (((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
        q).support) :
    RestrictedBoxSpace p →
      MvPolynomial
        (ClusterOperationSymbol
          (data.OrderedClusterPrefixBlock c.val)
          (data.orderedClusterPrefixConstantDerivativeCount
            (paperRankHermiteHigherCount boundary.S + 1) c.val)) ℝ :=
  coefficients.representative ⟨q, ⟨e, he⟩⟩

/-- The supported representative has exactly the coefficient-polynomial germ
stored in the canonical source. -/
theorem simultaneousSupportedCoefficientRepresentative_germ_eq
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (he : e ∈ (((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
        q).support) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        ((((boundary.simultaneousNumericTrace D representative offset radius
          Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
            q).coeff e) =
      (boundary.simultaneousSupportedCoefficientRepresentative D representative
        offset radius Fsys x w₀ hw₀ data c r coefficients q e he :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (ClusterOperationSymbol
              (data.OrderedClusterPrefixBlock c.val)
              (data.orderedClusterPrefixConstantDerivativeCount
                (paperRankHermiteHigherCount boundary.S + 1) c.val)) ℝ)) := by
  exact coefficients.germ_eq ⟨q, ⟨e, he⟩⟩

/-- The generic zero-extended supported value is literally the concrete
coefficient value used by the common-tail simultaneous transfer. -/
theorem nestedSupportedCoefficientValue_eq_simultaneousQuantitative
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (n : ℕ) :
    nestedSupportedCoefficientValue
        (((boundary.simultaneousNumericTrace D representative offset radius
          Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
            q)
        (boundary.simultaneousSupportedCoefficientRepresentative D
          representative offset radius Fsys x w₀ hw₀ data c r coefficients q)
        (fun k ↦ (boundary.selectedTranslatedParameter D representative offset
          radius Fsys x w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset radius
            Fsys x w₀ hw₀ data hA k)).2)
        (fun z k ↦ boundary.simultaneousSmallerPrefixSequenceValue D
          representative offset radius Fsys x w₀ hw₀ data c r.val z
          (boundary.simultaneousQuantitativeReindex D representative offset radius
            Fsys x w₀ hw₀ data hA k)) e n =
      boundary.simultaneousQuantitativeSourceCoefficientValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r coefficients q e n := by
  by_cases he : e ∈ (((boundary.simultaneousNumericTrace D representative
      offset radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
        q).support
  · simp only [nestedSupportedCoefficientValue, dif_pos he,
      simultaneousQuantitativeSourceCoefficientValue,
      simultaneousSourceCoefficientValue, dif_pos he,
      FiniteMovingCoefficientData.polynomialValueAlong,
      simultaneousSupportedCoefficientRepresentative]
  · simp only [nestedSupportedCoefficientValue, dif_neg he,
      simultaneousQuantitativeSourceCoefficientValue,
      simultaneousSourceCoefficientValue, dif_neg he]

/-- Any flattened representative of a canonical simultaneous source agrees
eventually with its concrete support-local coefficientwise source evaluation.
This is the direct seam needed by a finite analytic displayed-source change. -/
theorem eventually_flattenedRepresentativeEvaluation_eq_simultaneousCoefficientwiseSource
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (sourceRepresentative : RestrictedBoxSpace p →
      MvPolynomial
        (ClusterOperationSymbol
            (Fin (data.orderedCluster c).card)
            (terminalTotalDerivativeCount (fun _ :
              Fin (data.orderedCluster c).card ↦
                paperRankHermiteHigherCount boundary.S)) ⊕
          ClusterOperationSymbol
            (data.OrderedClusterPrefixBlock c.val)
            (data.orderedClusterPrefixConstantDerivativeCount
              (paperRankHermiteHigherCount boundary.S + 1) c.val)) ℝ)
    (hsourceRepresentative :
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
            (ClusterOperationSymbol
              (Fin (data.orderedCluster c).card)
              (terminalTotalDerivativeCount (fun _ :
                Fin (data.orderedCluster c).card ↦
                  paperRankHermiteHigherCount boundary.S)))
            (ClusterOperationSymbol
              (data.OrderedClusterPrefixBlock c.val)
              (data.orderedClusterPrefixConstantDerivativeCount
                (paperRankHermiteHigherCount boundary.S + 1) c.val))
            (((boundary.simultaneousNumericTrace D representative offset radius
              Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
                q)) =
        (sourceRepresentative : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (ClusterOperationSymbol
                (Fin (data.orderedCluster c).card)
                (terminalTotalDerivativeCount (fun _ :
                  Fin (data.orderedCluster c).card ↦
                    paperRankHermiteHigherCount boundary.S)) ⊕
              ClusterOperationSymbol
                (data.OrderedClusterPrefixBlock c.val)
                (data.orderedClusterPrefixConstantDerivativeCount
                  (paperRankHermiteHigherCount boundary.S + 1) c.val)) ℝ)))
    (u : Fin (data.orderedCluster c).card → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i)) :
    ∀ᶠ n in atTop,
      MvPolynomial.eval
          (Sum.elim
            (fun z ↦ finiteRealJetActualAssignment u
              (terminalTotalDerivativeCount (fun _ :
                Fin (data.orderedCluster c).card ↦
                  paperRankHermiteHigherCount boundary.S)) jets z n)
            (fun z ↦ boundary.simultaneousSmallerPrefixSequenceValue D
              representative offset radius Fsys x w₀ hw₀ data c r.val z
              (boundary.simultaneousQuantitativeReindex D representative offset
                radius Fsys x w₀ hw₀ data hA n)))
          (sourceRepresentative
            ((boundary.selectedTranslatedParameter D representative offset
              radius Fsys x w₀ hw₀ data
              (boundary.simultaneousQuantitativeReindex D representative offset
                radius Fsys x w₀ hw₀ data hA n)).2)) =
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q) u jets
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source
              q) n := by
  let parameter : ℕ → RestrictedBoxSpace p := fun n ↦
    (boundary.selectedTranslatedParameter D representative offset radius Fsys x
      w₀ hw₀ data
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)).2
  let outerValue := finiteRealJetActualAssignment u
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦ paperRankHermiteHigherCount boundary.S))
    jets
  let coefficientValue := fun z n ↦
    boundary.simultaneousSmallerPrefixSequenceValue D representative offset
      radius Fsys x w₀ hw₀ data c r.val z
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)
  have hgeneric :=
    eventually_flattenedRepresentativeEvaluation_eq_coefficientwise
      (((boundary.simultaneousNumericTrace D representative offset radius Fsys x
        w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
      sourceRepresentative hsourceRepresentative
      (boundary.simultaneousSupportedCoefficientRepresentative D representative
        offset radius Fsys x w₀ hw₀ data c r coefficients q)
      (boundary.simultaneousSupportedCoefficientRepresentative_germ_eq D
        representative offset radius Fsys x w₀ hw₀ data c r coefficients q)
      parameter
      ((boundary.selectedTranslatedParameter_box_tendsto_zero D representative
        offset radius Fsys x w₀ hw₀ data).comp
        (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
          offset radius Fsys x w₀ hw₀ data hA))
      outerValue coefficientValue
  filter_upwards [hgeneric] with n hn
  rw [hn]
  unfold ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
  dsimp only [parameter, coefficientValue, outerValue]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  exact boundary.nestedSupportedCoefficientValue_eq_simultaneousQuantitative D
    representative offset radius Fsys x w₀ hw₀ data hA c r coefficients q e n

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

end AbelFormalization
