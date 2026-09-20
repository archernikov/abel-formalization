import AbelFormalization.RestrictedBasePaperRankElimination
import Scratch.RestrictedBaseZeroLocalControl

/-!
# The representative-count-zero base case

This scratch file composes the maintained sequential compactness reduction
with the finite-system/rank-elimination bridge and the local analytic-germ
algebra in `RestrictedBaseZeroLocalControl`.

No o-minimality theorem is used.  If the representative count is zero, the
finite selected Abel-jet set is empty.  The contracted height-`p` ideal first
forces the translated bounded coordinate of every sufficiently late regular
zero to be exactly zero.  The full unit-augmented Jacobian ideal then has
maximal possible height; specialization of its analytic-germ coefficients at
zero has a finite common-zero set.  Its assignments remember every auxiliary
coordinate, contradicting injectivity of the regular-zero sequence.
-/

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {A : ℝ → ℝ}

/-- The full representative-count-zero base case, conditional only on the
existing analytic-rank bridge.  In particular, it does not use the external
o-minimality hypothesis from `Statement`. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_zero
    (hA : IsAbel A) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 := by
  classical
  intro ι _ p D representative offset
  rw [restrictedBaseRegularZeroFinite_iff_no_boxConvergent_sequence]
  intro a R hDomain F hF x w₀ hxinj hxmem hw₀ hxlim
  letI : IsEmpty ι := ⟨fun k ↦ Fin.elim0 (representative k)⟩

  let D₀ : RestrictedBox p := D.translateToZero w₀
  let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
    restrictedOffsetTranslateToZero w₀ offset
  let F₀ : Fin ((0 + p) + a) → RestrictedSource 0 p a → ℝ :=
    restrictedEquationFamilyTranslateToZero w₀ F
  let x₀ : ℕ → RestrictedSource 0 p a :=
    fun n ↦ restrictedSourceTranslateToZero w₀ (x n)
  have h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox := by
    exact D.zero_mem_closedBox_translateToZero hw₀
  have hDomain₀ : restrictedBaseClosedDomain (m := 0) (a := a) D₀ R ⊆
      restrictedAbelJetDomain (a := a) D₀ representative offset₀ := by
    exact restrictedBaseClosedDomain_subset_AbelJetDomain_translateToZero
      D R representative offset w₀ hDomain
  have hF₀ : ∀ i, F₀ i ∈ restrictedExpressionBase D₀
      (restrictedAbelJetGenerators (a := a) A representative offset₀) := by
    intro i
    exact restrictedExpressionBase_precomp_translateFromZero
      A D representative offset w₀ (hF i)
  have hx₀ : ∀ n, x₀ n ∈ regularZeroSet
      (restrictedBaseOpenDomain D₀ R) (constraintMap F₀) := by
    intro n
    exact mem_regularZeroSet_restrictedEquationFamilyTranslateToZero
      D R w₀ F (hxmem n)
  have hxlim₀ : Tendsto (fun n ↦ (x₀ n).1.2) atTop
      (𝒩 (0 : RestrictedBoxSpace p)) := by
    exact tendsto_restrictedSourceTranslateToZero_box_zero w₀ x hxlim
  have hx₀inj : Function.Injective x₀ := by
    exact (restrictedSourceTranslateToZero_injective w₀).comp hxinj

  obtain ⟨S, Q, C, I, c, g, G, W, hC, hQ, hI, hheight, hspan,
      hWopen, h0W, hsupport, hanalytic, hG, hvanish⟩ :=
    hA.exists_restrictedBasePaperRankElimination_of_mem_base
      D₀ h0D₀ representative offset₀ R hDomain₀ F₀ hF₀
        x₀ hx₀ hxlim₀

  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨k, r⟩ hk
    exact isEmptyElim k
  subst S

  have hheightI : (p : ℕ∞) ≤ I.height := by
    simpa only [Nat.zero_add] using hheight
  have hparameterLocal :
      ∀ᶠ v in 𝒩 (0 : RestrictedBoxSpace p),
        ∀ z : PaperRankRetainedSymbols 0 0 → ℝ,
          (∀ j, MvPolynomial.eval z (G j v) = 0) → v = 0 :=
    eventually_parameter_eq_zero_of_isEmpty_polynomial_height
      p I hheightI g G hspan hG
  have hparameterSequence :
      ∀ᶠ n in atTop, (x₀ n).1.2 = 0 := by
    have hlocalAlong := hxlim₀.eventually hparameterLocal
    filter_upwards [hlocalAlong, hvanish] with n hn hzero
    exact hn
      (paperRankRetainedArgument
        (restrictedSelectedAbelJets A representative offset₀
          (restrictedJetEnumeration ∅)) (x₀ n)) hzero

  let P : Fin (p + a) →
      MvPolynomial (PaperRankSymbols 0 a 0) (RealAnalyticGerm p) :=
    fun i ↦ restrictedPaperGermPolynomial D₀ h0D₀ (Q i)
  let coeff : Fin (p + a) → (PaperRankSymbols 0 a 0 →₀ ℕ) →
      RestrictedBoxSpace p → ℝ :=
    restrictedPaperCoefficientRepresentative Q
  let PRep : Fin (p + a) → RestrictedBoxSpace p →
      MvPolynomial (PaperRankSymbols 0 a 0) ℝ :=
    fun i ↦ polynomialFromCoefficientRepresentatives
      (P i).support (coeff i)
  let d : MvPolynomial (PaperRankSymbols 0 a 0) (RealAnalyticGerm p) :=
    derivationJacobianDenominator P (analyticGermFormalDerivations p)
  let dRep : RestrictedBoxSpace p →
      MvPolynomial (PaperRankSymbols 0 a 0) ℝ :=
    analyticGermJacobianDenominatorRepresentative P coeff
  let V : PaperRankParameterSpace 0 p → PaperRankRealSpace 0 :=
    restrictedSelectedAbelJets A representative offset₀
      (restrictedJetEnumeration ∅)

  have hcoeff0 : ∀ i e, AnalyticAt ℝ (coeff i e) 0 := by
    intro i e
    exact restrictedAnalyticCoefficient_analyticAt_zero
      D₀ h0D₀ ((Q i).coeff e)
  have hrep : ∀ i e, e ∈ (P i).support →
      (P i).coeff e = analyticGermOf (coeff i e) (hcoeff0 i e) := by
    intro i e he
    exact restrictedPaperGermPolynomial_coeff_representation
      D₀ h0D₀ Q i e
  have hPRep : ∀ i,
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (P i) =
        (PRep i : Germ (𝒩 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankSymbols 0 a 0) ℝ)) := by
    intro i
    exact analyticPolynomialGermHom_eq_coefficientRepresentative
      (0 : RestrictedBoxSpace p) (P i) (coeff i) (hcoeff0 i) (hrep i)
  have hdRep :
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p) d =
        (dRep : Germ (𝒩 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankSymbols 0 a 0) ℝ)) := by
    exact analyticPolynomialGermHom_formalJacobianDenominator
      P coeff hcoeff0 hrep

  let J : Ideal
      (MvPolynomial (Option (PaperRankSymbols 0 a 0)) (RealAnalyticGerm p)) :=
    mvPolynomialUnitAugmentedIdeal P d
  let Z : Set (Option (PaperRankSymbols 0 a 0) → ℝ) :=
    {z | ∀ f ∈ J,
      MvPolynomial.eval₂
        (analyticGermValueAlgHom (0 : RestrictedBoxSpace p)).toRingHom z f = 0}
  have hZfinite : Z.Finite := by
    dsimp only [Z, J, d]
    apply finite_specialized_commonZero_unitAugmentedJacobian
      p (p + a) (σ := PaperRankSymbols 0 a 0)
        (γ := Fin p ⊕ PaperRankSymbols 0 a 0)
        (P := P) (D := analyticGermFormalDerivations p)
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_option,
      Nat.zero_add, Nat.add_zero]

  obtain ⟨W₀, hW₀open, h0W₀, hcoeffW₀, hpolyW₀⟩ :=
    exists_restrictedPaperCoefficientNeighborhood D₀ h0D₀ Q C hC
  let Ω : Set (RestrictedSource 0 p a) :=
    restrictedBaseOpenDomain D₀ R ∩ {y | y.1.2 ∈ W₀}
  have hΩopen : IsOpen Ω := by
    exact (isOpen_restrictedBaseOpenDomain D₀ R).inter
      (hW₀open.preimage (continuous_snd.comp continuous_fst))
  have hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω) := by
    exact hA.contDiffOn_restrictedSelectedAbelJets
      D₀ R representative offset₀ hDomain₀
        (restrictedJetEnumeration ∅) Ω Set.inter_subset_left
  have heqOn : ∀ y ∈ Ω,
      paperRankEquation P coeff V y = constraintMap F₀ y := by
    intro y hy
    exact paperRankEquation_restricted_eq_constraintMap
      A D₀ h0D₀ representative offset₀
        (restrictedJetEnumeration ∅) Q F₀ hQ W₀ hpolyW₀ y hy.2

  let augmentedAssignment : ℕ → Option (PaperRankSymbols 0 a 0) → ℝ :=
    fun n o ↦ o.elim
      (MvPolynomial.eval (paperRankSymbolArgument V (x₀ n))
        (dRep 0))⁻¹
      (paperRankSymbolArgument V (x₀ n))
  have haugmented : ∀ᶠ n in atTop, augmentedAssignment n ∈ Z := by
    filter_upwards [hparameterSequence] with n hn
    have hxnΩ : x₀ n ∈ Ω := by
      refine ⟨(hx₀ n).1, ?_⟩
      simpa only [hn] using h0W₀
    have hzeroPaper : paperRankEquation P coeff V (x₀ n) = 0 := by
      rw [heqOn (x₀ n) hxnΩ]
      exact (hx₀ n).2.1
    have heventuallyEq : paperRankEquation P coeff V =ᶠ[𝒩 (x₀ n)]
        constraintMap F₀ := by
      filter_upwards [hΩopen.mem_nhds hxnΩ] with y hy
      exact heqOn y hy
    have hregularPaper : Function.Surjective
        (fderiv ℝ (paperRankEquation P coeff V) (x₀ n)) := by
      rw [heventuallyEq.fderiv_eq]
      exact (hx₀ n).2.2
    have hcoeffDiff : ∀ i e, e ∈ (P i).support →
        DifferentiableAt ℝ (coeff i e)
          (paperRankCoefficientArgument 0 p a (x₀ n)) := by
      intro i e he
      exact (hcoeffW₀ i e he _ hxnΩ.2).differentiableAt
    have hpositive := polynomialFamilyFormalJacobian_sumSquares_pos
      (fun i ↦ (P i).support) coeff
      (paperRankCoefficientArgument 0 p a) (paperRankSymbolArgument V)
      (x₀ n)
      (differentiableAt_paperRankCoefficientArgument 0 p a (x₀ n))
      (differentiableAt_paperRankSymbolArgument hΩopen hV hxnΩ)
      hcoeffDiff hregularPaper
    have hdenominator :
        MvPolynomial.eval (paperRankSymbolArgument V (x₀ n))
          (dRep 0) ≠ 0 := by
      change MvPolynomial.eval (paperRankSymbolArgument V (x₀ n))
        (analyticGermJacobianDenominatorRepresentative P coeff 0) ≠ 0
      rw [eval_analyticGermJacobianDenominatorRepresentative]
      apply ne_of_gt
      simpa only [paperRankCoefficientArgument_apply, hn] using hpositive
    have hzeroRep : ∀ i,
        MvPolynomial.eval (paperRankSymbolArgument V (x₀ n))
          (PRep i 0) = 0 := by
      intro i
      have hi := congrFun hzeroPaper i
      simpa only [paperRankEquation, polynomialFamilyEvaluation,
        polynomialFromCoefficientRepresentatives,
        paperRankCoefficientArgument_apply, Pi.zero_apply, hn, PRep] using hi
    have hker :=
      mvPolynomialUnitAugmentedIdeal_le_ker_eval₂_analyticGermValue
        p (p + a) P d PRep dRep hPRep hdRep
        (paperRankSymbolArgument V (x₀ n)) hzeroRep hdenominator
    intro f hf
    exact hker hf

  have hboth : ∀ᶠ n in atTop,
      (x₀ n).1.2 = 0 ∧ augmentedAssignment n ∈ Z :=
    hparameterSequence.and haugmented
  obtain ⟨N, hN⟩ := eventually_atTop.mp hboth
  let tailAssignment : ℕ → Option (PaperRankSymbols 0 a 0) → ℝ :=
    fun n ↦ augmentedAssignment (N + n)
  have htailInjective : Function.Injective tailAssignment := by
    intro n k hnk
    have hnData := hN (N + n) (Nat.le_add_right N n)
    have hkData := hN (N + k) (Nat.le_add_right N k)
    have hy : (x₀ (N + n)).2 = (x₀ (N + k)).2 := by
      funext i
      have hi := congrFun hnk (some (Sum.inl i))
      simpa only [tailAssignment, augmentedAssignment,
        paperRankSymbolArgument_aux] using hi
    have hxEq : x₀ (N + n) = x₀ (N + k) := by
      apply Prod.ext
      · apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact hnData.1.trans hkData.1.symm
      · exact hy
    exact Nat.add_left_cancel (hx₀inj hxEq)
  have htailMem : ∀ n, tailAssignment n ∈ Z := by
    intro n
    exact (hN (N + n) (Nat.le_add_right N n)).2
  exact (Set.infinite_of_injective_forall_mem htailInjective htailMem) hZfinite

end AbelFormalization
