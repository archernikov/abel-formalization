import AbelFormalization.AnalyticRankElimination
import AbelFormalization.RestrictedBaseConvergentSequence
import AbelFormalization.RestrictedBaseFiniteSystemCompression
import AbelFormalization.RestrictedBoxTranslation

/-!
# The restricted base system as an analytic-germ rank system

This file is the local algebraic bridge used in the all-unbounded branch.
It starts after finite-system compression.  The bounded coordinates have
already been translated so that their selected limit is zero.

The analytic-box coefficients are mapped to actual analytic germs at zero.
Because taking a germ can delete supported monomials, the resulting paper
equation need only equal the original compressed polynomial on a smaller
common neighborhood of zero.  Finiteness of the polynomial family makes
that neighborhood uniform.  Restricting the original open source domain to
this neighborhood preserves both its zeros and its Frechet derivative.
-/

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- An analytic-box coefficient is analytic at zero whenever zero belongs
to the closed box. -/
theorem restrictedAnalyticCoefficient_analyticAt_zero
    {p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    AnalyticAt ℝ (b : RestrictedBoxSpace p → ℝ) 0 :=
  (D.analyticNearClosedBox_iff.mp b.property) 0 h0D

/-- Take the germ at the normalized bounded-coordinate limit. -/
def restrictedAnalyticCoefficientGermHom
    {p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox) :
    RestrictedBox.analyticNearClosedBoxSubalgebra D →+*
      RealAnalyticGerm p :=
  RingHom.codRestrict
    ((Germ.coeRingHom (𝓝 (0 : RestrictedBoxSpace p))).comp
      (RestrictedBox.analyticNearClosedBoxSubalgebra D).val.toRingHom)
    (analyticGermSubring (0 : RestrictedBoxSpace p))
    (fun b => ⟨(b : RestrictedBoxSpace p → ℝ),
      restrictedAnalyticCoefficient_analyticAt_zero D h0D b, rfl⟩)

@[simp]
theorem restrictedAnalyticCoefficientGermHom_apply
    {p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedAnalyticCoefficientGermHom D h0D b =
      analyticGermOf (b : RestrictedBoxSpace p → ℝ)
        (restrictedAnalyticCoefficient_analyticAt_zero D h0D b) := by
  apply Subtype.ext
  rfl

/-- Map one compressed paper polynomial to analytic germs at zero. -/
def restrictedPaperGermPolynomial
    {p m a b : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (Q : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    MvPolynomial (PaperRankSymbols m a b) (RealAnalyticGerm p) :=
  MvPolynomial.map (restrictedAnalyticCoefficientGermHom D h0D) Q

/-- The original total analytic representative of every coefficient. -/
def restrictedPaperCoefficientRepresentative
    {p m a b n : ℕ} {D : RestrictedBox p}
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (i : Fin n) (d : PaperRankSymbols m a b →₀ ℕ) :
    RestrictedBoxSpace p → ℝ :=
  (Q i).coeff d

/-- Specialize all analytic-box coefficients of a compressed polynomial at
one bounded-coordinate value, without yet assigning its paper symbols. -/
def restrictedPaperRealPolynomial
    {p m a b : ℕ} (D : RestrictedBox p)
    (Q : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (w : RestrictedBoxSpace p) : MvPolynomial (PaperRankSymbols m a b) ℝ :=
  MvPolynomial.map
    (subalgebraPointEval
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) w) Q

@[simp]
theorem restrictedPaperGermPolynomial_coeff
    {p m a b : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (Q : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (d : PaperRankSymbols m a b →₀ ℕ) :
    (restrictedPaperGermPolynomial D h0D Q).coeff d =
      restrictedAnalyticCoefficientGermHom D h0D (Q.coeff d) := by
  rw [restrictedPaperGermPolynomial, MvPolynomial.coeff_map]

/-- Mapping analytic representatives to germs and then forming a polynomial
is the germ of the pointwise real-coefficient polynomial. -/
theorem analyticPolynomialGermHom_restrictedPaperGermPolynomial
    {p m a b : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (Q : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (restrictedPaperGermPolynomial D h0D Q) =
      (restrictedPaperRealPolynomial D Q :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankSymbols m a b) ℝ)) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [restrictedPaperGermPolynomial, MvPolynomial.map_monomial,
        restrictedAnalyticCoefficientGermHom_apply,
        analyticPolynomialGermHom_monomial_of]
      apply Germ.coe_eq.mpr
      exact Eventually.of_forall fun w => by
        simp [restrictedPaperRealPolynomial]
  | add P Q hP hQ =>
      calc
        analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
            (restrictedPaperGermPolynomial D h0D (P + Q)) =
            analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
                (restrictedPaperGermPolynomial D h0D P) +
              analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
                (restrictedPaperGermPolynomial D h0D Q) := by
          simp [restrictedPaperGermPolynomial]
        _ = (restrictedPaperRealPolynomial D P :
              Germ (𝓝 (0 : RestrictedBoxSpace p))
                (MvPolynomial (PaperRankSymbols m a b) ℝ)) +
            (restrictedPaperRealPolynomial D Q :
              Germ (𝓝 (0 : RestrictedBoxSpace p))
                (MvPolynomial (PaperRankSymbols m a b) ℝ)) := by
          rw [hP, hQ]
        _ = (restrictedPaperRealPolynomial D (P + Q) :
              Germ (𝓝 (0 : RestrictedBoxSpace p))
                (MvPolynomial (PaperRankSymbols m a b) ℝ)) := by
          apply Germ.coe_eq.mpr
          exact Eventually.of_forall fun w => by
            simp [restrictedPaperRealPolynomial]

/-- Every mapped germ coefficient is represented by the original analytic
box function, including the precise proof expected by the rank lemma. -/
theorem restrictedPaperGermPolynomial_coeff_representation
    {p m a b n : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (i : Fin n) (d : PaperRankSymbols m a b →₀ ℕ) :
    (restrictedPaperGermPolynomial D h0D (Q i)).coeff d =
      analyticGermOf (restrictedPaperCoefficientRepresentative Q i d)
        (restrictedAnalyticCoefficient_analyticAt_zero D h0D
          ((Q i).coeff d)) := by
  rw [restrictedPaperGermPolynomial_coeff,
    restrictedAnalyticCoefficientGermHom_apply]
  rfl

/-- On some common open neighborhood of zero, the real polynomial obtained
from all original coefficients agrees with the support-truncated polynomial
used by `paperRankEquation`.  The same neighborhood makes every supported
coefficient analytic. -/
theorem exists_restrictedPaperCoefficientNeighborhood
    {p m a b n : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (hC : ∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C) :
    ∃ W₀ : Set (RestrictedBoxSpace p),
      IsOpen W₀ ∧ (0 : RestrictedBoxSpace p) ∈ W₀ ∧
      (∀ i d, d ∈ (restrictedPaperGermPolynomial D h0D (Q i)).support →
        AnalyticOnNhd ℝ (restrictedPaperCoefficientRepresentative Q i d) W₀) ∧
      ∀ i w, w ∈ W₀ →
        restrictedPaperRealPolynomial D (Q i) w =
          polynomialFromCoefficientRepresentatives
            (restrictedPaperGermPolynomial D h0D (Q i)).support
            (restrictedPaperCoefficientRepresentative Q i) w := by
  classical
  have hcoeffEventually : ∀ᶠ w in 𝓝 (0 : RestrictedBoxSpace p),
      ∀ c ∈ C, AnalyticAt ℝ (c : RestrictedBoxSpace p → ℝ) w :=
    (eventually_all_finset C).mpr fun c hc =>
      (restrictedAnalyticCoefficient_analyticAt_zero D h0D c).eventually_analyticAt
  have hpolyEventually : ∀ᶠ w in 𝓝 (0 : RestrictedBoxSpace p),
      ∀ i : Fin n,
        restrictedPaperRealPolynomial D (Q i) w =
          polynomialFromCoefficientRepresentatives
            (restrictedPaperGermPolynomial D h0D (Q i)).support
            (restrictedPaperCoefficientRepresentative Q i) w := by
    apply eventually_all.mpr
    intro i
    have hrep : ∀ d,
        AnalyticAt ℝ (restrictedPaperCoefficientRepresentative Q i d) 0 :=
      fun d => restrictedAnalyticCoefficient_analyticAt_zero
        D h0D ((Q i).coeff d)
    have hcoeffRep : ∀ d ∈
        (restrictedPaperGermPolynomial D h0D (Q i)).support,
        (restrictedPaperGermPolynomial D h0D (Q i)).coeff d =
          analyticGermOf (restrictedPaperCoefficientRepresentative Q i d)
            (hrep d) := by
      intro d hd
      exact restrictedPaperGermPolynomial_coeff_representation
        D h0D Q i d
    have htruncated :=
      analyticPolynomialGermHom_eq_coefficientRepresentative
        (0 : RestrictedBoxSpace p)
        (restrictedPaperGermPolynomial D h0D (Q i))
        (restrictedPaperCoefficientRepresentative Q i) hrep hcoeffRep
    exact Germ.coe_eq.mp
      ((analyticPolynomialGermHom_restrictedPaperGermPolynomial
        D h0D (Q i)).symm.trans htruncated)
  obtain ⟨W₀, hW₀, hW₀open, h0W₀⟩ := eventually_nhds_iff.mp
    (hcoeffEventually.and hpolyEventually)
  refine ⟨W₀, hW₀open, h0W₀, ?_, ?_⟩
  · intro i d hd w hw
    have hdQ : d ∈ (Q i).support :=
      MvPolynomial.support_map_subset
        (f := restrictedAnalyticCoefficientGermHom D h0D) (Q i) hd
    exact (hW₀ w hw).1 ((Q i).coeff d) (hC i d hdQ)
  · intro i w hw
    exact (hW₀ w hw).2 i

/-- Pointwise polynomial evaluation factors through the specialized real
polynomial, a useful normalization of `eval₂`. -/
theorem restrictedPaperPolynomialValue_eq_eval_realPolynomial
    (A : ℝ → ℝ) {m p a b : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ)
    (Q : MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (x : RestrictedSource m p a) :
    restrictedPaperPolynomialValue A D representative offset selected Q x =
      MvPolynomial.eval
        (paperRankSymbolArgument
          (restrictedSelectedAbelJets A representative offset selected) x)
        (restrictedPaperRealPolynomial D Q x.1.2) := by
  exact MvPolynomial.eval₂_eq_eval_map _ _ _

/-- Positivity on the original restricted domain makes every selected Abel
jet smooth on the projected parameter domain required by the paper's rank
lemma. -/
theorem IsAbel.contDiffOn_restrictedSelectedAbelJets
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a b : ℕ} (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (selected : Fin b → ι × ℕ)
    (Ω : Set (RestrictedSource m p a))
    (hΩbase : Ω ⊆ restrictedBaseOpenDomain D R) :
    ContDiffOn ℝ ∞
      (restrictedSelectedAbelJets A representative offset selected)
      (Prod.fst '' Ω) := by
  rw [contDiffOn_pi]
  intro j
  let k := (selected j).1
  let r := (selected j).2
  let arg : PaperRankParameterSpace m p → ℝ := fun sw =>
    sw.1 (representative k) +
      (offset k : RestrictedBoxSpace p → ℝ) sw.2
  have harg : AnalyticOnNhd ℝ arg (Prod.fst '' Ω) := by
    rintro sw ⟨x, hxΩ, rfl⟩
    have hxbase := hΩbase hxΩ
    have hxclosed := restrictedBaseOpenDomain_subset_closedDomain D R hxbase
    have hwclosed : x.1.2 ∈ D.closedBox := hxclosed.2
    have hs : AnalyticAt ℝ
        (fun sw : PaperRankParameterSpace m p =>
          sw.1 (representative k)) x.1 :=
      ((ContinuousLinearMap.proj (R := ℝ) (representative k)).analyticAt x.1.1).comp
        (f := fun sw : PaperRankParameterSpace m p => sw.1) analyticAt_fst
    have hoff : AnalyticAt ℝ
        (fun sw : PaperRankParameterSpace m p =>
          (offset k : RestrictedBoxSpace p → ℝ) sw.2) x.1 :=
      ((D.analyticNearClosedBox_iff.mp (offset k).property)
        x.1.2 hwclosed).comp
          (f := fun sw : PaperRankParameterSpace m p => sw.2) analyticAt_snd
    exact hs.add hoff
  have hpos : MapsTo arg (Prod.fst '' Ω) (Set.Ioi 0) := by
    rintro sw ⟨x, hxΩ, rfl⟩
    have hxbase := hΩbase hxΩ
    have hxjet := hDomain
      (restrictedBaseOpenDomain_subset_closedDomain D R hxbase)
    exact hxjet.2 k
  change ContDiffOn ℝ ∞ ((iteratedDeriv r A) ∘ arg) (Prod.fst '' Ω)
  rw [iteratedDeriv_eq_iterate]
  have hcomp : AnalyticOnNhd ℝ ((deriv^[r] A) ∘ arg)
      (Prod.fst '' Ω) := (hA.analytic.iterated_deriv r).comp harg hpos
  exact hcomp.contDiffOn_of_completeSpace

/-- On the common coefficient neighborhood, the compressed paper equation
is literally the original square map. -/
theorem paperRankEquation_restricted_eq_constraintMap
    (A : ℝ → ℝ) {m p a b : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ)
    (Q : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hQ : ∀ i, restrictedPaperPolynomialValue A D representative offset
      selected (Q i) = F i)
    (W₀ : Set (RestrictedBoxSpace p))
    (hpoly : ∀ i w, w ∈ W₀ →
      restrictedPaperRealPolynomial D (Q i) w =
        polynomialFromCoefficientRepresentatives
          (restrictedPaperGermPolynomial D h0D (Q i)).support
          (restrictedPaperCoefficientRepresentative Q i) w) :
    ∀ x, x.1.2 ∈ W₀ →
      paperRankEquation
          (fun i => restrictedPaperGermPolynomial D h0D (Q i))
          (restrictedPaperCoefficientRepresentative Q)
          (restrictedSelectedAbelJets A representative offset selected) x =
        constraintMap F x := by
  intro x hxW
  funext i
  change MvPolynomial.eval
      (paperRankSymbolArgument
        (restrictedSelectedAbelJets A representative offset selected) x)
      (polynomialFromCoefficientRepresentatives
        (restrictedPaperGermPolynomial D h0D (Q i)).support
        (restrictedPaperCoefficientRepresentative Q i) x.1.2) = F i x
  rw [← hpoly i x.1.2 hxW]
  rw [← restrictedPaperPolynomialValue_eq_eval_realPolynomial
    A D representative offset selected (Q i) x]
  exact congrFun (hQ i) x

/-- Apply the paper's analytic rank elimination once to a fixed compressed
base system.  Along any normalized regular-zero sequence, every chosen
eliminated generator then vanishes exactly for all sufficiently large
indices. -/
theorem IsAbel.exists_restrictedBasePaperRankElimination_along_sequence
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a b : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (selected : Fin b → ι × ℕ)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (Q : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (hC : ∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C)
    (hQ : ∀ i, restrictedPaperPolynomialValue A D representative offset
      selected (Q i) = F i)
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hxlim : Tendsto (fun n => (x n).1.2) atTop
      (𝓝 (0 : RestrictedBoxSpace p))) :
    ∃ I : Ideal
        (MvPolynomial (PaperRankRetainedSymbols m b) (RealAnalyticGerm p)),
      ∃ c : ℕ,
      ∃ g : Fin c →
          MvPolynomial (PaperRankRetainedSymbols m b) (RealAnalyticGerm p),
      ∃ G : Fin c → RestrictedBoxSpace p →
          MvPolynomial (PaperRankRetainedSymbols m b) ℝ,
      ∃ W : Set (RestrictedBoxSpace p),
        I = jacobianEliminationIdeal a
          (fun i => restrictedPaperGermPolynomial D h0D (Q i))
          (analyticGermFormalDerivations p) ∧
        ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
        Ideal.span (Set.range g) = I ∧
        IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
        (∀ j w, (G j w).support ⊆ (g j).support) ∧
        (∀ j d, AnalyticOnNhd ℝ (fun w => (G j w).coeff d) W) ∧
        (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
          (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial (PaperRankRetainedSymbols m b) ℝ))) ∧
        ∀ᶠ n in atTop, ∀ j,
          MvPolynomial.eval
            (paperRankRetainedArgument
              (restrictedSelectedAbelJets A representative offset selected) (x n))
            (G j (x n).1.2) = 0 := by
  classical
  obtain ⟨W₀, hW₀open, h0W₀, hcoeff, hpoly⟩ :=
    exists_restrictedPaperCoefficientNeighborhood D h0D Q C hC
  let P : Fin (m + p + a) →
      MvPolynomial (PaperRankSymbols m a b) (RealAnalyticGerm p) :=
    fun i => restrictedPaperGermPolynomial D h0D (Q i)
  let coeff : Fin (m + p + a) → (PaperRankSymbols m a b →₀ ℕ) →
      RestrictedBoxSpace p → ℝ :=
    restrictedPaperCoefficientRepresentative Q
  let V : PaperRankParameterSpace m p → PaperRankRealSpace b :=
    restrictedSelectedAbelJets A representative offset selected
  let Ω : Set (RestrictedSource m p a) :=
    restrictedBaseOpenDomain D R ∩ {y | y.1.2 ∈ W₀}
  have hΩopen : IsOpen Ω := by
    exact (isOpen_restrictedBaseOpenDomain D R).inter
      (hW₀open.preimage (continuous_snd.comp continuous_fst))
  have hΩbase : Ω ⊆ restrictedBaseOpenDomain D R := Set.inter_subset_left
  have hΩW₀ : ∀ y ∈ Ω, y.1.2 ∈ W₀ := fun y hy => hy.2
  have hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω) := by
    exact hA.contDiffOn_restrictedSelectedAbelJets
      D R representative offset hDomain selected Ω hΩbase
  have hrep : ∀ i d
      (hd : d ∈ (P i).support),
      (P i).coeff d = analyticGermOf (coeff i d)
        (hcoeff i d hd 0 h0W₀) := by
    intro i d hd
    exact restrictedPaperGermPolynomial_coeff_representation
      D h0D Q i d
  have heqOn : ∀ y ∈ Ω,
      paperRankEquation P coeff V y = constraintMap F y := by
    intro y hy
    exact paperRankEquation_restricted_eq_constraintMap
      A D h0D representative offset selected Q F hQ W₀ hpoly y hy.2
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W, hWW₀,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_paperRankElimination m p a b P coeff W₀ hW₀open h0W₀
      hcoeff hrep Ω hΩopen hΩW₀ V hV
  refine ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W,
    hsupport, hanalytic, hG, ?_⟩
  have hxW : ∀ᶠ n in atTop, (x n).1.2 ∈ W :=
    hxlim (hWopen.mem_nhds h0W)
  filter_upwards [hxW] with n hnW
  intro j
  have hxnΩ : x n ∈ Ω := ⟨(hx n).1, hWW₀ hnW⟩
  have hzero : paperRankEquation P coeff V (x n) = 0 := by
    rw [heqOn (x n) hxnΩ]
    exact (hx n).2.1
  have heventuallyEq : paperRankEquation P coeff V =ᶠ[𝓝 (x n)]
      constraintMap F := by
    filter_upwards [hΩopen.mem_nhds hxnΩ] with y hy
    exact heqOn y hy
  have hregular : Function.Surjective
      (fderiv ℝ (paperRankEquation P coeff V) (x n)) := by
    rw [heventuallyEq.fderiv_eq]
    exact (hx n).2.2
  exact hvanish (x n) hxnΩ hnW hzero hregular j

/-- The end-to-end level-zero wrapper: finite-system compression chooses one
finite list of Abel jets and one polynomial family, and analytic rank
elimination supplies a single fixed eliminated ideal and a finite analytic
generator family vanishing eventually along the normalized regular-zero
sequence. -/
theorem IsAbel.exists_restrictedBasePaperRankElimination_of_mem_base
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hxlim : Tendsto (fun n => (x n).1.2) atTop
      (𝓝 (0 : RestrictedBoxSpace p))) :
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
    ∃ C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D),
    ∃ I : Ideal
        (MvPolynomial (PaperRankRetainedSymbols m S.card)
          (RealAnalyticGerm p)),
    ∃ c : ℕ,
    ∃ g : Fin c →
        MvPolynomial (PaperRankRetainedSymbols m S.card)
          (RealAnalyticGerm p),
    ∃ G : Fin c → RestrictedBoxSpace p →
        MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ,
    ∃ W : Set (RestrictedBoxSpace p),
      (∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C) ∧
      (∀ i, restrictedPaperPolynomialValue A D representative offset
        (restrictedJetEnumeration S) (Q i) = F i) ∧
      I = jacobianEliminationIdeal a
        (fun i => restrictedPaperGermPolynomial D h0D (Q i))
        (analyticGermFormalDerivations p) ∧
      ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
      Ideal.span (Set.range g) = I ∧
      IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
      (∀ j w, (G j w).support ⊆ (g j).support) ∧
      (∀ j d, AnalyticOnNhd ℝ (fun w => (G j w).coeff d) W) ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
        (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) ∧
      ∀ᶠ n in atTop, ∀ j,
        MvPolynomial.eval
          (paperRankRetainedArgument
            (restrictedSelectedAbelJets A representative offset
              (restrictedJetEnumeration S)) (x n))
          (G j (x n).1.2) = 0 := by
  classical
  obtain ⟨S, Q, C, hC, hQ⟩ :=
    exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
      A D representative offset F hF
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W,
      hsupport, hanalytic, hG, hvanish⟩ :=
    hA.exists_restrictedBasePaperRankElimination_along_sequence
      D h0D representative offset (restrictedJetEnumeration S) R hDomain
      F Q C hC hQ x hx hxlim
  exact ⟨S, Q, C, I, c, g, G, W, hC, hQ, hI, hheight, hspan,
    hWopen, h0W, hsupport, hanalytic, hG, hvanish⟩

/-! ## Normalization at an arbitrary bounded-coordinate limit -/

/-- Subtract a bounded-coordinate base point from one restricted-source
point.  This is the explicit inverse of
`restrictedSourceTranslateFromZero`. -/
def restrictedSourceNormalizeAt {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) :
    RestrictedSource m p a → RestrictedSource m p a :=
  fun x ↦ ((x.1.1, x.1.2 - w₀), x.2)

@[simp]
theorem restrictedSourceTranslateFromZero_normalizeAt
    {m p a : ℕ} (w₀ : RestrictedBoxSpace p)
    (x : RestrictedSource m p a) :
    restrictedSourceTranslateFromZero w₀
        (restrictedSourceNormalizeAt w₀ x) = x := by
  ext i <;> simp [restrictedSourceTranslateFromZero,
    restrictedSourceNormalizeAt, RestrictedBox.translateFromZero]

@[simp]
theorem restrictedSourceNormalizeAt_box
    {m p a : ℕ} (w₀ : RestrictedBoxSpace p)
    (x : RestrictedSource m p a) :
    (restrictedSourceNormalizeAt w₀ x).1.2 = x.1.2 - w₀ :=
  rfl

/-- Normalize an arbitrary bounded-coordinate limit to zero, transport the
box, offsets, expression system, domain condition, and regular zeros, then
apply the level-zero paper-rank elimination bridge. -/
theorem IsAbel.exists_restrictedBasePaperRankElimination_at_limit
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (𝓝 w₀)) :
    let D₀ : RestrictedBox p := D.translateToZero w₀
    let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
      restrictedOffsetTranslateToZero w₀ offset
    let F₀ : Fin (m + p + a) → RestrictedSource m p a → ℝ :=
      restrictedEquationFamilyTranslateToZero w₀ F
    let x₀ : ℕ → RestrictedSource m p a :=
      fun n ↦ restrictedSourceNormalizeAt w₀ (x n)
    let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
      D.zero_mem_closedBox_translateToZero hw₀
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          D₀.analyticNearClosedBoxSubalgebra,
    ∃ C : Finset D₀.analyticNearClosedBoxSubalgebra,
    ∃ I : Ideal
        (MvPolynomial (PaperRankRetainedSymbols m S.card)
          (RealAnalyticGerm p)),
    ∃ c : ℕ,
    ∃ g : Fin c →
        MvPolynomial (PaperRankRetainedSymbols m S.card)
          (RealAnalyticGerm p),
    ∃ G : Fin c → RestrictedBoxSpace p →
        MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ,
    ∃ W : Set (RestrictedBoxSpace p),
      (∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C) ∧
      (∀ i, restrictedPaperPolynomialValue A D₀ representative offset₀
        (restrictedJetEnumeration S) (Q i) = F₀ i) ∧
      I = jacobianEliminationIdeal a
        (fun i ↦ restrictedPaperGermPolynomial D₀ h0D₀ (Q i))
        (analyticGermFormalDerivations p) ∧
      ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
      Ideal.span (Set.range g) = I ∧
      IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
      (∀ j w, (G j w).support ⊆ (g j).support) ∧
      (∀ j d, AnalyticOnNhd ℝ (fun w ↦ (G j w).coeff d) W) ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
        (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) ∧
      ∀ᶠ n in atTop, ∀ j,
        MvPolynomial.eval
          (paperRankRetainedArgument
            (restrictedSelectedAbelJets A representative offset₀
              (restrictedJetEnumeration S)) (x₀ n))
          (G j (x₀ n).1.2) = 0 := by
  dsimp only
  let D₀ : RestrictedBox p := D.translateToZero w₀
  let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
    restrictedOffsetTranslateToZero w₀ offset
  let F₀ : Fin (m + p + a) → RestrictedSource m p a → ℝ :=
    restrictedEquationFamilyTranslateToZero w₀ F
  let x₀ : ℕ → RestrictedSource m p a :=
    fun n ↦ restrictedSourceNormalizeAt w₀ (x n)
  let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
    D.zero_mem_closedBox_translateToZero hw₀
  have hDomain₀ : restrictedBaseClosedDomain (m := m) (a := a) D₀ R ⊆
      restrictedAbelJetDomain (a := a) D₀ representative offset₀ := by
    intro y hy
    have hyOld : restrictedSourceTranslateFromZero w₀ y ∈
        restrictedBaseClosedDomain (m := m) (a := a) D R := by
      have hyPre : y ∈ restrictedSourceTranslateFromZero w₀ ⁻¹'
          restrictedBaseClosedDomain (m := m) (a := a) D R := by
        rw [preimage_restrictedBaseClosedDomain_translateToZero D R w₀]
        exact hy
      exact hyPre
    have hyJetOld := hDomain hyOld
    have hyJetPre : y ∈ restrictedSourceTranslateFromZero w₀ ⁻¹'
        restrictedAbelJetDomain (a := a) D representative offset := hyJetOld
    rw [preimage_restrictedAbelJetDomain_translateToZero
      D representative offset w₀] at hyJetPre
    exact hyJetPre
  have hF₀ : ∀ i, F₀ i ∈ restrictedExpressionBase D₀
      (restrictedAbelJetGenerators (a := a) A representative offset₀) := by
    intro i
    exact restrictedExpressionBase_precomp_translateFromZero
      A D representative offset w₀ (hF i)
  have hx₀ : ∀ n, x₀ n ∈ regularZeroSet
      (restrictedBaseOpenDomain D₀ R) (constraintMap F₀) := by
    intro n
    rw [regularZeroSet_restrictedEquationFamilyTranslateToZero D R w₀ F]
    change restrictedSourceTranslateFromZero w₀ (x₀ n) ∈
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F)
    simpa only [x₀, restrictedSourceTranslateFromZero_normalizeAt] using hx n
  have hxlim₀ : Tendsto (fun n ↦ (x₀ n).1.2) atTop
      (𝓝 (0 : RestrictedBoxSpace p)) := by
    have hsub := hxlim.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ w₀) atTop (𝓝 w₀))
    simpa only [x₀, restrictedSourceNormalizeAt_box, sub_self] using hsub
  exact hA.exists_restrictedBasePaperRankElimination_of_mem_base
    D₀ h0D₀ representative offset₀ R hDomain₀ F₀ hF₀
      x₀ hx₀ hxlim₀

end AbelFormalization
