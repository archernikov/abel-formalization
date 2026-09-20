import AbelFormalization.RealQuantitativeTransferAssembly
import AbelFormalization.TransferCoefficientBounds

/-!
# Fixed-support coefficient bounds and real quantitative transfer

The coefficientwise evaluation API permits independently chosen analytic
representatives of the finitely many coefficients occurring in a
polynomial.  This file proves polynomial bounds and perturbation estimates
directly from that fixed support.  It then assembles the real jet transfer
without asking the coefficient values to extend to a ring homomorphism.

Values assigned to exponents outside the polynomial support are discarded.
They are explicitly replaced by zero before invoking the existing
coefficientwise quantitative theorem.  Thus every growth hypothesis below
is local to an actual finite support.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v

/-! ## Finite sums, products, and monomials -/

theorem HasPolynomialUpperBound.finset_sum
    {X κ : Type*} {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x) (s : Finset κ) (f : κ → X → Real)
    (hf : ∀ i ∈ s, HasPolynomialUpperBound l S (f i)) :
    HasPolynomialUpperBound l S (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using HasPolynomialUpperBound.zero l S
  | @insert i s his ih =>
      have hi := hf i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      apply (hi.add hS hs).congr
      intro x
      simp [Finset.sum_insert his]

theorem HasPolynomialUpperBound.finset_prod
    {X κ : Type*} {l : Filter X} {S : X → Real}
    (s : Finset κ) (f : κ → X → Real)
    (hf : ∀ i ∈ s, HasPolynomialUpperBound l S (f i)) :
    HasPolynomialUpperBound l S (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using HasPolynomialUpperBound.one l S
  | @insert i s his ih =>
      have hi := hf i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      apply (hi.mul hs).congr
      intro x
      simp [Finset.prod_insert his]

/-- A fixed monomial in polynomially bounded coordinates is polynomially
bounded.  No finiteness assumption on the ambient variable type is needed. -/
theorem finsuppMonomial_hasPolynomialUpperBound
    {X σ : Type*} {l : Filter X} {S : X → Real}
    (d : σ →₀ Nat) (y : σ → X → Real)
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    HasPolynomialUpperBound l S
      (fun x => d.prod (fun i n => y i x ^ n)) := by
  classical
  have hprod := HasPolynomialUpperBound.finset_prod d.support
    (fun i x => y i x ^ d i)
    (fun i hi => (hy i).pow (d i))
  apply hprod.congr
  intro x
  change (∏ i ∈ d.support, y i x ^ d i) =
    d.prod (fun i n => y i x ^ n)
  rfl

/-- A fixed monomial changes by a rapidly decaying amount under a
coordinatewise rapidly decaying perturbation. -/
theorem finsuppMonomial_sub_superpolynomialDecay
    {X σ : Type*} {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (d : σ →₀ Nat) (y z : σ → X → Real)
    (hy : ∀ i, HasPolynomialUpperBound l S (y i))
    (hz : ∀ i, HasPolynomialUpperBound l S (z i))
    (hyz : ∀ i, Asymptotics.SuperpolynomialDecay l S
      (fun x => y i x - z i x)) :
    Asymptotics.SuperpolynomialDecay l S (fun x =>
      d.prod (fun i n => y i x ^ n) -
        d.prod (fun i n => z i x ^ n)) := by
  have hp := mvPolynomial_eval₂Hom_sub_superpolynomialDecay
    hS (Pi.constRingHom X Real) y z
      (fun r => HasPolynomialUpperBound.const l S r)
      hy hz hyz (MvPolynomial.monomial d (1 : Real))
  apply hp.congr
  intro x
  simp only [MvPolynomial.eval₂Hom_monomial, Pi.constRingHom_apply,
    Pi.mul_apply, Function.const_apply, one_mul, Finsupp.prod,
    Finset.prod_apply, Pi.pow_apply]

/-! ## Arbitrary values on one finite monomial set -/

/-- Evaluation on an explicitly supplied finite monomial set. -/
def finiteMonomialSetEvaluation
    {σ X : Type*} (s : Finset (σ →₀ Nat))
    (a : (σ →₀ Nat) → X → Real) (y : σ → X → Real)
    (x : X) : Real :=
  ∑ d ∈ s, a d x * d.prod (fun i n => y i x ^ n)

/-- Fixed-set evaluation is polynomially bounded from bounds on precisely
the coefficients in that set and on the coordinates. -/
theorem finiteMonomialSetEvaluation_hasPolynomialUpperBound
    {X σ : Type*} {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (s : Finset (σ →₀ Nat))
    (a : (σ →₀ Nat) → X → Real) (y : σ → X → Real)
    (ha : ∀ d ∈ s, HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    HasPolynomialUpperBound l S
      (finiteMonomialSetEvaluation s a y) := by
  apply HasPolynomialUpperBound.finset_sum hS s
    (fun d x => a d x * d.prod (fun i n => y i x ^ n))
  intro d hd
  exact (ha d hd).mul (finsuppMonomial_hasPolynomialUpperBound d y hy)

/-- Fixed-set evaluation changes superpolynomially little when every
coordinate does.  Coefficient estimates are needed only on the displayed
finite set. -/
theorem finiteMonomialSetEvaluation_sub_superpolynomialDecay
    {X σ : Type*} {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (s : Finset (σ →₀ Nat))
    (a : (σ →₀ Nat) → X → Real)
    (y z : σ → X → Real)
    (ha : ∀ d ∈ s, HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i))
    (hz : ∀ i, HasPolynomialUpperBound l S (z i))
    (hyz : ∀ i, Asymptotics.SuperpolynomialDecay l S
      (fun x => y i x - z i x)) :
    Asymptotics.SuperpolynomialDecay l S (fun x =>
      finiteMonomialSetEvaluation s a y x -
        finiteMonomialSetEvaluation s a z x) := by
  have hS0 : ∀ᶠ x in l, 0 ≤ S x :=
    hS.mono (fun _ hx => zero_le_one.trans hx)
  have hterm : ∀ d ∈ s, Asymptotics.SuperpolynomialDecay l S
      (fun x => a d x *
        (d.prod (fun i n => y i x ^ n) -
          d.prod (fun i n => z i x ^ n))) := by
    intro d hd
    have hmono := finsuppMonomial_sub_superpolynomialDecay
      hS d y z hy hz hyz
    have hmul :=
      Asymptotics.SuperpolynomialDecay.mul_of_hasPolynomialUpperBound
        hmono hS0 (ha d hd)
    exact hmul.congr (fun x => mul_comm _ _)
  have hsum := superpolynomialDecay_finset_sum s
    (fun d x => a d x *
      (d.prod (fun i n => y i x ^ n) -
        d.prod (fun i n => z i x ^ n))) hterm
  apply hsum.congr
  intro x
  simp only [finiteMonomialSetEvaluation, Finset.sum_sub_distrib, mul_sub]

/-! ## Fixed polynomial support -/

/-- Coefficientwise evaluation of one fixed polynomial is polynomially
bounded using estimates only for coefficients in its support. -/
theorem finiteSupportPolynomialEvaluation_hasPolynomialUpperBound
    {R X σ : Type*} [CommRing R] {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real) (y : σ → X → Real)
    (ha : ∀ d ∈ f.support, HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    HasPolynomialUpperBound l S (fun x =>
      finiteSupportPolynomialEvaluation f (fun d => a d x)
        (fun i => y i x)) := by
  change HasPolynomialUpperBound l S
    (finiteMonomialSetEvaluation f.support a y)
  exact finiteMonomialSetEvaluation_hasPolynomialUpperBound
    hS f.support a y ha hy

/-- The coefficientwise evaluation of the initial support is polynomially
bounded under the same support-local coefficient assumptions. -/
theorem finiteSupportInitialEvaluation_hasPolynomialUpperBound
    {R X σ : Type*} [CommRing R] {h : Nat}
    {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (omega : σ → Fin h → Int) (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real) (y : σ → X → Real)
    (ha : ∀ d ∈ f.support, HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    HasPolynomialUpperBound l S (fun x =>
      finiteSupportInitialEvaluation omega f (fun d => a d x)
        (fun i => y i x)) := by
  change HasPolynomialUpperBound l S
    (finiteMonomialSetEvaluation
      (f.support.filter (fun d =>
        Finsupp.weight (fun i => toLex (omega i)) d =
          lexicographicMinimumWeight omega f)) a y)
  apply finiteMonomialSetEvaluation_hasPolynomialUpperBound hS
    (f.support.filter (fun d =>
      Finsupp.weight (fun i => toLex (omega i)) d =
        lexicographicMinimumWeight omega f)) a y
  · intro d hd
    exact ha d (Finset.mem_filter.mp hd).1
  · exact hy

/-- Support-local coefficient bounds and coordinatewise rapid decay imply
rapid decay of the difference of coefficientwise polynomial evaluations. -/
theorem finiteSupportPolynomialEvaluation_sub_superpolynomialDecay
    {R X σ : Type*} [CommRing R] {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real)
    (y z : σ → X → Real)
    (ha : ∀ d ∈ f.support, HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i))
    (hz : ∀ i, HasPolynomialUpperBound l S (z i))
    (hyz : ∀ i, Asymptotics.SuperpolynomialDecay l S
      (fun x => y i x - z i x)) :
    Asymptotics.SuperpolynomialDecay l S (fun x =>
      finiteSupportPolynomialEvaluation f (fun d => a d x)
          (fun i => y i x) -
        finiteSupportPolynomialEvaluation f (fun d => a d x)
          (fun i => z i x)) := by
  change Asymptotics.SuperpolynomialDecay l S (fun x =>
    finiteMonomialSetEvaluation f.support a y x -
      finiteMonomialSetEvaluation f.support a z x)
  exact finiteMonomialSetEvaluation_sub_superpolynomialDecay
    hS f.support a y z ha hy hz hyz

/-- The corresponding support-local perturbation theorem for the least
weighted part of a fixed polynomial. -/
theorem finiteSupportInitialEvaluation_sub_superpolynomialDecay
    {R X σ : Type*} [CommRing R] {h : Nat}
    {l : Filter X} {S : X → Real}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (omega : σ → Fin h → Int) (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real)
    (y z : σ → X → Real)
    (ha : ∀ d ∈ f.support, HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i))
    (hz : ∀ i, HasPolynomialUpperBound l S (z i))
    (hyz : ∀ i, Asymptotics.SuperpolynomialDecay l S
      (fun x => y i x - z i x)) :
    Asymptotics.SuperpolynomialDecay l S (fun x =>
      finiteSupportInitialEvaluation omega f (fun d => a d x)
          (fun i => y i x) -
        finiteSupportInitialEvaluation omega f (fun d => a d x)
          (fun i => z i x)) := by
  change Asymptotics.SuperpolynomialDecay l S (fun x =>
    finiteMonomialSetEvaluation
        (f.support.filter (fun d =>
          Finsupp.weight (fun i => toLex (omega i)) d =
            lexicographicMinimumWeight omega f)) a y x -
      finiteMonomialSetEvaluation
        (f.support.filter (fun d =>
          Finsupp.weight (fun i => toLex (omega i)) d =
            lexicographicMinimumWeight omega f)) a z x)
  apply finiteMonomialSetEvaluation_sub_superpolynomialDecay hS
    (f.support.filter (fun d =>
      Finsupp.weight (fun i => toLex (omega i)) d =
        lexicographicMinimumWeight omega f)) a y z
  · intro d hd
    exact ha d (Finset.mem_filter.mp hd).1
  · exact hy
  · exact hz
  · exact hyz

/-- The non-exponential multiplier of one tail monomial is polynomially
bounded from a bound on that coefficient and on all coordinates. -/
theorem coefficientwiseTailMultiplier_hasPolynomialUpperBound
    {R σ : Type*} [CommRing R] {l : Filter Nat} {S : Nat → Real}
    (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → Nat → Real) (y : σ → Nat → Real)
    (d : σ →₀ Nat)
    (ha : HasPolynomialUpperBound l S (a d))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    HasPolynomialUpperBound l S
      (fun x => coefficientwiseTailMultiplier f a y d x) := by
  exact ha.mul (finsuppMonomial_hasPolynomialUpperBound d y hy)

/-! ## Ignoring coefficient values outside the actual support -/

/-- Replace irrelevant coefficient values by zero. -/
def supportedCoefficientValue
    {R X σ : Type*} [CommRing R] (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real) :
    (σ →₀ Nat) → X → Real := by
  classical
  exact fun d x => if h : d ∈ f.support then a d x else 0

theorem supportedCoefficientValue_eq_of_mem
    {R X σ : Type*} [CommRing R] (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real)
    {d : σ →₀ Nat} (hd : d ∈ f.support) (x : X) :
    supportedCoefficientValue f a d x = a d x := by
  classical
  simp [supportedCoefficientValue, hd]

theorem supportedCoefficientValue_hasPolynomialUpperBound
    {R X σ : Type*} [CommRing R] {l : Filter X} {S : X → Real}
    (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real)
    (ha : ∀ d ∈ f.support, HasPolynomialUpperBound l S (a d)) :
    ∀ d, HasPolynomialUpperBound l S (supportedCoefficientValue f a d) := by
  classical
  intro d
  by_cases hd : d ∈ f.support
  · exact (ha d hd).congr
      (fun x => supportedCoefficientValue_eq_of_mem f a hd x)
  · exact (HasPolynomialUpperBound.zero l S).congr
      (fun x => by simp [supportedCoefficientValue, hd])

theorem finiteSupportPolynomialEvaluation_supportedCoefficientValue
    {R X σ : Type*} [CommRing R] (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real) (y : σ → X → Real)
    (x : X) :
    finiteSupportPolynomialEvaluation f
        (fun d => supportedCoefficientValue f a d x) (fun i => y i x) =
      finiteSupportPolynomialEvaluation f (fun d => a d x)
        (fun i => y i x) := by
  classical
  simp only [finiteSupportPolynomialEvaluation]
  apply Finset.sum_congr rfl
  intro d hd
  simp [supportedCoefficientValue, hd]

theorem finiteSupportInitialEvaluation_supportedCoefficientValue
    {R X σ : Type*} [CommRing R] {h : Nat}
    (omega : σ → Fin h → Int) (f : MvPolynomial σ R)
    (a : (σ →₀ Nat) → X → Real) (y : σ → X → Real)
    (x : X) :
    finiteSupportInitialEvaluation omega f
        (fun d => supportedCoefficientValue f a d x) (fun i => y i x) =
      finiteSupportInitialEvaluation omega f (fun d => a d x)
        (fun i => y i x) := by
  classical
  simp only [finiteSupportInitialEvaluation]
  apply Finset.sum_congr rfl
  intro d hd
  have hdsupport : d ∈ f.support := (Finset.mem_filter.mp hd).1
  simp [supportedCoefficientValue, hdsupport]

end AbelFormalization

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v

/-! ## Real jet evaluations with independent coefficient representatives -/

/-- Literal source evaluation using arbitrary values for the finitely many
coefficients of `f`. -/
def realJetCoefficientwiseSourceEvaluation
    {R : Type u} [CommRing R] {m : Nat} {A : Real → Real}
    (d : Fin (m + 1) → Nat)
    (coefficientValue : (RealJetTransferIndex m d →₀ Nat) → Nat → Real)
    (u : Fin (m + 1) → Nat → Real)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) : Real :=
  finiteSupportPolynomialEvaluation f (fun e => coefficientValue e n)
    (fun x => realJetActualAssignment u d jets x n)

/-- Central least-weight evaluation using the same independently chosen
coefficient representatives. -/
def realJetCoefficientwiseCentralEvaluation
    {R : Type u} [CommRing R] {m : Nat} (A : Real → Real)
    (d : Fin (m + 1) → Nat)
    (coefficientValue : (RealJetTransferIndex m d →₀ Nat) → Nat → Real)
    (u : Fin (m + 1) → Nat → Real)
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) : Real :=
  finiteSupportInitialEvaluation
    (centralLaurentWeight (centralTransferShear d)) f
    (fun e => coefficientValue e n)
    (fun x => realJetMainAssignment A u d x n)

/-- Exact compatibility of the weighted source expression with the literal
derivative/Hermite substitution.  No algebraic property of
`coefficientValue` is used. -/
theorem coefficientwiseWeightedSourceValue_eq_realJetCoefficientwiseSourceEvaluation
    {R : Type u} [CommRing R] {m : Nat} {A : Real → Real}
    (hA : IsAbel A) (d : Fin (m + 1) → Nat)
    (coefficientValue : (RealJetTransferIndex m d →₀ Nat) → Nat → Real)
    (u : Fin (m + 1) → Nat → Real)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) :
    coefficientwiseWeightedSourceValue
        (centralLaurentWeight (centralTransferShear d)) f
        coefficientValue (realJetPerturbedAssignment u d jets) u n =
      realJetCoefficientwiseSourceEvaluation d coefficientValue u jets f n := by
  unfold coefficientwiseWeightedSourceValue
  unfold realJetCoefficientwiseSourceEvaluation
  apply congrArg
    (finiteSupportPolynomialEvaluation f (fun e => coefficientValue e n))
  funext x
  exact hA.realCentralTransferPerturbed_scaled_eq_actual
    (fun i => u i n) (hu n) d (jets n) x

@[simp]
theorem coefficientwiseCentralValue_eq_realJetCoefficientwiseCentralEvaluation
    {R : Type u} [CommRing R] {m : Nat} (A : Real → Real)
    (d : Fin (m + 1) → Nat)
    (coefficientValue : (RealJetTransferIndex m d →₀ Nat) → Nat → Real)
    (u : Fin (m + 1) → Nat → Real)
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) :
    coefficientwiseCentralValue
        (centralLaurentWeight (centralTransferShear d)) f
        coefficientValue (realJetMainAssignment A u d) n =
      realJetCoefficientwiseCentralEvaluation A d coefficientValue u f n := rfl

/-! ## Certificate-level support-local quantitative transfer -/

/-- Quantitative transfer for independently selected coefficient
representatives of the finite canonical family.

Only coefficients in `(cert.source a).support` require bounds.  Values away
from those supports are replaced by zero internally.  Bounds on the main and
perturbed coordinates remain explicit; in particular, no bound is inferred
from positivity of an unchanged auxiliary argument.
-/
theorem CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer_coefficientwise
    {R : Type u} [CommRing R] {m : Nat}
    (d : Fin (m + 1) → Nat)
    (I : Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (cert : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    [Nonempty (Fin cert.count)]
    {A : Real → Real} (hA : IsAbel A)
    (coefficientValue : Fin cert.count →
      (RealJetTransferIndex m d →₀ Nat) → Nat → Real)
    (u : Fin (m + 1) → Nat → Real)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (Rscale Xscale : Nat → Real)
    {Central Original : Type v}
    [Fintype Central] [Nonempty Central]
    [Fintype Original] [Nonempty Original]
    (centralGenerator : Central → Nat → Real)
    (centralCoefficient : Central → Fin cert.count → Nat → Real)
    (originalGenerator : Original → Nat → Real)
    (sourceCoefficient : Fin cert.count → Original → Nat → Real)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last m) n)
    (hR : ∀ᶠ n in atTop, 2 ≤ Rscale n)
    (hratios : ∀ i : Fin m,
      Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto
      (fun n => u (Fin.last m) n / Real.log (Rscale n)) atTop atTop)
    (hRX : ∀ᶠ n in atTop, Rscale n ≤ Xscale n)
    (hX : ∀ᶠ n in atTop, 2 ≤ Xscale n)
    (hEX : ∀ᶠ n in atTop, ∀ i, E (u i n) ≤ Xscale n)
    (Pweight : Nat)
    (hweight : ∀ a,
      (∑ i, abs
        (coefficientwiseLeastWeight
          (centralLaurentWeight (centralTransferShear d))
          (cert.source a) i : Real)) ≤ (Pweight : Real))
    (hcoefficient : ∀ a e, e ∈ (cert.source a).support →
      HasPolynomialUpperBound atTop Rscale (coefficientValue a e))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u d x))
    (hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d jets x))
    (hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n => realCentralTransferCoordinateError (jets n) x))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n =
        ∑ a, centralCoefficient b a n *
          realJetCoefficientwiseCentralEvaluation A d (coefficientValue a)
            u (cert.source a) n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetCoefficientwiseSourceEvaluation d (coefficientValue a)
          u jets (cert.source a) n =
        ∑ j, sourceCoefficient a j n * originalGenerator j n)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient) :
    HasInversePowerLowerBound atTop Xscale originalGenerator := by
  let omega : RealJetTransferIndex m d → Fin (m + 1) → Int :=
    centralLaurentWeight (centralTransferShear d)
  let supportedValue : Fin cert.count →
      (RealJetTransferIndex m d →₀ Nat) → Nat → Real :=
    fun a => supportedCoefficientValue (cert.source a) (coefficientValue a)
  let perturbed : RealJetTransferIndex m d → Nat → Real :=
    realJetPerturbedAssignment u d jets
  let main : RealJetTransferIndex m d → Nat → Real :=
    realJetMainAssignment A u d
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hR.mono (fun _ hn => one_le_two.trans hn)
  have hu0 : ∀ᶠ n in atTop, ∀ i, 0 ≤ u i n :=
    Filter.Eventually.of_forall (fun n i => (hu n i).le)
  have hsupportedCoefficient : ∀ a e,
      HasPolynomialUpperBound atTop Rscale (supportedValue a e) := by
    intro a e
    exact supportedCoefficientValue_hasPolynomialUpperBound
      (cert.source a) (coefficientValue a) (hcoefficient a) e
  have hcoordinateDifference : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n => perturbed x n - main x n) := by
    intro x
    apply (hcoordinateError x).congr
    intro n
    exact (realCentralTransferPerturbedValue_sub_main
      A (fun i => u i n) d (jets n) x).symm
  have hinitial : ∀ a,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n =>
          finiteSupportInitialEvaluation omega (cert.source a)
              (fun e => supportedValue a e n) (fun x => perturbed x n) -
            finiteSupportInitialEvaluation omega (cert.source a)
              (fun e => supportedValue a e n) (fun x => main x n)) := by
    intro a
    exact finiteSupportInitialEvaluation_sub_superpolynomialDecay
      hRone omega (cert.source a) (supportedValue a)
      perturbed main (fun e he => hsupportedCoefficient a e)
      hperturbedBound hmainBound hcoordinateDifference
  have htailPolynomial : ∀ a e,
      HasPolynomialUpperBound atTop Rscale
        (fun n => coefficientwiseTailMultiplier (cert.source a)
          (supportedValue a) perturbed e n) := by
    intro a e
    exact coefficientwiseTailMultiplier_hasPolynomialUpperBound
      (cert.source a) (supportedValue a) perturbed e
      (hsupportedCoefficient a e) hperturbedBound
  choose Ctail hCtail Ptail htailBound using
    fun p : Fin cert.count × (RealJetTransferIndex m d →₀ Nat) =>
      htailPolynomial p.1 p.2
  have hcentralIdentity' : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n =
        ∑ a, centralCoefficient b a n *
          coefficientwiseCentralValue omega (cert.source a)
            (supportedValue a) main n := by
    filter_upwards [hcentralIdentity] with n hn
    intro b
    calc
      centralGenerator b n =
          ∑ a, centralCoefficient b a n *
            realJetCoefficientwiseCentralEvaluation A d (coefficientValue a)
              u (cert.source a) n := hn b
      _ = ∑ a, centralCoefficient b a n *
          coefficientwiseCentralValue omega (cert.source a)
            (supportedValue a) main n := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [coefficientwiseCentralValue_eq_realJetCoefficientwiseCentralEvaluation]
        exact congrArg (fun t => centralCoefficient b a n * t)
          (finiteSupportInitialEvaluation_supportedCoefficientValue
            omega (cert.source a) (coefficientValue a) main n).symm
  have hsourceIdentity' : ∀ᶠ n in atTop, ∀ a,
      coefficientwiseWeightedSourceValue omega (cert.source a)
          (supportedValue a) perturbed u n =
        ∑ j, sourceCoefficient a j n * originalGenerator j n := by
    filter_upwards [hsourceIdentity] with n hn
    intro a
    calc
      coefficientwiseWeightedSourceValue omega (cert.source a)
          (supportedValue a) perturbed u n =
        realJetCoefficientwiseSourceEvaluation d (supportedValue a)
          u jets (cert.source a) n :=
        coefficientwiseWeightedSourceValue_eq_realJetCoefficientwiseSourceEvaluation
          hA d (supportedValue a) u hu jets (cert.source a) n
      _ = realJetCoefficientwiseSourceEvaluation d (coefficientValue a)
          u jets (cert.source a) n :=
        finiteSupportPolynomialEvaluation_supportedCoefficientValue
          (cert.source a) (coefficientValue a)
            (realJetActualAssignment u d jets) n
      _ = ∑ j, sourceCoefficient a j n * originalGenerator j n := hn a
  exact coefficientwiseWeightedQuantitativeTransfer
    (Canonical := Fin cert.count) (Central := Central) (Original := Original)
    omega cert.source supportedValue perturbed main u Rscale Xscale
      centralGenerator centralCoefficient originalGenerator sourceCoefficient
      horder hpos hR hratios hscale hRX hX hu0 hEX Pweight hweight
      hinitial (fun a e => Ctail (a, e)) (fun a e => Ptail (a, e))
      (fun a e he => (hCtail (a, e)).le)
      (fun a e he => htailBound (a, e))
      hcentralIdentity' hcentralCoefficient hcentralLower
      hsourceIdentity' hsourceCoefficient

/-! ## Analytic representatives on the finite supports -/

/-- Analytic coefficient representatives are polynomially bounded along a
convergent parameter sequence, with quantification restricted to the actual
supports of a finite polynomial family. -/
theorem analyticFiniteSupportCoefficientFamily_hasPolynomialUpperBound
    {R : Type u} [CommRing R]
    {κ σ : Type*} {Param : Type v}
    [NormedAddCommGroup Param] [NormedSpace Real Param]
    (polynomial : κ → MvPolynomial σ R)
    (coefficientRepresentative : κ → (σ →₀ Nat) → Param → Real)
    (w : Nat → Param) (x₀ : Param) (U : Set Param) (hx₀U : x₀ ∈ U)
    (hw : Tendsto w atTop (𝓝 x₀))
    (hanalytic : ∀ a e, e ∈ (polynomial a).support →
      AnalyticOnNhd Real (coefficientRepresentative a e) U)
    (S : Nat → Real) :
    ∀ a e, e ∈ (polynomial a).support →
      HasPolynomialUpperBound atTop S
        (fun n => coefficientRepresentative a e (w n)) := by
  intro a e he
  exact HasPolynomialUpperBound.of_analyticOnNhd_comp
    hx₀U (hanalytic a e he) hw

/-- Fully analytic version of support-local real quantitative transfer.

The source-polynomial coefficients and both generator-change matrices are
given by analytic representatives on a common neighborhood.  Only the
source coefficients lying in the selected finite supports are required to
be analytic.  This is the interface produced by
`exists_analyticPolynomialRepresentatives` for polynomials over analytic
germs; it does not require evaluation of the entire germ ring at points away
from the base point.
-/
theorem CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer_of_analyticRepresentatives
    {R : Type u} [CommRing R] {m : Nat}
    (d : Fin (m + 1) → Nat)
    (I : Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (cert : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    [Nonempty (Fin cert.count)]
    {A : Real → Real} (hA : IsAbel A)
    {Param : Type v} [NormedAddCommGroup Param] [NormedSpace Real Param]
    (w : Nat → Param) (x₀ : Param) (U : Set Param) (hx₀U : x₀ ∈ U)
    (hw : Tendsto w atTop (𝓝 x₀))
    (coefficientRepresentative : Fin cert.count →
      (RealJetTransferIndex m d →₀ Nat) → Param → Real)
    (hcoefficientAnalytic : ∀ a e, e ∈ (cert.source a).support →
      AnalyticOnNhd Real (coefficientRepresentative a e) U)
    (u : Fin (m + 1) → Nat → Real)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (Rscale Xscale : Nat → Real)
    {Central Original : Type v}
    [Fintype Central] [Nonempty Central]
    [Fintype Original] [Nonempty Original]
    (centralGenerator : Central → Nat → Real)
    (centralCoefficient : Central → Fin cert.count → Param → Real)
    (originalGenerator : Original → Nat → Real)
    (sourceCoefficient : Fin cert.count → Original → Param → Real)
    (hcentralCoefficientAnalytic : ∀ b a,
      AnalyticOnNhd Real (centralCoefficient b a) U)
    (hsourceCoefficientAnalytic : ∀ a j,
      AnalyticOnNhd Real (sourceCoefficient a j) U)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last m) n)
    (hR : ∀ᶠ n in atTop, 2 ≤ Rscale n)
    (hratios : ∀ i : Fin m,
      Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto
      (fun n => u (Fin.last m) n / Real.log (Rscale n)) atTop atTop)
    (hRX : ∀ᶠ n in atTop, Rscale n ≤ Xscale n)
    (hX : ∀ᶠ n in atTop, 2 ≤ Xscale n)
    (hEX : ∀ᶠ n in atTop, ∀ i, E (u i n) ≤ Xscale n)
    (Pweight : Nat)
    (hweight : ∀ a,
      (∑ i, abs
        (coefficientwiseLeastWeight
          (centralLaurentWeight (centralTransferShear d))
          (cert.source a) i : Real)) ≤ (Pweight : Real))
    (hmainBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetMainAssignment A u d x))
    (hperturbedBound : ∀ x,
      HasPolynomialUpperBound atTop Rscale
        (realJetPerturbedAssignment u d jets x))
    (hcoordinateError : ∀ x,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n => realCentralTransferCoordinateError (jets n) x))
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n =
        ∑ a, centralCoefficient b a (w n) *
          realJetCoefficientwiseCentralEvaluation A d
            (fun e n => coefficientRepresentative a e (w n))
            u (cert.source a) n)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetCoefficientwiseSourceEvaluation d
          (fun e n => coefficientRepresentative a e (w n))
          u jets (cert.source a) n =
        ∑ j, sourceCoefficient a j (w n) * originalGenerator j n) :
    HasInversePowerLowerBound atTop Xscale originalGenerator := by
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hR.mono (fun _ hn => one_le_two.trans hn)
  have hXone : ∀ᶠ n in atTop, 1 ≤ Xscale n :=
    hX.mono (fun _ hn => one_le_two.trans hn)
  have hcoefficient :=
    analyticFiniteSupportCoefficientFamily_hasPolynomialUpperBound
      cert.source coefficientRepresentative w x₀ U hx₀U hw
        hcoefficientAnalytic Rscale
  have hcentralCoefficient :=
    analyticCoefficientMatrix_hasUniformPolynomialUpperBound
      centralCoefficient hx₀U hcentralCoefficientAnalytic hw hRone
  have hsourceCoefficient :=
    analyticCoefficientMatrix_hasUniformPolynomialUpperBound
      sourceCoefficient hx₀U hsourceCoefficientAnalytic hw hXone
  exact
    CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer_coefficientwise
      d I cert hA
      (fun a e n => coefficientRepresentative a e (w n))
      u hu jets Rscale Xscale centralGenerator
      (fun b a n => centralCoefficient b a (w n)) originalGenerator
      (fun a j n => sourceCoefficient a j (w n))
      horder hpos hR hratios hscale hRX hX hEX Pweight hweight
      hcoefficient hmainBound hperturbedBound hcoordinateError
      hcentralIdentity hcentralCoefficient hcentralLower
      hsourceIdentity hsourceCoefficient

end AbelFormalization
