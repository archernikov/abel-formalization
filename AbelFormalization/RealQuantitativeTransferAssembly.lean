import AbelFormalization.RealTransferJetSubstitution
import AbelFormalization.TransferPolynomialPerturbation
import AbelFormalization.TransferCoefficientBounds
import AbelFormalization.QuantitativeTransfer

/-!
# Real jet substitution assembled with quantitative transfer

This file connects the real derivative/Hermite jet substitution to the
finite-family quantitative transfer theorem.  The coefficient ring is
evaluated by a ring homomorphism into real sequences.  This is the interface
required by the existing structural polynomial-perturbation theorem.

All growth assumptions are stated in the scale in which they are used.
In particular, no estimate is inferred from positivity of an unchanged
auxiliary argument.  Polynomial bounds for the normalized coordinates,
coefficient values, and the two generator-change matrices are hypotheses;
the final theorem below derives the matrix bounds from analytic
representatives along a convergent parameter sequence.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v

/-! ## Pointwise evaluation of coefficient-valued sequences -/

/-- Evaluation at one index, composed with a coefficient homomorphism into
real sequences. -/
def coefficientEvaluationAt {R : Type u} [CommRing R]
    (c : R →+* (Nat → Real)) (n : Nat) : R →+* Real :=
  (Pi.evalRingHom (fun _ : Nat => Real) n).comp c

@[simp]
theorem coefficientEvaluationAt_apply {R : Type u} [CommRing R]
    (c : R →+* (Nat → Real)) (n : Nat) (r : R) :
    coefficientEvaluationAt c n r = c r n := rfl

/-- Evaluation of a multivariate polynomial in a function ring is
pointwise evaluation through the corresponding coefficient homomorphism. -/
theorem mvPolynomial_eval₂Hom_pi_apply
    {R S X sigma : Type*} [CommRing R] [CommRing S]
    (c : R →+* (X → S)) (y : sigma → X → S)
    (p : MvPolynomial sigma R) (x : X) :
    MvPolynomial.eval₂Hom c y p x =
      MvPolynomial.eval₂Hom
        ((Pi.evalRingHom (fun _ : X => S) x).comp c)
        (fun i => y i x) p := by
  let ev : (X → S) →+* S := Pi.evalRingHom (fun _ : X => S) x
  have hhom :
      ev.comp (MvPolynomial.eval₂Hom c y) =
        MvPolynomial.eval₂Hom (ev.comp c) (fun i => y i x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ev]
    · intro i
      simp [ev]
  change ev (MvPolynomial.eval₂Hom c y p) =
    MvPolynomial.eval₂Hom (ev.comp c) (fun i => y i x) p
  exact RingHom.congr_fun hhom p

/-! ## The three concrete sequence-valued assignments -/

/-- Full variable type of an `m + 1`-scale central transfer problem. -/
abbrev RealJetTransferIndex (m : Nat) (d : Fin (m + 1) → Nat) :=
  Fin (m + 1) ⊕
    CentralPolynomialIndex (Fin (m + 1)) d (Fin (m + 1))

/-- The normalized source coordinates, including the projected Hermite
errors, as real sequences. -/
def realJetPerturbedAssignment {m : Nat} {A : Real → Real}
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    RealJetTransferIndex m d → Nat → Real :=
  fun x n => realCentralTransferPerturbedValue A (fun i => u i n) d (jets n) x

/-- The error-free normalized central assignment as real sequences. -/
def realJetMainAssignment {m : Nat} (A : Real → Real)
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat) :
    RealJetTransferIndex m d → Nat → Real :=
  fun x n => realCentralTransferMainValue A (fun i => u i n) d x

/-- Literal source coordinates before weight normalization as real
sequences. -/
def realJetActualAssignment {m : Nat} {A : Real → Real}
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    RealJetTransferIndex m d → Nat → Real :=
  fun x n => realCentralTransferActualValue A (fun i => u i n) d (jets n) x

/-- Literal evaluation of a source polynomial at the derivative/Hermite
coordinates. -/
def realJetSourceEvaluation {R : Type u} [CommRing R]
    {m : Nat} {A : Real → Real}
    (c : R →+* (Nat → Real))
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) : Real :=
  MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
    (fun x => realJetActualAssignment u d jets x n) f

/-- Evaluation of the canonical central polynomial selected from a source
polynomial by normalized initial form and `Phi`. -/
def realJetCentralEvaluation {R : Type u} [CommRing R]
    {m : Nat} (A : Real → Real)
    (c : R →+* (Nat → Real))
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat)
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) : Real :=
  MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
    (realCentralTransferCentralValue A (fun i => u i n) d)
    (centralPolynomialPhi R (Fin (m + 1)) d (Fin (m + 1))
      (centralNormalizedInitialPolynomial (centralTransferShear d) f))

/-! ## Compatibility with the coefficientwise expansion -/

/-- The coefficientwise weighted source value is the literal real
derivative/Hermite evaluation. -/
theorem coefficientwiseWeightedSourceValue_eq_realJetSourceEvaluation
    {R : Type u} [CommRing R] {m : Nat} {A : Real → Real}
    (hA : IsAbel A) (c : R →+* (Nat → Real))
    (u : Fin (m + 1) → Nat → Real)
    (hu : ∀ n i, 0 < u i n) (d : Fin (m + 1) → Nat)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) :
    coefficientwiseWeightedSourceValue
        (centralLaurentWeight (centralTransferShear d)) f
        (fun e n => c (f.coeff e) n)
        (realJetPerturbedAssignment u d jets) u n =
      realJetSourceEvaluation c u d jets f n := by
  change finiteSupportPolynomialEvaluation f
      (fun e => coefficientEvaluationAt c n (f.coeff e))
      (fun x => realJetPerturbedAssignment u d jets x n *
        Real.exp (-lexicographicDot
          (centralLaurentWeight (centralTransferShear d) x)
          (fun i => u i n))) = _
  rw [finiteSupportPolynomialEvaluation_eq_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext x
  exact hA.realCentralTransferPerturbed_scaled_eq_actual
    (fun i => u i n) (hu n) d (jets n) x

/-- The coefficientwise least-weight main term is the literal evaluation of
the canonical `Phi` generator. -/
theorem coefficientwiseCentralValue_eq_realJetCentralEvaluation
    {R : Type u} [CommRing R] {m : Nat} (A : Real → Real)
    (c : R →+* (Nat → Real))
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat)
    (f : MvPolynomial (RealJetTransferIndex m d) R) (n : Nat) :
    coefficientwiseCentralValue
        (centralLaurentWeight (centralTransferShear d)) f
        (fun e n => c (f.coeff e) n)
        (realJetMainAssignment A u d) n =
      realJetCentralEvaluation A c u d f n := by
  change finiteSupportInitialEvaluation
      (centralLaurentWeight (centralTransferShear d)) f
      (fun e => coefficientEvaluationAt c n (f.coeff e))
      (realCentralTransferMainValue A (fun i => u i n) d) = _
  exact finiteSupportInitialEvaluation_realCentralMain_eq_centralGenerator
    (coefficientEvaluationAt c n) A (fun i => u i n) d f

/-- A tail multiplier is the value of its corresponding monomial in the
sequence-valued coefficient ring. -/
theorem coefficientwiseTailMultiplier_realJet_eq_eval₂Hom
    {R : Type u} [CommRing R] {m : Nat} {A : Real → Real}
    (c : R →+* (Nat → Real))
    (u : Fin (m + 1) → Nat → Real) (d : Fin (m + 1) → Nat)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (f : MvPolynomial (RealJetTransferIndex m d) R)
    (e : RealJetTransferIndex m d →₀ Nat) (n : Nat) :
    coefficientwiseTailMultiplier f (fun e n => c (f.coeff e) n)
        (realJetPerturbedAssignment u d jets) e n =
      MvPolynomial.eval₂Hom c (realJetPerturbedAssignment u d jets)
        (MvPolynomial.monomial e (f.coeff e)) n := by
  rw [mvPolynomial_eval₂Hom_pi_apply]
  simp [coefficientwiseTailMultiplier, coefficientEvaluationAt]

/-! ## Quantitative transfer for the algebraic certificate -/

/-- The real quantitative transfer theorem for the finite canonical family
selected by `CentralQuantitativeTransferCertificate`.

The hypotheses `hcoefficient`, `hmainBound`, and `hperturbedBound` are direct
polynomial bounds in `Rscale`.  They cover every analytic coefficient and
every normalized coordinate occurring in the finite expansion.  In
particular, positivity of an auxiliary coordinate is not used as a proxy for
one of these bounds.
-/
theorem CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer
    {R : Type u} [CommRing R] {m : Nat}
    (d : Fin (m + 1) → Nat)
    (I : Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (cert : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    [Nonempty (Fin cert.count)]
    {A : Real → Real} (hA : IsAbel A)
    (c : R →+* (Nat → Real))
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
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop Rscale (c r))
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
          realJetCentralEvaluation A c u d (cert.source a) n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetSourceEvaluation c u d jets (cert.source a) n =
        ∑ j, sourceCoefficient a j n * originalGenerator j n)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient) :
    HasInversePowerLowerBound atTop Xscale originalGenerator := by
  let omega : RealJetTransferIndex m d → Fin (m + 1) → Int :=
    centralLaurentWeight (centralTransferShear d)
  let coefficientValue : Fin cert.count →
      (RealJetTransferIndex m d →₀ Nat) → Nat → Real :=
    fun a e n => c ((cert.source a).coeff e) n
  let perturbed : RealJetTransferIndex m d → Nat → Real :=
    realJetPerturbedAssignment u d jets
  let main : RealJetTransferIndex m d → Nat → Real :=
    realJetMainAssignment A u d
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hR.mono (fun _ hn => one_le_two.trans hn)
  have hu0 : ∀ᶠ n in atTop, ∀ i, 0 ≤ u i n :=
    Filter.Eventually.of_forall (fun n i => (hu n i).le)
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
              (fun e => coefficientValue a e n) (fun x => perturbed x n) -
            finiteSupportInitialEvaluation omega (cert.source a)
              (fun e => coefficientValue a e n) (fun x => main x n)) := by
    intro a
    have hp := mvPolynomial_eval₂Hom_sub_superpolynomialDecay
      hRone c perturbed main hcoefficient hperturbedBound hmainBound
        hcoordinateDifference
        (lexicographicInitialForm omega (cert.source a))
    apply hp.congr
    intro n
    congr 1
    · calc
        (MvPolynomial.eval₂Hom c perturbed
            (lexicographicInitialForm omega (cert.source a))) n =
            MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
              (fun x => perturbed x n)
              (lexicographicInitialForm omega (cert.source a)) :=
          mvPolynomial_eval₂Hom_pi_apply c perturbed _ n
        _ = finiteSupportInitialEvaluation omega (cert.source a)
              (fun e => coefficientValue a e n) (fun x => perturbed x n) := by
          simpa only [coefficientEvaluationAt_apply, coefficientValue] using
            (finiteSupportInitialEvaluation_eq_eval₂Hom_initial
              (coefficientEvaluationAt c n) omega (cert.source a)
                (fun x => perturbed x n)).symm
    · calc
        (MvPolynomial.eval₂Hom c main
            (lexicographicInitialForm omega (cert.source a))) n =
            MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
              (fun x => main x n)
              (lexicographicInitialForm omega (cert.source a)) :=
          mvPolynomial_eval₂Hom_pi_apply c main _ n
        _ = finiteSupportInitialEvaluation omega (cert.source a)
              (fun e => coefficientValue a e n) (fun x => main x n) := by
          simpa only [coefficientEvaluationAt_apply, coefficientValue] using
            (finiteSupportInitialEvaluation_eq_eval₂Hom_initial
              (coefficientEvaluationAt c n) omega (cert.source a)
                (fun x => main x n)).symm
  have htailPolynomial : ∀ a e,
      HasPolynomialUpperBound atTop Rscale
        (fun n => coefficientwiseTailMultiplier (cert.source a)
          (coefficientValue a) perturbed e n) := by
    intro a e
    have hp := mvPolynomial_eval₂Hom_hasPolynomialUpperBound
      hRone c perturbed hcoefficient hperturbedBound
        (MvPolynomial.monomial e ((cert.source a).coeff e))
    apply hp.congr
    intro n
    exact coefficientwiseTailMultiplier_realJet_eq_eval₂Hom
      c u d jets (cert.source a) e n
  choose Ctail hCtail Ptail htailBound using
    fun p : Fin cert.count × (RealJetTransferIndex m d →₀ Nat) =>
      htailPolynomial p.1 p.2
  have hcentralIdentity' : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n =
        ∑ a, centralCoefficient b a n *
          coefficientwiseCentralValue omega (cert.source a)
            (coefficientValue a) main n := by
    filter_upwards [hcentralIdentity] with n hn
    intro b
    calc
      centralGenerator b n =
          ∑ a, centralCoefficient b a n *
            realJetCentralEvaluation A c u d (cert.source a) n := hn b
      _ = ∑ a, centralCoefficient b a n *
          coefficientwiseCentralValue omega (cert.source a)
            (coefficientValue a) main n := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [coefficientwiseCentralValue_eq_realJetCentralEvaluation]
  have hsourceIdentity' : ∀ᶠ n in atTop, ∀ a,
      coefficientwiseWeightedSourceValue omega (cert.source a)
          (coefficientValue a) perturbed u n =
        ∑ j, sourceCoefficient a j n * originalGenerator j n := by
    filter_upwards [hsourceIdentity] with n hn
    intro a
    rw [coefficientwiseWeightedSourceValue_eq_realJetSourceEvaluation
      hA c u hu d jets]
    exact hn a
  exact coefficientwiseWeightedQuantitativeTransfer
    (Canonical := Fin cert.count) (Central := Central) (Original := Original)
    omega cert.source coefficientValue perturbed main u Rscale Xscale
      centralGenerator centralCoefficient originalGenerator sourceCoefficient
      horder hpos hR hratios hscale hRX hX hu0 hEX Pweight hweight
      hinitial (fun a e => Ctail (a, e)) (fun a e => Ptail (a, e))
      (fun a e he => (hCtail (a, e)).le)
      (fun a e he => htailBound (a, e))
      hcentralIdentity' hcentralCoefficient hcentralLower
      hsourceIdentity' hsourceCoefficient

/-! ## Analytic coefficient bounds -/

/-- Analytic representatives of the coefficient homomorphism give all
individual polynomial bounds required by the structural perturbation
theorem.  The equality hypothesis is explicit because arbitrary choices of
representatives of analytic germs need not form a ring homomorphism. -/
theorem coefficientHom_hasPolynomialUpperBound_of_analyticRepresentatives
    {R : Type u} [CommRing R]
    {Param : Type v} [NormedAddCommGroup Param] [NormedSpace Real Param]
    (c : R →+* (Nat → Real)) (coefficientRepresentative : R → Param → Real)
    (w : Nat → Param) (x₀ : Param) (U : Set Param)
    (hx₀U : x₀ ∈ U)
    (hanalytic : ∀ r, AnalyticOnNhd Real (coefficientRepresentative r) U)
    (hw : Tendsto w atTop (𝓝 x₀))
    (hrep : ∀ r n, c r n = coefficientRepresentative r (w n))
    (S : Nat → Real) :
    ∀ r, HasPolynomialUpperBound atTop S (c r) := by
  intro r
  apply (HasPolynomialUpperBound.of_analyticOnNhd_comp
    hx₀U (hanalytic r) hw).congr
  intro n
  exact hrep r n

/-- Analytic generator-change coefficients along a convergent parameter
sequence discharge both uniform matrix bounds in the concrete transfer
theorem. -/
theorem CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer_of_analyticMatrices
    {R : Type u} [CommRing R] {m : Nat}
    (d : Fin (m + 1) → Nat)
    (I : Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (cert : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    [Nonempty (Fin cert.count)]
    {A : Real → Real} (hA : IsAbel A)
    (c : R →+* (Nat → Real))
    (u : Fin (m + 1) → Nat → Real)
    (hu : ∀ n i, 0 < u i n)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (Rscale Xscale : Nat → Real)
    {Central Original : Type v}
    [Fintype Central] [Nonempty Central]
    [Fintype Original] [Nonempty Original]
    {Param : Type*} [NormedAddCommGroup Param] [NormedSpace Real Param]
    (w : Nat → Param) (x₀ : Param) (U : Set Param) (hx₀U : x₀ ∈ U)
    (hw : Tendsto w atTop (𝓝 x₀))
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
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop Rscale (c r))
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
          realJetCentralEvaluation A c u d (cert.source a) n)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      realJetSourceEvaluation c u d jets (cert.source a) n =
        ∑ j, sourceCoefficient a j (w n) * originalGenerator j n) :
    HasInversePowerLowerBound atTop Xscale originalGenerator := by
  have hRone : ∀ᶠ n in atTop, 1 ≤ Rscale n :=
    hR.mono (fun _ hn => one_le_two.trans hn)
  have hXone : ∀ᶠ n in atTop, 1 ≤ Xscale n :=
    hX.mono (fun _ hn => one_le_two.trans hn)
  have hcentralCoefficient :=
    analyticCoefficientMatrix_hasUniformPolynomialUpperBound
      centralCoefficient hx₀U hcentralCoefficientAnalytic hw hRone
  have hsourceCoefficient :=
    analyticCoefficientMatrix_hasUniformPolynomialUpperBound
      sourceCoefficient hx₀U hsourceCoefficientAnalytic hw hXone
  exact CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer
    d I cert hA c u hu jets Rscale Xscale
    centralGenerator (fun b a n => centralCoefficient b a (w n))
    originalGenerator (fun a j n => sourceCoefficient a j (w n))
    horder hpos hR hratios hscale hRX hX hEX Pweight hweight
    hcoefficient hmainBound hperturbedBound hcoordinateError
    hcentralIdentity hcentralCoefficient hcentralLower
    hsourceIdentity hsourceCoefficient

end AbelFormalization
