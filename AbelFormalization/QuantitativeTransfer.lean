import AbelFormalization.TransferInitialCertificate
import AbelFormalization.TransferWeightedExpansion
import AbelFormalization.TransferFiniteBounds
import AbelFormalization.TransferLowerBoundTransport

/-!
# Assembly of the quantitative transfer argument

This file packages the part of the manuscript's quantitative-reduction lemma
which follows from the finite initial-form certificate, the exact weighted
expansion, lexicographic exponential decay, and elementary lower-bound
transport.

There are two public layers.

* `quantitativeTransfer_of_normalizedExpansion` is the abstract finite-family
  theorem.  It starts from identities

      `normalization a n * source a n = central a n + error a n`

  and performs both changes of finite generating family, absorbs the rapidly
  decaying error, changes from the central scale to the source scale, and
  removes the normalization.

* `coefficientwiseWeightedQuantitativeTransfer` obtains the preceding error
  from the exact finite-support weighted expansion.  Strictly higher
  lexicographic weights supply the rapidly decaying exponential factors.  All
  remaining factors are required to satisfy explicit polynomial bounds.

The direct polynomial-growth hypotheses are intentional.  Positivity of an
unchanged auxiliary argument `rho` does not imply a polynomial bound for an
expression involving `rho` when `rho` can approach zero.  A later concrete
application may derive the hypotheses from `rho -> infinity`, compactness of
coefficient parameters, and the analytic jet estimates, but this theorem does
not silently infer them from positivity alone.

The last section bundles the algebraic output of
`exists_centralTransferGeneratingFamily`.  It records that the finite family
used by the analytic theorem consists of actual translated source elements
and that its normalized central images generate the literal central ideal.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Finset Set
open scoped BigOperators Topology

/-! ## Eventual replacement of a finite family -/

variable {X iota : Type*}

/-- The inverse-power lower-bound predicate only depends on the eventual
pointwise values of a finite family. -/
theorem hasInversePowerLowerBound_of_eventuallyEq
    [Fintype iota] [Nonempty iota]
    {l : Filter X} {S : X -> Real} {f g : iota -> X -> Real}
    (hfg : ∀ᶠ x in l, ∀ i, f i x = g i x)
    (hf : HasInversePowerLowerBound l S f) :
    HasInversePowerLowerBound l S g := by
  obtain ⟨c, hc, M, hf⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hf, hfg] with x hx hxeq
  have hmax : finiteFamilyMaxAbs f x = finiteFamilyMaxAbs g x := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := exists_abs_eq_finiteFamilyMaxAbs f x
      rw [← hi, hxeq i]
      exact abs_le_finiteFamilyMaxAbs g x i
    · obtain ⟨i, hi⟩ := exists_abs_eq_finiteFamilyMaxAbs g x
      rw [← hi, ← hxeq i]
      exact abs_le_finiteFamilyMaxAbs f x i
  calc
    c / (S x) ^ M <= finiteFamilyMaxAbs f x := hx
    _ = finiteFamilyMaxAbs g x := hmax

/-- Symmetric eventual replacement, exposed as an iff for convenient use
with exact evaluation identities. -/
theorem hasInversePowerLowerBound_eventuallyEq_iff
    [Fintype iota] [Nonempty iota]
    {l : Filter X} {S : X -> Real} {f g : iota -> X -> Real}
    (hfg : ∀ᶠ x in l, ∀ i, f i x = g i x) :
    HasInversePowerLowerBound l S f ↔ HasInversePowerLowerBound l S g := by
  constructor
  · exact hasInversePowerLowerBound_of_eventuallyEq hfg
  · exact hasInversePowerLowerBound_of_eventuallyEq
      (hfg.mono (fun x hx i => (hx i).symm))

/-! ## The abstract quantitative-transfer endpoint -/

variable {Canonical Central Original : Type*}

/-- The complete numerical core of the manuscript's quantitative-reduction
lemma.

`centralGenerator` and `originalGenerator` may be arbitrary fixed generating
lists.  The two displayed coefficient matrices encode their evaluated ideal
membership identities relative to the compatible canonical family.  Their
polynomial upper bounds are hypotheses, rather than consequences of mere
positivity of auxiliary arguments.

This theorem is independent of the origin of `error`.  The next section
constructs it from the exact weighted polynomial expansion. -/
theorem quantitativeTransfer_of_normalizedExpansion
    [Fintype Canonical] [Nonempty Canonical]
    [Fintype Central] [Nonempty Central]
    [Fintype Original] [Nonempty Original]
    {l : Filter X} {Rscale Xscale : X -> Real}
    (source central error normalization : Canonical -> X -> Real)
    (centralGenerator : Central -> X -> Real)
    (centralCoefficient : Central -> Canonical -> X -> Real)
    (originalGenerator : Original -> X -> Real)
    (sourceCoefficient : Canonical -> Original -> X -> Real)
    (hR : ∀ᶠ x in l, 1 <= Rscale x)
    (hRX : ∀ᶠ x in l, Rscale x <= Xscale x)
    (hcentralIdentity : ∀ᶠ x in l, ∀ b,
      centralGenerator b x =
        ∑ a, centralCoefficient b a x * central a x)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound l Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound l Rscale centralGenerator)
    (hexpansion : ∀ᶠ x in l, ∀ a,
      normalization a x * source a x = central a x + error a x)
    (herror : ∀ a,
      Asymptotics.SuperpolynomialDecay l Rscale (error a))
    {Cnormalization : Real} (hCnormalization : 0 < Cnormalization)
    {Pnormalization : Nat}
    (hnormalization : ∀ᶠ x in l, ∀ a,
      abs (normalization a x) <=
        Cnormalization * (Xscale x) ^ Pnormalization)
    (hsourceIdentity : ∀ᶠ x in l, ∀ a,
      source a x =
        ∑ j, sourceCoefficient a j x * originalGenerator j x)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound l Xscale sourceCoefficient) :
    HasInversePowerLowerBound l Xscale originalGenerator := by
  have hcentral : HasInversePowerLowerBound l Rscale central :=
    hasInversePowerLowerBound_of_linearCombinations
      central centralGenerator centralCoefficient hR hcentralIdentity
        hcentralCoefficient hcentralLower
  have hcentralError : HasInversePowerLowerBound l Rscale
      (fun a x => central a x + error a x) :=
    hasInversePowerLowerBound_add_superpolynomialPerturbation
      central error hR herror hcentral
  have hnormalized : HasInversePowerLowerBound l Rscale
      (fun a x => normalization a x * source a x) :=
    hasInversePowerLowerBound_of_eventuallyEq
      (hexpansion.mono (fun x hx a => (hx a).symm)) hcentralError
  have hsource : HasInversePowerLowerBound l Xscale source :=
    hasInversePowerLowerBound_of_normalization_and_scale
      source normalization hR hRX hCnormalization hnormalization hnormalized
  have hX : ∀ᶠ x in l, 1 <= Xscale x := by
    filter_upwards [hR, hRX] with x hxR hxRX
    exact hxR.trans hxRX
  exact hasInversePowerLowerBound_of_linearCombinations
    originalGenerator source sourceCoefficient hX hsourceIdentity
      hsourceCoefficient hsource

/-! ## Coefficientwise weighted evaluation -/

variable {Coeff Sigma : Type*} [CommRing Coeff]
variable {h : Nat}

/-- The actual least-weight vector of a polynomial. -/
def coefficientwiseLeastWeight
    (omega : Sigma -> Fin (h + 1) -> Int)
    (f : MvPolynomial Sigma Coeff) : Fin (h + 1) -> Int :=
  ofLex (lexicographicMinimumWeight omega f)

/-- Evaluation at variables split into a normalized value and their
exponential weight.  The coefficient values are arbitrary functions on the
finite monomial support, so independently chosen analytic-germ
representatives may be used. -/
def coefficientwiseWeightedSourceValue
    (omega : Sigma -> Fin (h + 1) -> Int)
    (f : MvPolynomial Sigma Coeff)
    (coefficientValue : (Sigma →₀ Nat) -> Nat -> Real)
    (normalizedValue : Sigma -> Nat -> Real)
    (u : Fin (h + 1) -> Nat -> Real) (n : Nat) : Real :=
  finiteSupportPolynomialEvaluation f (fun d => coefficientValue d n)
    (fun i => normalizedValue i n *
      Real.exp (-lexicographicDot (omega i) (fun k => u k n)))

/-- Evaluation of the least-weight part at the target central values. -/
def coefficientwiseCentralValue
    (omega : Sigma -> Fin (h + 1) -> Int)
    (f : MvPolynomial Sigma Coeff)
    (coefficientValue : (Sigma →₀ Nat) -> Nat -> Real)
    (centralValue : Sigma -> Nat -> Real) (n : Nat) : Real :=
  finiteSupportInitialEvaluation omega f (fun d => coefficientValue d n)
    (fun i => centralValue i n)

/-- The non-exponential factor attached to one discarded monomial.  Its
polynomial upper bound is the precise substitute for the manuscript's
insufficient positivity-only condition on unchanged arguments. -/
def coefficientwiseTailMultiplier
    (f : MvPolynomial Sigma Coeff)
    (coefficientValue : (Sigma →₀ Nat) -> Nat -> Real)
    (normalizedValue : Sigma -> Nat -> Real)
    (d : Sigma →₀ Nat) (n : Nat) : Real :=
  coefficientValue d n * d.prod (fun i m => normalizedValue i n ^ m)

/-- The exact error: perturbation of the least-weight evaluation plus the
finite strictly-higher-weight tail. -/
def coefficientwiseTransferError
    (omega : Sigma -> Fin (h + 1) -> Int)
    (f : MvPolynomial Sigma Coeff)
    (coefficientValue : (Sigma →₀ Nat) -> Nat -> Real)
    (normalizedValue centralValue : Sigma -> Nat -> Real)
    (u : Fin (h + 1) -> Nat -> Real) (n : Nat) : Real :=
  (finiteSupportInitialEvaluation omega f (fun d => coefficientValue d n)
      (fun i => normalizedValue i n) -
    finiteSupportInitialEvaluation omega f (fun d => coefficientValue d n)
      (fun i => centralValue i n)) +
    ∑ d ∈ lexicographicTailSupport omega f,
      Real.exp (-lexicographicDot
        (lexicographicWeightDifference omega f d) (fun k => u k n)) *
          coefficientwiseTailMultiplier f coefficientValue normalizedValue d n

/-- Pointwise form of the manuscript identity
`exp (lambda dot u) f = g + epsilon`. -/
theorem coefficientwiseWeightedSourceValue_expansion
    (omega : Sigma -> Fin (h + 1) -> Int)
    (f : MvPolynomial Sigma Coeff)
    (coefficientValue : (Sigma →₀ Nat) -> Nat -> Real)
    (normalizedValue centralValue : Sigma -> Nat -> Real)
    (u : Fin (h + 1) -> Nat -> Real) (n : Nat) :
    Real.exp (lexicographicDot (coefficientwiseLeastWeight omega f)
        (fun k => u k n)) *
      coefficientwiseWeightedSourceValue omega f coefficientValue
        normalizedValue u n =
    coefficientwiseCentralValue omega f coefficientValue centralValue n +
      coefficientwiseTransferError omega f coefficientValue normalizedValue
        centralValue u n := by
  calc
    Real.exp (lexicographicDot (coefficientwiseLeastWeight omega f)
          (fun k => u k n)) *
        coefficientwiseWeightedSourceValue omega f coefficientValue
          normalizedValue u n =
      finiteSupportInitialEvaluation omega f (fun d => coefficientValue d n)
          (fun i => normalizedValue i n) +
        ∑ d ∈ lexicographicTailSupport omega f,
          Real.exp (-lexicographicDot
            (lexicographicWeightDifference omega f d) (fun k => u k n)) *
              coefficientwiseTailMultiplier f coefficientValue
                normalizedValue d n := by
      simpa [coefficientwiseLeastWeight, coefficientwiseWeightedSourceValue,
        coefficientwiseTailMultiplier] using
        (normalized_exponential_finiteSupportEvaluation_eq_initial_add_tail
          (A := Real) omega f (fun d => coefficientValue d n)
            (fun i => normalizedValue i n) (fun k => u k n))
    _ = coefficientwiseCentralValue omega f coefficientValue centralValue n +
        coefficientwiseTransferError omega f coefficientValue normalizedValue
          centralValue u n := by
      simp only [coefficientwiseCentralValue, coefficientwiseTransferError]
      ring

/-- The error in the coefficientwise expansion is superpolynomially small.

The least-weight perturbation is supplied separately; the future jet bridge
proves it from the exact Abel/Hermite identities.  For the discarded tail we
require a polynomial bound on every remaining monomial factor.  Since the
support is finite, no uniform exponent across different monomials is needed.
-/
theorem coefficientwiseTransferError_superpolynomialDecay
    (omega : Sigma -> Fin (h + 1) -> Int)
    (f : MvPolynomial Sigma Coeff)
    (coefficientValue : (Sigma →₀ Nat) -> Nat -> Real)
    (normalizedValue centralValue : Sigma -> Nat -> Real)
    (u : Fin (h + 1) -> Nat -> Real) (Rscale : Nat -> Real)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last h) n)
    (hR : ∀ᶠ n in atTop, 2 <= Rscale n)
    (hratios : ∀ i : Fin h,
      Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto
      (fun n => u (Fin.last h) n / Real.log (Rscale n)) atTop atTop)
    (hinitial : Asymptotics.SuperpolynomialDecay atTop Rscale
      (fun n =>
        finiteSupportInitialEvaluation omega f
            (fun d => coefficientValue d n) (fun i => normalizedValue i n) -
          finiteSupportInitialEvaluation omega f
            (fun d => coefficientValue d n) (fun i => centralValue i n)))
    (C : (Sigma →₀ Nat) -> Real) (P : (Sigma →₀ Nat) -> Nat)
    (hC : ∀ d ∈ lexicographicTailSupport omega f, 0 <= C d)
    (hpoly : ∀ d ∈ lexicographicTailSupport omega f,
      ∀ᶠ n in atTop,
        abs (coefficientwiseTailMultiplier f coefficientValue
          normalizedValue d n) <= C d * (Rscale n) ^ P d) :
    Asymptotics.SuperpolynomialDecay atTop Rscale
      (coefficientwiseTransferError omega f coefficientValue normalizedValue
        centralValue u) := by
  have htail : Asymptotics.SuperpolynomialDecay atTop Rscale
      (fun n => ∑ d ∈ lexicographicTailSupport omega f,
        Real.exp (-lexicographicDot
          (lexicographicWeightDifference omega f d) (fun k => u k n)) *
            coefficientwiseTailMultiplier f coefficientValue
              normalizedValue d n) := by
    apply superpolynomialDecay_finset_sum_mul_of_polynomialBound
      (lexicographicTailSupport omega f)
      (fun d n => Real.exp (-lexicographicDot
        (lexicographicWeightDifference omega f d) (fun k => u k n)))
      (fun d n => coefficientwiseTailMultiplier f coefficientValue
        normalizedValue d n) (C := C) (P := P)
    · intro d hd
      exact lexicographicTailExponential_superpolynomialDecay
        omega f hd u Rscale horder hpos hR hratios hscale
    · exact hR.mono (fun n hn => (zero_le_two.trans hn))
    · exact hC
    · exact hpoly
  exact (hinitial.add htail).congr (fun n => by
    rfl)

/-! ## The assembled coefficientwise theorem -/

/-- Quantitative reduction for a finite family of weighted polynomials.

This is the strongest statement obtainable from the four imported modules
without building the Abel/Hermite coordinate bridge into this file.  It
derives all higher-weight errors from the scale hierarchy, absorbs the
least-weight perturbation, performs the central and source generator changes,
and concludes at the larger source scale.

The hypotheses `htailBound`, `hcentralCoefficient`, and `hsourceCoefficient`
are the explicit polynomial-growth assumptions.  In a concrete application
they include every coefficient germ, retained variable, unchanged argument,
jet, and Hermite remainder occurring in the displayed finite identities.
-/
theorem coefficientwiseWeightedQuantitativeTransfer
    [Fintype Canonical] [Nonempty Canonical]
    [Fintype Central] [Nonempty Central]
    [Fintype Original] [Nonempty Original]
    (omega : Sigma -> Fin (h + 1) -> Int)
    (polynomial : Canonical -> MvPolynomial Sigma Coeff)
    (coefficientValue : Canonical -> (Sigma →₀ Nat) -> Nat -> Real)
    (normalizedValue centralVariableValue : Sigma -> Nat -> Real)
    (u : Fin (h + 1) -> Nat -> Real)
    (Rscale Xscale : Nat -> Real)
    (centralGenerator : Central -> Nat -> Real)
    (centralCoefficient : Central -> Canonical -> Nat -> Real)
    (originalGenerator : Original -> Nat -> Real)
    (sourceCoefficient : Canonical -> Original -> Nat -> Real)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last h) n)
    (hR : ∀ᶠ n in atTop, 2 <= Rscale n)
    (hratios : ∀ i : Fin h,
      Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto
      (fun n => u (Fin.last h) n / Real.log (Rscale n)) atTop atTop)
    (hRX : ∀ᶠ n in atTop, Rscale n <= Xscale n)
    (hX : ∀ᶠ n in atTop, 2 <= Xscale n)
    (hu0 : ∀ᶠ n in atTop, ∀ i, 0 <= u i n)
    (hEX : ∀ᶠ n in atTop, ∀ i, E (u i n) <= Xscale n)
    (Pweight : Nat)
    (hweight : ∀ a,
      (∑ i, abs (coefficientwiseLeastWeight omega (polynomial a) i : Real)) <=
        (Pweight : Real))
    (hinitial : ∀ a,
      Asymptotics.SuperpolynomialDecay atTop Rscale
        (fun n =>
          finiteSupportInitialEvaluation omega (polynomial a)
              (fun d => coefficientValue a d n)
              (fun i => normalizedValue i n) -
            finiteSupportInitialEvaluation omega (polynomial a)
              (fun d => coefficientValue a d n)
              (fun i => centralVariableValue i n)))
    (Ctail : Canonical -> (Sigma →₀ Nat) -> Real)
    (Ptail : Canonical -> (Sigma →₀ Nat) -> Nat)
    (hCtail : ∀ a d,
      d ∈ lexicographicTailSupport omega (polynomial a) ->
        0 <= Ctail a d)
    (htailBound : ∀ a d,
      d ∈ lexicographicTailSupport omega (polynomial a) ->
        ∀ᶠ n in atTop,
          abs (coefficientwiseTailMultiplier (polynomial a)
            (coefficientValue a) normalizedValue d n) <=
              Ctail a d * (Rscale n) ^ Ptail a d)
    (hcentralIdentity : ∀ᶠ n in atTop, ∀ b,
      centralGenerator b n = ∑ a, centralCoefficient b a n *
        coefficientwiseCentralValue omega (polynomial a)
          (coefficientValue a) centralVariableValue n)
    (hcentralCoefficient :
      HasUniformPolynomialUpperBound atTop Rscale centralCoefficient)
    (hcentralLower :
      HasInversePowerLowerBound atTop Rscale centralGenerator)
    (hsourceIdentity : ∀ᶠ n in atTop, ∀ a,
      coefficientwiseWeightedSourceValue omega (polynomial a)
          (coefficientValue a) normalizedValue u n =
        ∑ j, sourceCoefficient a j n * originalGenerator j n)
    (hsourceCoefficient :
      HasUniformPolynomialUpperBound atTop Xscale sourceCoefficient) :
    HasInversePowerLowerBound atTop Xscale originalGenerator := by
  let source : Canonical -> Nat -> Real := fun a =>
    coefficientwiseWeightedSourceValue omega (polynomial a)
      (coefficientValue a) normalizedValue u
  let central : Canonical -> Nat -> Real := fun a =>
    coefficientwiseCentralValue omega (polynomial a)
      (coefficientValue a) centralVariableValue
  let error : Canonical -> Nat -> Real := fun a =>
    coefficientwiseTransferError omega (polynomial a)
      (coefficientValue a) normalizedValue centralVariableValue u
  let normalization : Canonical -> Nat -> Real := fun a n =>
    Real.exp (lexicographicDot
      (coefficientwiseLeastWeight omega (polynomial a)) (fun i => u i n))
  have hRone : ∀ᶠ n in atTop, 1 <= Rscale n :=
    hR.mono (fun n hn => one_le_two.trans hn)
  have hexpansion : ∀ᶠ n in atTop, ∀ a,
      normalization a n * source a n = central a n + error a n := by
    exact Filter.Eventually.of_forall (fun n a =>
      coefficientwiseWeightedSourceValue_expansion omega (polynomial a)
        (coefficientValue a) normalizedValue centralVariableValue u n)
  have herror : ∀ a,
      Asymptotics.SuperpolynomialDecay atTop Rscale (error a) := by
    intro a
    exact coefficientwiseTransferError_superpolynomialDecay
      omega (polynomial a) (coefficientValue a) normalizedValue
        centralVariableValue u Rscale horder hpos hR hratios hscale
        (hinitial a) (Ctail a) (Ptail a)
        (fun d hd => hCtail a d hd) (fun d hd => htailBound a d hd)
  have hnormalization : ∀ᶠ n in atTop, ∀ a,
      abs (normalization a n) <= 1 * (Xscale n) ^ (2 * Pweight) := by
    filter_upwards
      [eventually_abs_exp_lexicographicDot_le_sourceScale
        (fun a => coefficientwiseLeastWeight omega (polynomial a)) u Xscale
          Pweight hX hu0 hEX hweight] with n hn
    intro a
    simpa only [normalization, one_mul] using hn a
  exact quantitativeTransfer_of_normalizedExpansion
    source central error normalization centralGenerator centralCoefficient
      originalGenerator sourceCoefficient hRone hRX
      (by simpa only [central] using hcentralIdentity)
      hcentralCoefficient hcentralLower hexpansion herror
      (Cnormalization := 1) one_pos hnormalization
      (by simpa only [source] using hsourceIdentity) hsourceCoefficient

/-! ## Algebraic certificate selected by Noetherianity -/

universe u v w

/-- The exact algebraic family to which the coefficientwise theorem is
applied.  The four fields after `source` are the four algebraic assertions
needed in the manuscript: membership in the translated source ideal,
generation of the full initial ideal, generation of the Laurent contraction,
and generation of the literal central ideal after `Phi`. -/
structure CentralQuantitativeTransferCertificate
    (R : Type u) [CommRing R]
    (Block : Type v) (Time : Type w) (d : Block -> Nat) (h : Nat)
    (omega : CentralPolynomialIndex Block d Time -> Fin h -> Int)
    (I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) where
  count : Nat
  source : Fin count -> MvPolynomial
    (Fin h ⊕ CentralPolynomialIndex Block d Time) R
  source_mem : ∀ a, source a ∈ I.map
    (polynomialCoordinateTranslation
      (Sum.elim (fun _ : Fin h => (-1 : R))
        (fun _ : CentralPolynomialIndex Block d Time => 0))).toRingHom
  initial_span : Ideal.span (Set.range (fun a =>
      lexicographicInitialForm (centralLaurentWeight omega) (source a))) =
    lexicographicInitialIdeal (centralLaurentWeight omega)
      (I.map (polynomialCoordinateTranslation
        (Sum.elim (fun _ : Fin h => (-1 : R))
          (fun _ : CentralPolynomialIndex Block d Time => 0))).toRingHom)
  normalized_span : Ideal.span (Set.range (fun a =>
      centralNormalizedInitialPolynomial omega (source a))) =
    centralShiftedLaurentContraction omega I
  central_span : Ideal.span (Set.range (fun a =>
      centralPolynomialPhi R Block d Time
        (centralNormalizedInitialPolynomial omega (source a)))) =
    centralIdealConstruction omega I

/-- Noetherianity supplies a compatible algebraic certificate.  The theorem
does not assert that `count` is positive: the zero ideal may legitimately
have an empty generating family.  Any application with an inverse-power
lower bound for the central ideal can separately rule out that degenerate
case before invoking a finite-family maximum theorem. -/
theorem exists_centralQuantitativeTransferCertificate
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Block : Type v} {Time : Type w} [Finite Block] [Finite Time]
    {d : Block -> Nat} {h : Nat}
    (omega : CentralPolynomialIndex Block d Time -> Fin h -> Int)
    (I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) :
    Nonempty (CentralQuantitativeTransferCertificate
      R Block Time d h omega I) := by
  obtain ⟨n, f, hf, hinitial, hnormalized, hcentral⟩ :=
    exists_centralTransferGeneratingFamily omega I
  exact ⟨{
    count := n
    source := f
    source_mem := hf
    initial_span := hinitial
    normalized_span := hnormalized
    central_span := hcentral }⟩

end AbelFormalization
