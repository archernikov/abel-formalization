import AbelFormalization.TransferScaleHierarchy
import AbelFormalization.WeightedGroupEvaluation
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Exact weighted evaluation expansion

This file isolates the finite algebra behind the quantitative-transfer
identity.  A multiplicative character of an additive weight group evaluates a
variable of weight `omega i` at the character value of that weight times a
normalized value.  After multiplying a polynomial by the inverse character
of its least lexicographic weight, its evaluation is exactly the evaluation
of its least-weight form plus a finite tail.  Every index in that tail carries
a strictly positive lexicographic weight difference.

The final specialization takes the character to be
`nu ↦ exp (-nu dot u)`.  It is deliberately independent of the coefficient
ring and of the meaning of the normalized variable values.  In the transfer
argument those values may therefore be either the exact central jets or the
central jets plus the Hermite remainder.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open scoped BigOperators

variable {R A sigma G : Type*}
variable [CommRing R] [CommRing A] [AddCommGroup G]

/-! ## Characters of additive weight groups -/

/-- Evaluate an additive group element under a multiplicative character. -/
def additiveCharacterValue (chi : Multiplicative G →* A) (gamma : G) : A :=
  chi (Multiplicative.ofAdd gamma)

@[simp]
theorem additiveCharacterValue_zero (chi : Multiplicative G →* A) :
    additiveCharacterValue chi (0 : G) = 1 := by
  exact chi.map_one

theorem additiveCharacterValue_add (chi : Multiplicative G →* A)
    (gamma delta : G) :
    additiveCharacterValue chi (gamma + delta) =
      additiveCharacterValue chi gamma * additiveCharacterValue chi delta := by
  exact chi.map_mul (Multiplicative.ofAdd gamma) (Multiplicative.ofAdd delta)

@[simp]
theorem additiveCharacterValue_neg_mul_self (chi : Multiplicative G →* A)
    (gamma : G) :
    additiveCharacterValue chi (-gamma) * additiveCharacterValue chi gamma = 1 := by
  rw [← additiveCharacterValue_add]
  simp

@[simp]
theorem additiveCharacterValue_mul_neg_self (chi : Multiplicative G →* A)
    (gamma : G) :
    additiveCharacterValue chi gamma * additiveCharacterValue chi (-gamma) = 1 := by
  rw [← additiveCharacterValue_add]
  simp

theorem additiveCharacterValue_nsmul (chi : Multiplicative G →* A)
    (n : Nat) (gamma : G) :
    additiveCharacterValue chi (n • gamma) =
      additiveCharacterValue chi gamma ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, additiveCharacterValue_add, ih, pow_succ]

theorem additiveCharacterValue_finset_sum {kappa : Type*}
    (chi : Multiplicative G →* A) (s : Finset kappa) (gamma : kappa → G) :
    additiveCharacterValue chi (∑ i ∈ s, gamma i) =
      ∏ i ∈ s, additiveCharacterValue chi (gamma i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, additiveCharacterValue_add, ih]

/-- A character sends an additive monomial weight to the corresponding
finite product of character powers. -/
theorem additiveCharacterValue_finsupp_weight
    (chi : Multiplicative G →* A) (omega : sigma → G)
    (d : sigma →₀ Nat) :
    additiveCharacterValue chi (Finsupp.weight omega d) =
      d.prod (fun i n => additiveCharacterValue chi (omega i) ^ n) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
  rw [additiveCharacterValue_finset_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact additiveCharacterValue_nsmul chi (d i) (omega i)

/-- Scaling each variable by the character of its weight extracts the
character of the whole monomial weight. -/
theorem finsupp_prod_character_scaled
    (chi : Multiplicative G →* A) (omega : sigma → G)
    (y : sigma → A) (d : sigma →₀ Nat) :
    d.prod (fun i n =>
      (y i * additiveCharacterValue chi (omega i)) ^ n) =
      d.prod (fun i n => y i ^ n) *
        additiveCharacterValue chi (Finsupp.weight omega d) := by
  classical
  rw [additiveCharacterValue_finsupp_weight]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]

/-! ## The finite lexicographic tail -/

variable {h : Nat}

/-- The vector difference between a monomial's weight and the actual least
lexicographic weight of the polynomial. -/
def lexicographicWeightDifference (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) (d : sigma →₀ Nat) : Fin h → Int :=
  Finsupp.weight omega d - ofLex (lexicographicMinimumWeight omega f)

/-- The finite set of supported monomials whose weight is not the least
weight.  Membership in this set will be strengthened to a strict
lexicographic inequality below. -/
def lexicographicTailSupport (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) : Finset (sigma →₀ Nat) :=
  f.support.filter (fun d =>
    Finsupp.weight (fun i => toLex (omega i)) d ≠
      lexicographicMinimumWeight omega f)

theorem mem_lexicographicTailSupport_iff (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) (d : sigma →₀ Nat) :
    d ∈ lexicographicTailSupport omega f ↔
      d ∈ f.support ∧
        Finsupp.weight (fun i => toLex (omega i)) d ≠
          lexicographicMinimumWeight omega f := by
  classical
  simp [lexicographicTailSupport]

/-- Converting the vector difference back to the lexicographically ordered
group gives literal subtraction of the two lexicographic weights. -/
theorem toLex_lexicographicWeightDifference (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) (d : sigma →₀ Nat) :
    toLex (lexicographicWeightDifference omega f d) =
      Finsupp.weight (fun i => toLex (omega i)) d -
        lexicographicMinimumWeight omega f := by
  apply ofLex.injective
  change Finsupp.weight omega d -
      ofLex (lexicographicMinimumWeight omega f) =
    ofLex (Finsupp.weight (fun i => toLex (omega i)) d) -
      ofLex (lexicographicMinimumWeight omega f)
  rw [lexicographicWeight_ofLex]

/-- Every tail index has a positive lexicographic weight difference.  This is
the exact order fact consumed by the separated-scale exponential estimate. -/
theorem lexicographicWeightDifference_pos_of_mem_tail
    (omega : sigma → Fin h → Int) (f : MvPolynomial sigma R)
    {d : sigma →₀ Nat} (hd : d ∈ lexicographicTailSupport omega f) :
    0 < toLex (lexicographicWeightDifference omega f d) := by
  classical
  obtain ⟨hdsupp, hdne⟩ :=
    (mem_lexicographicTailSupport_iff omega f d).mp hd
  have hle := lexicographicMinimumWeight_le omega f hdsupp
  have hlt : lexicographicMinimumWeight omega f <
      Finsupp.weight (fun i => toLex (omega i)) d :=
    lt_of_le_of_ne hle (Ne.symm hdne)
  rw [toLex_lexicographicWeightDifference, sub_pos]
  exact hlt

/-- Direct compatibility with the separated-scale estimate: every
exponential attached to a tail monomial has superpolynomial decay. -/
theorem lexicographicTailExponential_superpolynomialDecay
    (omega : sigma → Fin (h + 1) → Int) (f : MvPolynomial sigma R)
    {d : sigma →₀ Nat} (hd : d ∈ lexicographicTailSupport omega f)
    (u : Fin (h + 1) → Nat → Real) (S : Nat → Real)
    (horder : ∀ᶠ n in Filter.atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in Filter.atTop, 0 < u (Fin.last h) n)
    (hS : ∀ᶠ n in Filter.atTop, 2 ≤ S n)
    (hratios : ∀ i : Fin h, Filter.Tendsto
      (fun n => u i.castSucc n / u i.succ n) Filter.atTop Filter.atTop)
    (hscale : Filter.Tendsto
      (fun n => u (Fin.last h) n / Real.log (S n))
      Filter.atTop Filter.atTop) :
    Asymptotics.SuperpolynomialDecay Filter.atTop S
      (fun n => Real.exp (-lexicographicDot
        (lexicographicWeightDifference omega f d) (fun i => u i n))) := by
  exact lexicographicExponential_superpolynomialDecay
    (lexicographicWeightDifference omega f d) u S
    (lexicographicWeightDifference_pos_of_mem_tail omega f hd)
    horder hpos hS hratios hscale

/-- The polynomial made of all supported monomials strictly above the least
weight. -/
def lexicographicTailPolynomial (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) : MvPolynomial sigma R :=
  ∑ d ∈ lexicographicTailSupport omega f,
    MvPolynomial.monomial d (f.coeff d)

/-- A polynomial is the sum of its actual least lexicographic form and its
finite tail. -/
theorem lexicographicInitialForm_add_tail (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) :
    f = lexicographicInitialForm omega f +
      lexicographicTailPolynomial omega f := by
  classical
  let p : (sigma →₀ Nat) → Prop := fun d =>
    Finsupp.weight (fun i => toLex (omega i)) d =
      lexicographicMinimumWeight omega f
  calc
    f = ∑ d ∈ f.support, MvPolynomial.monomial d (f.coeff d) :=
      MvPolynomial.as_sum f
    _ = (∑ d ∈ f.support with p d,
          MvPolynomial.monomial d (f.coeff d)) +
        ∑ d ∈ f.support with ¬ p d,
          MvPolynomial.monomial d (f.coeff d) := by
      exact (Finset.sum_filter_add_sum_filter_not f.support p
        (fun d => MvPolynomial.monomial d (f.coeff d))).symm
    _ = lexicographicInitialForm omega f +
        lexicographicTailPolynomial omega f := by
      rw [lexicographicInitialForm,
        MvPolynomial.weightedHomogeneousComponent_apply]
      rfl

/-! ## Coefficientwise finite-support evaluation -/

/-- Evaluation written only in terms of a fixed finite support, arbitrary
coefficient values, and arbitrary variable values.  Unlike `eval₂Hom`, this
does not require the coefficient values to extend to a ring homomorphism.
This is the form used for independently chosen analytic-germ
representatives. -/
def finiteSupportPolynomialEvaluation
    (f : MvPolynomial sigma R) (a : (sigma →₀ Nat) → A)
    (y : sigma → A) : A :=
  ∑ d ∈ f.support, a d * d.prod (fun i n => y i ^ n)

/-- The coefficientwise evaluation restricted to the actual least-weight
support. -/
def finiteSupportInitialEvaluation (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) (a : (sigma →₀ Nat) → A)
    (y : sigma → A) : A :=
  ∑ d ∈ f.support with
      Finsupp.weight (fun i => toLex (omega i)) d =
        lexicographicMinimumWeight omega f,
    a d * d.prod (fun i n => y i ^ n)

/-- Coefficientwise finite-support evaluation agrees with `eval₂Hom` when
the coefficient values come from a ring homomorphism. -/
theorem finiteSupportPolynomialEvaluation_eq_eval₂Hom
    (c : R →+* A) (f : MvPolynomial sigma R) (y : sigma → A) :
    finiteSupportPolynomialEvaluation f (fun d => c (f.coeff d)) y =
      MvPolynomial.eval₂Hom c y f := by
  have h := congrArg (MvPolynomial.eval₂Hom c y)
    (MvPolynomial.support_sum_monomial_coeff f)
  simpa only [finiteSupportPolynomialEvaluation, map_sum,
    MvPolynomial.eval₂Hom_monomial] using h

/-- The analogous coefficientwise description of the least-weight initial
form. -/
theorem finiteSupportInitialEvaluation_eq_eval₂Hom_initial
    (c : R →+* A) (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) (y : sigma → A) :
    finiteSupportInitialEvaluation omega f (fun d => c (f.coeff d)) y =
      MvPolynomial.eval₂Hom c y (lexicographicInitialForm omega f) := by
  have h := congrArg (MvPolynomial.eval₂Hom c y)
    (MvPolynomial.weightedHomogeneousComponent_apply
      (w := fun i => toLex (omega i))
      (lexicographicMinimumWeight omega f) f)
  simpa only [finiteSupportInitialEvaluation, lexicographicInitialForm,
    map_sum, MvPolynomial.eval₂Hom_monomial] using h.symm

/-- Exact normalized monomial identity with arbitrary coefficient values. -/
theorem normalized_character_scaled_monomial
    (chi : Multiplicative G →* A) (omega : sigma → G)
    (lambda : G) (a : A) (y : sigma → A) (d : sigma →₀ Nat) :
    additiveCharacterValue chi (-lambda) *
        (a * d.prod (fun i n =>
          (y i * additiveCharacterValue chi (omega i)) ^ n)) =
      additiveCharacterValue chi (Finsupp.weight omega d - lambda) *
        (a * d.prod (fun i n => y i ^ n)) := by
  rw [finsupp_prod_character_scaled]
  calc
    additiveCharacterValue chi (-lambda) *
        (a * (d.prod (fun i n => y i ^ n) *
          additiveCharacterValue chi (Finsupp.weight omega d))) =
      (additiveCharacterValue chi (-lambda) *
          additiveCharacterValue chi (Finsupp.weight omega d)) *
        (a * d.prod (fun i n => y i ^ n)) := by
      ac_rfl
    _ = additiveCharacterValue chi
          (-lambda + Finsupp.weight omega d) *
        (a * d.prod (fun i n => y i ^ n)) := by
      rw [additiveCharacterValue_add]
    _ = additiveCharacterValue chi (Finsupp.weight omega d - lambda) *
        (a * d.prod (fun i n => y i ^ n)) := by
      rw [sub_eq_add_neg, add_comm]

/-- Fully coefficientwise normalized expansion.  This is the most general
exact statement in the file: the coefficient evaluator is an arbitrary map,
so pointwise analytic representatives can be substituted directly. -/
theorem normalized_character_finiteSupportEvaluation_eq_initial_add_tail
    (chi : Multiplicative (Fin h → Int) →* A)
    (omega : sigma → Fin h → Int) (f : MvPolynomial sigma R)
    (a : (sigma →₀ Nat) → A) (y : sigma → A) :
    additiveCharacterValue chi
        (-ofLex (lexicographicMinimumWeight omega f)) *
      finiteSupportPolynomialEvaluation f a
        (fun i => y i * additiveCharacterValue chi (omega i)) =
      finiteSupportInitialEvaluation omega f a y +
        ∑ d ∈ lexicographicTailSupport omega f,
          additiveCharacterValue chi (lexicographicWeightDifference omega f d) *
            (a d * d.prod (fun i n => y i ^ n)) := by
  classical
  let p : (sigma →₀ Nat) → Prop := fun d =>
    Finsupp.weight (fun i => toLex (omega i)) d =
      lexicographicMinimumWeight omega f
  simp only [finiteSupportPolynomialEvaluation, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not f.support p
    (fun d => additiveCharacterValue chi
      (-ofLex (lexicographicMinimumWeight omega f)) *
        (a d * d.prod (fun i n =>
          (y i * additiveCharacterValue chi (omega i)) ^ n)))]
  congr 1
  · simp only [finiteSupportInitialEvaluation]
    apply Finset.sum_congr rfl
    intro d hd
    have hdweight : Finsupp.weight omega d =
        ofLex (lexicographicMinimumWeight omega f) := by
      calc
        Finsupp.weight omega d =
            ofLex (Finsupp.weight (fun i => toLex (omega i)) d) :=
          (lexicographicWeight_ofLex omega d).symm
        _ = ofLex (lexicographicMinimumWeight omega f) :=
          congrArg ofLex (Finset.mem_filter.mp hd).2
    rw [normalized_character_scaled_monomial, hdweight, sub_self]
    simp
  · change (∑ d ∈ lexicographicTailSupport omega f,
        additiveCharacterValue chi
            (-ofLex (lexicographicMinimumWeight omega f)) *
          (a d * d.prod (fun i n =>
            (y i * additiveCharacterValue chi (omega i)) ^ n))) = _
    apply Finset.sum_congr rfl
    intro d hd
    exact normalized_character_scaled_monomial chi omega
      (ofLex (lexicographicMinimumWeight omega f)) (a d) y d

/-! ## Evaluation through an abstract weight character -/

/-- Evaluate a polynomial at normalized values multiplied by the character
of their weights.  The group-algebra factorization makes the monomial weight
visible without requiring the ambient variable type to be finite. -/
def weightedCharacterEvaluation (c : R →+* A)
    (chi : Multiplicative G →* A) (y : sigma → A) (omega : sigma → G) :
    MvPolynomial sigma R →+* A :=
  (AddMonoidAlgebra.lift A A G chi).toRingHom.comp
    (weightedGroupEvaluation c y omega)

@[simp]
theorem weightedCharacterEvaluation_monomial (c : R →+* A)
    (chi : Multiplicative G →* A) (y : sigma → A) (omega : sigma → G)
    (d : sigma →₀ Nat) (r : R) :
    weightedCharacterEvaluation c chi y omega (MvPolynomial.monomial d r) =
      MvPolynomial.eval₂Hom c y (MvPolynomial.monomial d r) *
        additiveCharacterValue chi (Finsupp.weight omega d) := by
  simp [weightedCharacterEvaluation, additiveCharacterValue,
    Algebra.smul_def]

/-- The group-algebra definition is ordinary multivariate evaluation at the
character-scaled variable values. -/
theorem weightedCharacterEvaluation_eq_eval₂Hom (c : R →+* A)
    (chi : Multiplicative G →* A) (y : sigma → A) (omega : sigma → G) :
    weightedCharacterEvaluation c chi y omega =
      MvPolynomial.eval₂Hom c
        (fun i => y i * additiveCharacterValue chi (omega i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [weightedCharacterEvaluation]
  · intro i
    simp [weightedCharacterEvaluation, additiveCharacterValue,
      Algebra.smul_def]

/-- Normalizing one monomial by an arbitrary weight `lambda` replaces its
character factor by the character of `weight - lambda`. -/
theorem normalized_weightedCharacterEvaluation_monomial
    (c : R →+* A) (chi : Multiplicative G →* A)
    (y : sigma → A) (omega : sigma → G) (lambda : G)
    (d : sigma →₀ Nat) (r : R) :
    additiveCharacterValue chi (-lambda) *
        weightedCharacterEvaluation c chi y omega
          (MvPolynomial.monomial d r) =
      additiveCharacterValue chi (Finsupp.weight omega d - lambda) *
        MvPolynomial.eval₂Hom c y (MvPolynomial.monomial d r) := by
  rw [weightedCharacterEvaluation_monomial]
  calc
    additiveCharacterValue chi (-lambda) *
        (MvPolynomial.eval₂Hom c y (MvPolynomial.monomial d r) *
          additiveCharacterValue chi (Finsupp.weight omega d)) =
      (additiveCharacterValue chi (-lambda) *
          additiveCharacterValue chi (Finsupp.weight omega d)) *
        MvPolynomial.eval₂Hom c y (MvPolynomial.monomial d r) := by
      ac_rfl
    _ = additiveCharacterValue chi
          (-lambda + Finsupp.weight omega d) *
        MvPolynomial.eval₂Hom c y (MvPolynomial.monomial d r) := by
      rw [additiveCharacterValue_add]
    _ = additiveCharacterValue chi (Finsupp.weight omega d - lambda) *
        MvPolynomial.eval₂Hom c y (MvPolynomial.monomial d r) := by
      rw [sub_eq_add_neg, add_comm]

/-- Normalization cancels the character on a homogeneous polynomial. -/
theorem normalized_weightedCharacterEvaluation_of_homogeneous
    (c : R →+* A) (chi : Multiplicative G →* A)
    (y : sigma → A) (omega : sigma → G) (lambda : G)
    {f : MvPolynomial sigma R}
    (hf : f.IsWeightedHomogeneous omega lambda) :
    additiveCharacterValue chi (-lambda) *
        weightedCharacterEvaluation c chi y omega f =
      MvPolynomial.eval₂Hom c y f := by
  rw [weightedCharacterEvaluation,
    RingHom.comp_apply,
    weightedGroupEvaluation_of_homogeneous c y omega hf]
  change additiveCharacterValue chi (-lambda) *
      AddMonoidAlgebra.lift A A G chi
        (AddMonoidAlgebra.single lambda (MvPolynomial.eval₂Hom c y f)) = _
  rw [AddMonoidAlgebra.lift_single, Algebra.smul_def]
  calc
    additiveCharacterValue chi (-lambda) *
        (MvPolynomial.eval₂Hom c y f * additiveCharacterValue chi lambda) =
      (additiveCharacterValue chi (-lambda) *
          additiveCharacterValue chi lambda) *
        MvPolynomial.eval₂Hom c y f := by
      ac_rfl
    _ = MvPolynomial.eval₂Hom c y f := by simp

/-- Exact normalized evaluation of the finite tail. -/
theorem normalized_weightedCharacterEvaluation_tail
    (c : R →+* A) (chi : Multiplicative (Fin h → Int) →* A)
    (y : sigma → A) (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) :
    additiveCharacterValue chi
        (-ofLex (lexicographicMinimumWeight omega f)) *
      weightedCharacterEvaluation c chi y omega
        (lexicographicTailPolynomial omega f) =
      ∑ d ∈ lexicographicTailSupport omega f,
        additiveCharacterValue chi (lexicographicWeightDifference omega f d) *
          MvPolynomial.eval₂Hom c y
            (MvPolynomial.monomial d (f.coeff d)) := by
  classical
  simp only [lexicographicTailPolynomial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact normalized_weightedCharacterEvaluation_monomial c chi y omega
    (ofLex (lexicographicMinimumWeight omega f)) d (f.coeff d)

/-- The generic exact expansion.  Its tail is finite and each tail term is
tagged by `lexicographicWeightDifference`; the preceding positivity theorem
shows that every such tag is lexicographically positive. -/
theorem normalized_weightedCharacterEvaluation_eq_initial_add_tail
    (c : R →+* A) (chi : Multiplicative (Fin h → Int) →* A)
    (y : sigma → A) (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) :
    additiveCharacterValue chi
        (-ofLex (lexicographicMinimumWeight omega f)) *
      weightedCharacterEvaluation c chi y omega f =
      MvPolynomial.eval₂Hom c y (lexicographicInitialForm omega f) +
        ∑ d ∈ lexicographicTailSupport omega f,
          additiveCharacterValue chi (lexicographicWeightDifference omega f d) *
            MvPolynomial.eval₂Hom c y
              (MvPolynomial.monomial d (f.coeff d)) := by
  calc
    additiveCharacterValue chi
          (-ofLex (lexicographicMinimumWeight omega f)) *
        weightedCharacterEvaluation c chi y omega f =
        additiveCharacterValue chi
            (-ofLex (lexicographicMinimumWeight omega f)) *
          weightedCharacterEvaluation c chi y omega
            (lexicographicInitialForm omega f +
              lexicographicTailPolynomial omega f) := by
          rw [← lexicographicInitialForm_add_tail omega f]
    _ = additiveCharacterValue chi
            (-ofLex (lexicographicMinimumWeight omega f)) *
          weightedCharacterEvaluation c chi y omega
            (lexicographicInitialForm omega f) +
        additiveCharacterValue chi
            (-ofLex (lexicographicMinimumWeight omega f)) *
          weightedCharacterEvaluation c chi y omega
            (lexicographicTailPolynomial omega f) := by
          rw [map_add, mul_add]
    _ = MvPolynomial.eval₂Hom c y (lexicographicInitialForm omega f) +
        ∑ d ∈ lexicographicTailSupport omega f,
          additiveCharacterValue chi (lexicographicWeightDifference omega f d) *
            MvPolynomial.eval₂Hom c y
              (MvPolynomial.monomial d (f.coeff d)) := by
          rw [normalized_weightedCharacterEvaluation_of_homogeneous c chi y omega
            (ofLex (lexicographicMinimumWeight omega f))
            (lexicographicInitialForm_isWeightedHomogeneous omega f),
            normalized_weightedCharacterEvaluation_tail]

/-! ## The exponential character -/

theorem lexicographicDot_add (gamma delta : Fin h → Int) (u : Fin h → Real) :
    lexicographicDot (gamma + delta) u =
      lexicographicDot gamma u + lexicographicDot delta u := by
  simp [lexicographicDot, add_mul, Finset.sum_add_distrib]

@[simp]
theorem lexicographicDot_neg (gamma : Fin h → Int) (u : Fin h → Real) :
    lexicographicDot (-gamma) u = -lexicographicDot gamma u := by
  simp [lexicographicDot, Finset.sum_neg_distrib]

/-- The real multiplicative character `gamma |-> exp (-gamma dot u)`. -/
def realLexicographicExponentialCharacter (u : Fin h → Real) :
    Multiplicative (Fin h → Int) →* Real where
  toFun gamma := Real.exp (-lexicographicDot gamma.toAdd u)
  map_one' := by simp [lexicographicDot]
  map_mul' gamma delta := by
    change Real.exp (-lexicographicDot (gamma.toAdd + delta.toAdd) u) =
      Real.exp (-lexicographicDot gamma.toAdd u) *
        Real.exp (-lexicographicDot delta.toAdd u)
    rw [lexicographicDot_add, neg_add, Real.exp_add]

@[simp]
theorem realLexicographicExponentialCharacter_apply
    (u : Fin h → Real) (gamma : Fin h → Int) :
    realLexicographicExponentialCharacter u (Multiplicative.ofAdd gamma) =
      Real.exp (-lexicographicDot gamma u) := rfl

/-- The same exponential character in an arbitrary commutative real algebra.
In particular, this supplies both the real and complex evaluations needed by
the transfer argument. -/
def lexicographicExponentialCharacter
    (A : Type*) [CommRing A] [Algebra Real A] (u : Fin h → Real) :
    Multiplicative (Fin h → Int) →* A :=
  (algebraMap Real A).toMonoidHom.comp
    (realLexicographicExponentialCharacter u)

@[simp]
theorem additiveCharacterValue_lexicographicExponentialCharacter
    (A : Type*) [CommRing A] [Algebra Real A]
    (u : Fin h → Real) (gamma : Fin h → Int) :
    additiveCharacterValue (lexicographicExponentialCharacter A u) gamma =
      algebraMap Real A (Real.exp (-lexicographicDot gamma u)) := rfl

/-- Exponential specialization of the fully coefficientwise expansion.  The
map `a` can be the pointwise values of independently chosen coefficient-germ
representatives. -/
theorem normalized_exponential_finiteSupportEvaluation_eq_initial_add_tail
    [Algebra Real A]
    (omega : sigma → Fin h → Int) (f : MvPolynomial sigma R)
    (a : (sigma →₀ Nat) → A) (y : sigma → A) (u : Fin h → Real) :
    algebraMap Real A
        (Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight omega f)) u)) *
      finiteSupportPolynomialEvaluation f a
        (fun i => y i * algebraMap Real A
          (Real.exp (-lexicographicDot (omega i) u))) =
      finiteSupportInitialEvaluation omega f a y +
        ∑ d ∈ lexicographicTailSupport omega f,
          algebraMap Real A
              (Real.exp (-lexicographicDot
                (lexicographicWeightDifference omega f d) u)) *
            (a d * d.prod (fun i n => y i ^ n)) := by
  simpa only [additiveCharacterValue_lexicographicExponentialCharacter,
    lexicographicDot_neg, neg_neg] using
    (normalized_character_finiteSupportEvaluation_eq_initial_add_tail
      (lexicographicExponentialCharacter A u) omega f a y)

/-- Concrete exponential version of the generic expansion.  This is the
finite-support identity used before applying lexicographic superpolynomial
decay to each tail summand. -/
theorem normalized_exponential_eval₂_eq_initial_add_tail
    [Algebra Real A]
    (c : R →+* A) (y : sigma → A) (omega : sigma → Fin h → Int)
    (f : MvPolynomial sigma R) (u : Fin h → Real) :
    algebraMap Real A
        (Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight omega f)) u)) *
      MvPolynomial.eval₂Hom c
        (fun i => y i * algebraMap Real A
          (Real.exp (-lexicographicDot (omega i) u))) f =
      MvPolynomial.eval₂Hom c y (lexicographicInitialForm omega f) +
        ∑ d ∈ lexicographicTailSupport omega f,
          algebraMap Real A
              (Real.exp (-lexicographicDot
                (lexicographicWeightDifference omega f d) u)) *
            MvPolynomial.eval₂Hom c y
              (MvPolynomial.monomial d (f.coeff d)) := by
  simpa only [weightedCharacterEvaluation_eq_eval₂Hom,
    additiveCharacterValue_lexicographicExponentialCharacter,
    lexicographicDot_neg, neg_neg] using
    (normalized_weightedCharacterEvaluation_eq_initial_add_tail
      c (lexicographicExponentialCharacter A u) y omega f)

/-- A second exact form exposes the error caused by replacing the normalized
values `y` by target central values `z`.  The first error is now a plain
polynomial-evaluation perturbation, while every term in the remaining finite
sum still has a positive lexicographic exponential factor. -/
theorem normalized_exponential_eval₂_eq_base_add_errors
    [Algebra Real A]
    (c : R →+* A) (y z : sigma → A)
    (omega : sigma → Fin h → Int) (f : MvPolynomial sigma R)
    (u : Fin h → Real) :
    algebraMap Real A
        (Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight omega f)) u)) *
      MvPolynomial.eval₂Hom c
        (fun i => y i * algebraMap Real A
          (Real.exp (-lexicographicDot (omega i) u))) f =
      MvPolynomial.eval₂Hom c z (lexicographicInitialForm omega f) +
        (MvPolynomial.eval₂Hom c y (lexicographicInitialForm omega f) -
          MvPolynomial.eval₂Hom c z (lexicographicInitialForm omega f)) +
        ∑ d ∈ lexicographicTailSupport omega f,
          algebraMap Real A
              (Real.exp (-lexicographicDot
                (lexicographicWeightDifference omega f d) u)) *
            MvPolynomial.eval₂Hom c y
              (MvPolynomial.monomial d (f.coeff d)) := by
  rw [normalized_exponential_eval₂_eq_initial_add_tail]
  ring

end AbelFormalization
