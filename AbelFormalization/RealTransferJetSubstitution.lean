import AbelFormalization.TransferJetSubstitution

/-!
# Real-valued jet substitutions for quantitative transfer

The quantitative lower-bound modules are formulated over `Real`, whereas the
contour construction naturally produces complex coefficients and remainders.
There is no need to duplicate the lower-bound theory over `Complex`: apply
`Complex.re` to the exact complex identities.

The Hermite source coordinate is the real part of the contour coefficient and
its error is the real part of the complex one-extra-scale remainder.  Exactness
is preserved because every normalizing scalar and every central Stirling jet is
real.  The required error estimate follows from `Complex.abs_re_le_norm` and
the existing complex norm estimate.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open scoped BigOperators

/-! ## Real central jets and coordinate data -/

/-- The real signed-Stirling jet represented by the zero-based coordinate
`r : Fin d`; its derivative order is `r.val + 1`. -/
def realCentralStirlingJet (A : Real → Real) (u : Real) (d : Nat)
    (r : Fin d) : Real :=
  ∑ j ∈ Finset.range (r.val + 2),
    (signedStirling (r.val + 1) j : Real) * iteratedDeriv j A u

@[simp]
theorem centralStirlingJet_re (A : Real → Real) (u : Real) (d : Nat)
    (r : Fin d) :
    (centralStirlingJet A u d r).re = realCentralStirlingJet A u d r := by
  simp [centralStirlingJet, realCentralStirlingJet, Complex.mul_re]

/-- The finite signed-Stirling coordinate change in real scalars. -/
theorem realCentralStirlingJet_eq_fin_sum (A : Real → Real) (u : Real)
    (d : Nat) (r : Fin d) :
    realCentralStirlingJet A u d r =
      ∑ j : Fin d,
        (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : Real)
          else 0) *
        iteratedDeriv (j.val + 1) A u := by
  classical
  unfold realCentralStirlingJet
  rw [Finset.sum_range_succ']
  have hrpos : 1 ≤ r.val + 1 := by omega
  simp only [signedStirling_zero hrpos, Int.cast_zero, zero_mul, add_zero]
  have hfin :
      (∑ j : Fin d,
        (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : Real)
          else 0) *
        iteratedDeriv (j.val + 1) A u) =
      ∑ j ∈ Finset.range d,
        if j ≤ r.val then
          (signedStirling (r.val + 1) (j + 1) : Real) *
            iteratedDeriv (j + 1) A u
        else 0 := by
    simpa using (Fin.sum_univ_eq_sum_range
      (fun j => if j ≤ r.val then
        (signedStirling (r.val + 1) (j + 1) : Real) *
          iteratedDeriv (j + 1) A u
        else 0) d)
  rw [hfin]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range d).filter (fun j => j ≤ r.val) =
        Finset.range (r.val + 1) := by
    ext j
    simp
    omega
  rw [hfilter]

/-- Real data common to the exact derivative and Hermite source-jet modes. -/
structure RealCentralJetSubstitutionData (A : Real → Real) (u : Real)
    (d : Nat) where
  sourceJet : Fin d → Real
  error : Fin d → Real
  normalized_sourceJet : ∀ r,
    Real.exp (((r.val + 1 : Nat) : Real) * u) * sourceJet r =
      realCentralStirlingJet A u d r + error r

/-- Taking real parts sends complex substitution data to exact real
substitution data. -/
def CentralJetSubstitutionData.realPart
    {A : Real → Real} {u : Real} {d : Nat}
    (J : CentralJetSubstitutionData A u d) :
    RealCentralJetSubstitutionData A u d where
  sourceJet r := (J.sourceJet r).re
  error r := (J.error r).re
  normalized_sourceJet r := by
    have h := congrArg Complex.re (J.normalized_sourceJet r)
    have hre :
        (algebraMap Real Complex
          (Real.exp (((r.val + 1 : Nat) : Real) * u))).re =
            Real.exp (((r.val + 1 : Nat) : Real) * u) := by
      change ((Real.exp (((r.val + 1 : Nat) : Real) * u) : Complex)).re = _
      exact Complex.ofReal_re _
    have him :
        (algebraMap Real Complex
          (Real.exp (((r.val + 1 : Nat) : Real) * u))).im = 0 := by
      change ((Real.exp (((r.val + 1 : Nat) : Real) * u) : Complex)).im = 0
      exact Complex.ofReal_im _
    rw [Complex.mul_re, hre, him, zero_mul, sub_zero,
      Complex.add_re, centralStirlingJet_re] at h
    exact h

/-- Exact derivatives give real substitution data with zero error. -/
def IsAbel.realDerivativeJetSubstitutionData {A : Real → Real}
    (hA : IsAbel A) {u : Real} (hu : 0 < u) (d : Nat) :
    RealCentralJetSubstitutionData A u d :=
  (hA.derivativeJetSubstitutionData hu d).realPart

@[simp]
theorem IsAbel.realDerivativeJetSubstitutionData_sourceJet
    {A : Real → Real} (hA : IsAbel A) {u : Real} (hu : 0 < u)
    (d : Nat) (r : Fin d) :
    (hA.realDerivativeJetSubstitutionData hu d).sourceJet r =
      iteratedDeriv (r.val + 1) A (E u) := by
  simp [IsAbel.realDerivativeJetSubstitutionData,
    CentralJetSubstitutionData.realPart,
    IsAbel.derivativeJetSubstitutionData]

@[simp]
theorem IsAbel.realDerivativeJetSubstitutionData_error
    {A : Real → Real} (hA : IsAbel A) {u : Real} (hu : 0 < u)
    (d : Nat) (r : Fin d) :
    (hA.realDerivativeJetSubstitutionData hu d).error r = 0 := by
  simp [IsAbel.realDerivativeJetSubstitutionData,
    CentralJetSubstitutionData.realPart,
    IsAbel.derivativeJetSubstitutionData]

/-- Hermite coefficients give real substitution data by taking the real part
of the exact contour identity.  This construction does not require a separate
Schwarz-reflection theorem for the chosen complex extensions. -/
def FullHermiteLemmaSpec.realHermiteJetSubstitutionData
    {iota : Type*} [Fintype iota] {A : Real → Real} {B : Real}
    {m : iota → Nat} {X0 K K0 u0 epsilon Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 epsilon Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {delta : iota → Complex}
    (hdelta : delta ∈ hermiteNodeNeighborhood B) :
    RealCentralJetSubstitutionData A u d :=
  (H.hermiteJetSubstitutionData d hd hu hdelta).realPart

@[simp]
theorem FullHermiteLemmaSpec.realHermiteJetSubstitutionData_sourceJet
    {iota : Type*} [Fintype iota] {A : Real → Real} {B : Real}
    {m : iota → Nat} {X0 K K0 u0 epsilon Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 epsilon Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {delta : iota → Complex}
    (hdelta : delta ∈ hermiteNodeNeighborhood B) (r : Fin d) :
    (H.realHermiteJetSubstitutionData d hd hu hdelta).sourceJet r =
      (abelHermiteCoeff branch B m (E u) delta (r.val + 1)).re := by
  rfl

@[simp]
theorem FullHermiteLemmaSpec.realHermiteJetSubstitutionData_error
    {iota : Type*} [Fintype iota] {A : Real → Real} {B : Real}
    {m : iota → Nat} {X0 K K0 u0 epsilon Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 epsilon Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {delta : iota → Complex}
    (hdelta : delta ∈ hermiteNodeNeighborhood B) (r : Fin d) :
    (H.realHermiteJetSubstitutionData d hd hu hdelta).error r =
      (algebraMap Real Complex (Real.exp (-u)) *
        centralRemainder F m (1 / 4) (u : Complex)
          (Real.exp (-u) : Complex) delta (r.val + 1)).re := by
  rfl

/-- The projected Hermite error has the same one-extra-scale estimate as the
complex error. -/
theorem FullHermiteLemmaSpec.abs_realHermiteJetSubstitutionData_error_le
    {iota : Type*} [Fintype iota] {A : Real → Real} {B : Real}
    {m : iota → Nat} {X0 K K0 u0 epsilon Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 epsilon Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {delta : iota → Complex}
    (hdelta : delta ∈ hermiteNodeNeighborhood B) (r : Fin d) :
    |(H.realHermiteJetSubstitutionData d hd hu hdelta).error r| ≤
      Real.exp (-u) * (Kr * (1 + u)) := by
  calc
    |(H.realHermiteJetSubstitutionData d hd hu hdelta).error r| =
        |((H.hermiteJetSubstitutionData d hd hu hdelta).error r).re| := rfl
    _ ≤ ‖(H.hermiteJetSubstitutionData d hd hu hdelta).error r‖ :=
      Complex.abs_re_le_norm _
    _ ≤ Real.exp (-u) * (Kr * (1 + u)) :=
      H.norm_hermiteJetSubstitutionData_error_le d hd hu hdelta r

/-! ## Real global coordinate values -/

/-- Raw real central coordinates: positive derivatives at `u_i` and Abel
times at `u_i`. -/
def realCentralTransferCentralValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat) :
    CentralPolynomialIndex (Fin h) d (Fin h) → Real
  | Sum.inl ⟨i, r⟩ => iteratedDeriv (r.val + 1) A (u i)
  | Sum.inr i => A (u i)

/-- The all-main normalized source valuation over `Real`. -/
def realCentralTransferMainValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Real
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl ⟨i, r⟩) => realCentralStirlingJet A (u i) (d i) r
  | Sum.inr (Sum.inr i) => A (u i) + 1

/-- The real coordinate error is zero on `q` and time coordinates. -/
def realCentralTransferCoordinateError {h : Nat} {A : Real → Real}
    {u : Fin h → Real} {d : Fin h → Nat}
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i)) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Real
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl ⟨i, r⟩) => (jets i).error r
  | Sum.inr (Sum.inr _) => 0

/-- The real perturbed normalized valuation. -/
def realCentralTransferPerturbedValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i)) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Real :=
  fun x => realCentralTransferMainValue A u d x +
    realCentralTransferCoordinateError jets x

/-- Literal real source coordinates before weight normalization. -/
def realCentralTransferActualValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i)) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Real
  | Sum.inl i => Real.exp (u i)
  | Sum.inr (Sum.inl ⟨i, r⟩) => (jets i).sourceJet r
  | Sum.inr (Sum.inr i) => A (E (u i))

@[simp]
theorem realCentralTransferPerturbedValue_eq_main_add_error
    {h : Nat} (A : Real → Real) (u : Fin h → Real)
    (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i)) (x) :
    realCentralTransferPerturbedValue A u d jets x =
      realCentralTransferMainValue A u d x +
        realCentralTransferCoordinateError jets x := rfl

@[simp]
theorem realCentralTransferPerturbedValue_sub_main
    {h : Nat} (A : Real → Real) (u : Fin h → Real)
    (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i)) (x) :
    realCentralTransferPerturbedValue A u d jets x -
        realCentralTransferMainValue A u d x =
      realCentralTransferCoordinateError jets x := by
  simp [realCentralTransferPerturbedValue]

theorem real_exp_mul_exp_neg (x : Real) :
    Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add]
  simp

/-- Real character scaling recovers the literal source valuation. -/
theorem IsAbel.realCentralTransferPerturbed_scaled_eq_actual
    {A : Real → Real} (hA : IsAbel A) {h : Nat}
    (u : Fin h → Real) (hu : ∀ i, 0 < u i) (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i)) (x) :
    realCentralTransferPerturbedValue A u d jets x *
        Real.exp (-lexicographicDot
          (centralLaurentWeight (centralTransferShear d) x) u) =
      realCentralTransferActualValue A u d jets x := by
  cases x with
  | inl i =>
      simp [realCentralTransferPerturbedValue,
        realCentralTransferMainValue, realCentralTransferCoordinateError,
        realCentralTransferActualValue]
  | inr x =>
      cases x with
      | inl x =>
          rcases x with ⟨i, r⟩
          rw [lexicographicDot_centralTransfer_block]
          change (realCentralStirlingJet A (u i) (d i) r +
              (jets i).error r) *
                Real.exp (-(((r.val + 1 : Nat) : Real) * u i)) =
            (jets i).sourceJet r
          rw [← (jets i).normalized_sourceJet r]
          calc
            (Real.exp (((r.val + 1 : Nat) : Real) * u i) *
                  (jets i).sourceJet r) *
                Real.exp (-(((r.val + 1 : Nat) : Real) * u i)) =
              (Real.exp (((r.val + 1 : Nat) : Real) * u i) *
                Real.exp (-(((r.val + 1 : Nat) : Real) * u i))) *
                  (jets i).sourceJet r := by ring
            _ = (jets i).sourceJet r := by
              rw [real_exp_mul_exp_neg]
              simp
      | inr i =>
          rw [lexicographicDot_centralTransfer_time]
          simp only [realCentralTransferPerturbedValue,
            realCentralTransferMainValue, realCentralTransferCoordinateError,
            realCentralTransferActualValue, neg_zero, Real.exp_zero, mul_one,
            add_zero]
          exact (hA.abel (u i) (hu i)).symm

/-! ## Identification of the real main term -/

theorem centralTransferPhiValue_realCentral_block
    {R : Type*} [CommRing R] (c : R →+* Real)
    {h : Nat} (A : Real → Real) (u : Fin h → Real)
    (d : Fin h → Nat) (i : Fin h) (r : Fin (d i)) :
    centralTransferPhiValue c (realCentralTransferCentralValue A u d)
        (Sum.inl ⟨i, r⟩) = realCentralStirlingJet A (u i) (d i) r := by
  rw [realCentralStirlingJet_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjr : j ≤ r
  · simp [centralTransferPhiValue, realCentralTransferCentralValue, hjr]
  · simp [centralTransferPhiValue, realCentralTransferCentralValue, hjr]

@[simp]
theorem centralTransferPhiValue_realCentral_time
    {R : Type*} [CommRing R] (c : R →+* Real)
    {h : Nat} (A : Real → Real) (u : Fin h → Real)
    (d : Fin h → Nat) (i : Fin h) :
    centralTransferPhiValue c (realCentralTransferCentralValue A u d)
        (Sum.inr i) = A (u i) + 1 := by
  simp [centralTransferPhiValue, realCentralTransferCentralValue]

/-- The real all-main valuation is the explicit `Phi` source valuation. -/
theorem realCentralTransferMainValue_eq_phiSourceValue
    {R : Type*} [CommRing R] (c : R →+* Real)
    {h : Nat} (A : Real → Real) (u : Fin h → Real)
    (d : Fin h → Nat) :
    realCentralTransferMainValue A u d =
      centralTransferPhiSourceValue c
        (realCentralTransferCentralValue A u d) := by
  funext x
  cases x with
  | inl i => rfl
  | inr x =>
      cases x with
      | inl x =>
          rcases x with ⟨i, r⟩
          exact (centralTransferPhiValue_realCentral_block c A u d i r).symm
      | inr i =>
          exact (centralTransferPhiValue_realCentral_time c A u d i).symm

/-- With real homomorphic coefficient values, the all-main term is the value
of the actual canonical central generator. -/
theorem finiteSupportInitialEvaluation_realCentralMain_eq_centralGenerator
    {R : Type*} [CommRing R] (c : R →+* Real)
    {h : Nat} (A : Real → Real) (u : Fin h → Real)
    (d : Fin h → Nat)
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R) :
    finiteSupportInitialEvaluation
        (centralLaurentWeight (centralTransferShear d)) f
        (fun e => c (f.coeff e)) (realCentralTransferMainValue A u d) =
      MvPolynomial.eval₂Hom c (realCentralTransferCentralValue A u d)
        (centralPolynomialPhi R (Fin h) d (Fin h)
          (centralNormalizedInitialPolynomial
            (centralTransferShear d) f)) := by
  rw [finiteSupportInitialEvaluation_eq_eval₂Hom_initial,
    realCentralTransferMainValue_eq_phiSourceValue (R := R) c A u d]
  exact (eval₂Hom_centralGenerator_eq_initial c
    (realCentralTransferCentralValue A u d)
      (centralTransferShear d) f).symm

/-! ## Exact real weighted expansions -/

/-- The exact coefficientwise expansion over `Real` after substituting any
mixture of derivative and Hermite blocks. -/
theorem IsAbel.normalized_exponential_finiteSupport_realJetSubstitution
    {R : Type*} [CommRing R] {A : Real → Real} (hA : IsAbel A)
    {h : Nat} (u : Fin h → Real) (hu : ∀ i, 0 < u i)
    (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i))
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R)
    (a : ((Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) →₀ Nat) →
      Real) :
    Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight
            (centralLaurentWeight (centralTransferShear d)) f)) u) *
      finiteSupportPolynomialEvaluation f a
        (realCentralTransferActualValue A u d jets) =
      finiteSupportInitialEvaluation
          (centralLaurentWeight (centralTransferShear d)) f a
          (realCentralTransferMainValue A u d) +
        (finiteSupportInitialEvaluation
            (centralLaurentWeight (centralTransferShear d)) f a
            (realCentralTransferPerturbedValue A u d jets) -
          finiteSupportInitialEvaluation
            (centralLaurentWeight (centralTransferShear d)) f a
            (realCentralTransferMainValue A u d)) +
        ∑ e ∈ lexicographicTailSupport
            (centralLaurentWeight (centralTransferShear d)) f,
          Real.exp (-lexicographicDot
                (lexicographicWeightDifference
                  (centralLaurentWeight (centralTransferShear d)) f e) u) *
            (a e * e.prod (fun i n =>
              realCentralTransferPerturbedValue A u d jets i ^ n)) := by
  have hscaled :
      (fun x => realCentralTransferPerturbedValue A u d jets x *
        algebraMap Real Real
          (Real.exp (-lexicographicDot
            (centralLaurentWeight (centralTransferShear d) x) u))) =
        realCentralTransferActualValue A u d jets := by
    funext x
    change realCentralTransferPerturbedValue A u d jets x *
        Real.exp (-lexicographicDot
          (centralLaurentWeight (centralTransferShear d) x) u) =
      realCentralTransferActualValue A u d jets x
    exact hA.realCentralTransferPerturbed_scaled_eq_actual u hu d jets x
  have hexpand :=
    normalized_exponential_finiteSupportEvaluation_eq_initial_add_tail
      (A := Real) (centralLaurentWeight (centralTransferShear d)) f a
      (realCentralTransferPerturbedValue A u d jets) u
  rw [hscaled] at hexpand
  calc
    Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight
            (centralLaurentWeight (centralTransferShear d)) f)) u) *
        finiteSupportPolynomialEvaluation f a
          (realCentralTransferActualValue A u d jets) =
      finiteSupportInitialEvaluation
          (centralLaurentWeight (centralTransferShear d)) f a
          (realCentralTransferPerturbedValue A u d jets) +
        ∑ e ∈ lexicographicTailSupport
            (centralLaurentWeight (centralTransferShear d)) f,
          Real.exp (-lexicographicDot
                (lexicographicWeightDifference
                  (centralLaurentWeight (centralTransferShear d)) f e) u) *
            (a e * e.prod (fun i n =>
              realCentralTransferPerturbedValue A u d jets i ^ n)) := hexpand
    _ = _ := by ring

/-- Ring-homomorphic real specialization with its main term rewritten as the
actual canonical central generator. -/
theorem IsAbel.normalized_exponential_eval₂_realJetSubstitution
    {R : Type*} [CommRing R] {A : Real → Real} (hA : IsAbel A)
    (c : R →+* Real) {h : Nat}
    (u : Fin h → Real) (hu : ∀ i, 0 < u i) (d : Fin h → Nat)
    (jets : ∀ i, RealCentralJetSubstitutionData A (u i) (d i))
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R) :
    Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight
            (centralLaurentWeight (centralTransferShear d)) f)) u) *
      MvPolynomial.eval₂Hom c
        (realCentralTransferActualValue A u d jets) f =
      MvPolynomial.eval₂Hom c (realCentralTransferCentralValue A u d)
          (centralPolynomialPhi R (Fin h) d (Fin h)
            (centralNormalizedInitialPolynomial
              (centralTransferShear d) f)) +
        (MvPolynomial.eval₂Hom c
            (realCentralTransferPerturbedValue A u d jets)
            (lexicographicInitialForm
              (centralLaurentWeight (centralTransferShear d)) f) -
          MvPolynomial.eval₂Hom c
            (realCentralTransferCentralValue A u d)
            (centralPolynomialPhi R (Fin h) d (Fin h)
              (centralNormalizedInitialPolynomial
                (centralTransferShear d) f))) +
        ∑ e ∈ lexicographicTailSupport
            (centralLaurentWeight (centralTransferShear d)) f,
          Real.exp (-lexicographicDot
                (lexicographicWeightDifference
                  (centralLaurentWeight (centralTransferShear d)) f e) u) *
            MvPolynomial.eval₂Hom c
              (realCentralTransferPerturbedValue A u d jets)
              (MvPolynomial.monomial e (f.coeff e)) := by
  have hscaled :
      (fun x => realCentralTransferPerturbedValue A u d jets x *
        algebraMap Real Real
          (Real.exp (-lexicographicDot
            (centralLaurentWeight (centralTransferShear d) x) u))) =
        realCentralTransferActualValue A u d jets := by
    funext x
    change realCentralTransferPerturbedValue A u d jets x *
        Real.exp (-lexicographicDot
          (centralLaurentWeight (centralTransferShear d) x) u) =
      realCentralTransferActualValue A u d jets x
    exact hA.realCentralTransferPerturbed_scaled_eq_actual u hu d jets x
  have hexpand := normalized_exponential_eval₂_eq_base_add_errors
    c (realCentralTransferPerturbedValue A u d jets)
    (centralTransferPhiSourceValue c
      (realCentralTransferCentralValue A u d))
    (centralLaurentWeight (centralTransferShear d)) f u
  rw [hscaled] at hexpand
  rw [← eval₂Hom_centralGenerator_eq_initial c
    (realCentralTransferCentralValue A u d)
      (centralTransferShear d) f] at hexpand
  exact hexpand

end AbelFormalization
