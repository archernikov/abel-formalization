import AbelFormalization.TransferWeightedExpansion
import AbelFormalization.TransferInitialCertificate
import AbelFormalization.HermiteLemma

/-!
# Concrete jet substitutions in the quantitative transfer argument

This file joins three already formalized parts of the manuscript:

* the exact finite-support exponential expansion;
* the final signed-Stirling/time-translation equivalence `centralPolynomialPhi`;
* the exact derivative and Hermite transport identities.

The positive derivative order represented by `r : Fin (d i)` is `r.val + 1`.
The Hermite constructor therefore records the necessary relation
`d + 1 = totalMultiplicity m`.  A block can use either the exact derivative
constructor (whose coordinate error is zero) or the Hermite constructor
(whose coordinate error is exactly `exp (-u)` times the central remainder).

The final coefficientwise theorem does not assume that values of analytic
germs away from their base point form a ring homomorphism.  When the
coefficient values do come from a ring homomorphism, the last theorem
identifies its main term with the evaluation of the actual canonical central
generator.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open scoped BigOperators

/-! ## The concrete transfer weight -/

/-- The Laurent shear for the quantitative reduction.  Its negative appears
in `centralLaurentWeight`, so the order-`r+1` jet has positive original weight
`(r+1)e_i`. -/
def centralTransferShear {h : Nat} (d : Fin h → Nat) :
    CentralPolynomialIndex (Fin h) d (Fin h) → Fin h → Int
  | Sum.inl ⟨i, r⟩ => fun j =>
      if j = i then -((r.val + 1 : Nat) : Int) else 0
  | Sum.inr _ => 0

@[simp]
theorem centralTransferShear_block_apply {h : Nat} (d : Fin h → Nat)
    (i : Fin h) (r : Fin (d i)) (j : Fin h) :
    centralTransferShear d (Sum.inl ⟨i, r⟩) j =
      if j = i then -((r.val + 1 : Nat) : Int) else 0 := rfl

@[simp]
theorem centralTransferShear_time {h : Nat} (d : Fin h → Nat) (i : Fin h) :
    centralTransferShear d (Sum.inr i) = 0 := rfl

@[simp]
theorem centralLaurentWeight_transfer_q_apply {h : Nat} (d : Fin h → Nat)
    (i j : Fin h) :
    centralLaurentWeight (centralTransferShear d) (Sum.inl i) j =
      if i = j then -1 else 0 := by
  classical
  by_cases hij : i = j
  · simp [centralLaurentWeight, finiteLaurentExponentHom_apply,
      Finsupp.single_apply, hij]
  · simp [centralLaurentWeight, finiteLaurentExponentHom_apply,
      Finsupp.single_apply, hij]

@[simp]
theorem centralLaurentWeight_transfer_block_apply {h : Nat} (d : Fin h → Nat)
    (i : Fin h) (r : Fin (d i)) (j : Fin h) :
    centralLaurentWeight (centralTransferShear d) (Sum.inr (Sum.inl ⟨i, r⟩)) j =
      if j = i then ((r.val + 1 : Nat) : Int) else 0 := by
  by_cases hji : j = i
  · simp [centralLaurentWeight, centralTransferShear, hji]
  · simp [centralLaurentWeight, centralTransferShear, hji]

@[simp]
theorem centralLaurentWeight_transfer_time {h : Nat} (d : Fin h → Nat)
    (i : Fin h) :
    centralLaurentWeight (centralTransferShear d) (Sum.inr (Sum.inr i)) = 0 := by
  simp [centralLaurentWeight, centralTransferShear]

@[simp]
theorem lexicographicDot_centralTransfer_q {h : Nat} (d : Fin h → Nat)
    (u : Fin h → Real) (i : Fin h) :
    lexicographicDot
        (centralLaurentWeight (centralTransferShear d) (Sum.inl i)) u =
      -u i := by
  classical
  simp [lexicographicDot]

@[simp]
theorem lexicographicDot_centralTransfer_block {h : Nat} (d : Fin h → Nat)
    (u : Fin h → Real) (i : Fin h) (r : Fin (d i)) :
    lexicographicDot
        (centralLaurentWeight (centralTransferShear d)
          (Sum.inr (Sum.inl ⟨i, r⟩))) u =
      ((r.val + 1 : Nat) : Real) * u i := by
  classical
  simp [lexicographicDot]

@[simp]
theorem lexicographicDot_centralTransfer_time {h : Nat} (d : Fin h → Nat)
    (u : Fin h → Real) (i : Fin h) :
    lexicographicDot
        (centralLaurentWeight (centralTransferShear d)
          (Sum.inr (Sum.inr i))) u = 0 := by
  simp [lexicographicDot]

/-! ## The finite signed-Stirling coordinate change -/

/-- The central normalized value of the positive order represented by `r`.
The zero Stirling term is retained here so this is literally the endpoint of
the analytic transport theorems. -/
def centralStirlingJet (A : Real → Real) (u : Real) (d : Nat)
    (r : Fin d) : Complex :=
  ∑ j ∈ Finset.range (r.val + 2),
    (signedStirling (r.val + 1) j : Complex) *
      ((iteratedDeriv j A u : Real) : Complex)

/-- Delete the vanishing order-zero Stirling term and express the remaining
sum in the zero-based `Fin d` convention of `centralPolynomialPhi`. -/
theorem centralStirlingJet_eq_fin_sum (A : Real → Real) (u : Real)
    (d : Nat) (r : Fin d) :
    centralStirlingJet A u d r =
      ∑ j : Fin d,
        (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : Complex)
          else 0) *
        ((iteratedDeriv (j.val + 1) A u : Real) : Complex) := by
  classical
  unfold centralStirlingJet
  rw [Finset.sum_range_succ']
  have hrpos : 1 ≤ r.val + 1 := by omega
  simp only [signedStirling_zero hrpos, Int.cast_zero, zero_mul, add_zero]
  have hfin :
      (∑ j : Fin d,
        (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : Complex)
          else 0) *
        ((iteratedDeriv (j.val + 1) A u : Real) : Complex)) =
      ∑ j ∈ Finset.range d,
        if j ≤ r.val then
          (signedStirling (r.val + 1) (j + 1) : Complex) *
            ((iteratedDeriv (j + 1) A u : Real) : Complex)
        else 0 := by
    simpa using (Fin.sum_univ_eq_sum_range
      (fun j => if j ≤ r.val then
        (signedStirling (r.val + 1) (j + 1) : Complex) *
          ((iteratedDeriv (j + 1) A u : Real) : Complex)
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

/-- Evaluate the variable substitution underlying `centralPolynomialPhi` in
an arbitrary target ring. -/
def centralTransferPhiValue {R S Block Time : Type*}
    [CommRing R] [CommRing S] {d : Block → Nat}
    (c : R →+* S) (z : CentralPolynomialIndex Block d Time → S) :
    CentralPolynomialIndex Block d Time → S
  | Sum.inl ⟨b, i⟩ =>
      ∑ j : Fin (d b),
        c (if j ≤ i then
            (signedStirling (i.val + 1) (j.val + 1) : R)
          else 0) *
        z (Sum.inl ⟨b, j⟩)
  | Sum.inr t => z (Sum.inr t) + 1

/-- Evaluation after `Phi` is evaluation before `Phi` at the explicit
signed-Stirling/time-translated coordinate values. -/
theorem eval₂Hom_centralPolynomialPhi {R S Block Time : Type*}
    [CommRing R] [CommRing S] {d : Block → Nat}
    (c : R →+* S) (z : CentralPolynomialIndex Block d Time → S)
    (p : CentralPolynomial R Block d Time) :
    MvPolynomial.eval₂Hom c z
        (centralPolynomialPhi R Block d Time p) =
      MvPolynomial.eval₂Hom c (centralTransferPhiValue c z) p := by
  have heq :
      (MvPolynomial.eval₂Hom c z).comp
          (centralPolynomialPhi R Block d Time).toRingHom =
        MvPolynomial.eval₂Hom c (centralTransferPhiValue c z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro x
      cases x with
      | inl x =>
          rcases x with ⟨b, i⟩
          simp [centralTransferPhiValue]
      | inr t =>
          simp [centralTransferPhiValue]
  exact RingHom.congr_fun heq p

/-- Put the independent `q` variables at one and apply the evaluated `Phi`
substitution to every retained polynomial variable. -/
def centralTransferPhiSourceValue {R S Block Time : Type*}
    [CommRing R] [CommRing S] {h : Nat} {d : Block → Nat}
    (c : R →+* S) (z : CentralPolynomialIndex Block d Time → S) :
    (Fin h ⊕ CentralPolynomialIndex Block d Time) → S :=
  Sum.elim (fun _ => 1) (centralTransferPhiValue c z)

/-- Evaluating the normalized initial coefficient is the same as evaluating
the original initial form after putting every independent `q` at one. -/
theorem eval₂Hom_centralNormalizedInitialPolynomial {R S ι : Type*}
    [CommRing R] [CommRing S] {h : Nat}
    (c : R →+* S) (y : ι → S) (ω : ι → Fin h → Int)
    (f : MvPolynomial (Fin h ⊕ ι) R) :
    MvPolynomial.eval₂Hom c y (centralNormalizedInitialPolynomial ω f) =
      MvPolynomial.eval₂Hom c (Sum.elim (fun _ : Fin h => 1) y)
        (lexicographicInitialForm (centralLaurentWeight ω) f) := by
  unfold centralNormalizedInitialPolynomial
  have heq :
      (MvPolynomial.eval₂Hom c y).comp
          (MvPolynomial.eval₂Hom
            (MvPolynomial.C : R →+* MvPolynomial ι R)
            (Sum.elim (fun _ : Fin h => (1 : MvPolynomial ι R))
              MvPolynomial.X)) =
        MvPolynomial.eval₂Hom c (Sum.elim (fun _ : Fin h => 1) y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro x
      cases x <;> simp
  exact RingHom.congr_fun heq
    (lexicographicInitialForm (centralLaurentWeight ω) f)

/-- The main term in the weighted expansion is the actual `Phi` image of the
canonical normalized initial polynomial whenever coefficients are evaluated
through a ring homomorphism. -/
theorem eval₂Hom_centralGenerator_eq_initial {R S Block Time : Type*}
    [CommRing R] [CommRing S] {h : Nat} {d : Block → Nat}
    (c : R →+* S) (z : CentralPolynomialIndex Block d Time → S)
    (ω : CentralPolynomialIndex Block d Time → Fin h → Int)
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R) :
    MvPolynomial.eval₂Hom c z
        (centralPolynomialPhi R Block d Time
          (centralNormalizedInitialPolynomial ω f)) =
      MvPolynomial.eval₂Hom c (centralTransferPhiSourceValue c z)
        (lexicographicInitialForm (centralLaurentWeight ω) f) := by
  rw [eval₂Hom_centralPolynomialPhi,
    eval₂Hom_centralNormalizedInitialPolynomial]
  rfl

/-! ## Exact derivative and Hermite block data -/

theorem algebraMap_exp_nat_mul_mul_exp_neg_pow (n : Nat) (u : Real) :
    algebraMap Real Complex (Real.exp ((n : Real) * u)) *
        (algebraMap Real Complex (Real.exp (-u))) ^ n = 1 := by
  rw [← map_pow, ← map_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  simp [mul_neg]

/-- The exact derivative mode, written in the same normalized complex form
as the Hermite mode. -/
theorem IsAbel.normalizedDerivative_eq_centralStirlingJet
    {A : Real → Real} (hA : IsAbel A) (d : Nat) (r : Fin d)
    {u : Real} (hu : 0 < u) :
    algebraMap Real Complex
        (Real.exp (((r.val + 1 : Nat) : Real) * u)) *
      algebraMap Real Complex (iteratedDeriv (r.val + 1) A (E u)) =
        centralStirlingJet A u d r := by
  have h := hA.iteratedDeriv_transport_normalized
    (r.val + 1) (by omega) u hu
  rw [polynomialJet_descPochhammer] at h
  simpa [centralStirlingJet] using
    congrArg (algebraMap Real Complex) h

/-- The normalized Hermite coefficient is the central Stirling jet plus the
literal one-extra-scale remainder from `FullHermiteLemmaSpec`. -/
theorem FullHermiteLemmaSpec.normalizedHermiteCoeff_eq_centralStirlingJet_add_remainder
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {δ : ι → Complex}
    (hδ : δ ∈ hermiteNodeNeighborhood B) (r : Fin d) :
    algebraMap Real Complex
        (Real.exp (((r.val + 1 : Nat) : Real) * u)) *
      abelHermiteCoeff branch B m (E u) δ (r.val + 1) =
        centralStirlingJet A u d r +
          algebraMap Real Complex (Real.exp (-u)) *
            centralRemainder F m (1 / 4) (u : Complex)
              (Real.exp (-u) : Complex) δ (r.val + 1) := by
  have hrm : r.val + 1 < totalMultiplicity m := by omega
  rw [H.central_identity u hu δ hδ (r.val + 1) (by omega) hrm]
  rw [← mul_assoc]
  change
    (algebraMap Real Complex
          (Real.exp (((r.val + 1 : Nat) : Real) * u)) *
        (algebraMap Real Complex (Real.exp (-u))) ^ (r.val + 1)) * _ = _
  rw [algebraMap_exp_nat_mul_mul_exp_neg_pow (r.val + 1) u, one_mul]
  rfl

/-- Data common to both permitted source-jet evaluation modes. -/
structure CentralJetSubstitutionData (A : Real → Real) (u : Real)
    (d : Nat) where
  sourceJet : Fin d → Complex
  error : Fin d → Complex
  normalized_sourceJet : ∀ r,
    algebraMap Real Complex
        (Real.exp (((r.val + 1 : Nat) : Real) * u)) * sourceJet r =
      centralStirlingJet A u d r + error r

/-- Exact derivatives give substitution data with zero coordinate error. -/
def IsAbel.derivativeJetSubstitutionData {A : Real → Real}
    (hA : IsAbel A) {u : Real} (hu : 0 < u) (d : Nat) :
    CentralJetSubstitutionData A u d where
  sourceJet r := algebraMap Real Complex
    (iteratedDeriv (r.val + 1) A (E u))
  error _ := 0
  normalized_sourceJet r := by
    simpa using hA.normalizedDerivative_eq_centralStirlingJet d r hu

/-- Hermite coefficients give substitution data whose error is exactly the
central analytic remainder times one additional `exp (-u)` factor. -/
def FullHermiteLemmaSpec.hermiteJetSubstitutionData
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {δ : ι → Complex}
    (hδ : δ ∈ hermiteNodeNeighborhood B) :
    CentralJetSubstitutionData A u d where
  sourceJet r := abelHermiteCoeff branch B m (E u) δ (r.val + 1)
  error r := algebraMap Real Complex (Real.exp (-u)) *
    centralRemainder F m (1 / 4) (u : Complex)
      (Real.exp (-u) : Complex) δ (r.val + 1)
  normalized_sourceJet r :=
    H.normalizedHermiteCoeff_eq_centralStirlingJet_add_remainder
      d hd hu hδ r

/-- The actual real center, allowed node tuple, and exponential scale lie in
the joint parameter domain of the full Hermite lemma. -/
theorem FullHermiteLemmaSpec.actualParameters_mem_centralParameterDomain
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    {u : Real} (hu : u0 < u) {δ : ι → Complex}
    (hδ : δ ∈ hermiteNodeNeighborhood B) :
    (((u : Complex), δ), (Real.exp (-u) : Complex)) ∈
      centralParameterDomain u0 ε B := by
  have hscale : Real.exp (-u) < ε :=
    (Real.exp_lt_exp.mpr (neg_lt_neg hu)).trans H.exponentialScale_lt_radius
  refine ⟨⟨?_, hδ⟩, ?_⟩
  · simpa [rightHalfStrip] using And.intro hu H.parameterRadius_pos
  · simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-u))] using hscale

/-- The Hermite coordinate error has the manuscript's explicit extra
exponential factor and a remainder bounded linearly in the center. -/
theorem FullHermiteLemmaSpec.norm_hermiteJetSubstitutionData_error_le
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) {δ : ι → Complex}
    (hδ : δ ∈ hermiteNodeNeighborhood B) (r : Fin d) :
    ‖(H.hermiteJetSubstitutionData d hd hu hδ).error r‖ ≤
      Real.exp (-u) * (Kr * (1 + u)) := by
  have hrm : r.val + 1 < totalMultiplicity m := by omega
  have hb := H.remainder_bound (r.val + 1) hrm
    (((u : Complex), δ), (Real.exp (-u) : Complex))
    (H.actualParameters_mem_centralParameterDomain hu hδ)
  change ‖algebraMap Real Complex (Real.exp (-u)) *
      centralRemainder F m (1 / 4) (u : Complex)
        (Real.exp (-u) : Complex) δ (r.val + 1)‖ ≤ _
  rw [norm_mul]
  have hnorm : ‖algebraMap Real Complex (Real.exp (-u))‖ = Real.exp (-u) := by
    change ‖((Real.exp (-u) : Real) : Complex)‖ = Real.exp (-u)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (-u))]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left (by simpa using hb) (Real.exp_pos (-u)).le

/-! ## Global source, main, and error valuations -/

/-- Raw central coordinates: positive derivatives at `u_i` and times
`A(u_i)`. -/
def centralTransferCentralValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat) :
    CentralPolynomialIndex (Fin h) d (Fin h) → Complex
  | Sum.inl ⟨i, r⟩ =>
      algebraMap Real Complex (iteratedDeriv (r.val + 1) A (u i))
  | Sum.inr i => algebraMap Real Complex (A (u i))

/-- The all-main normalized source valuation.  It is `q_i = 1`, the
signed-Stirling jet in each block, and `A(u_i)+1` on each old time symbol. -/
def centralTransferMainValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Complex
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl ⟨i, r⟩) => centralStirlingJet A (u i) (d i) r
  | Sum.inr (Sum.inr i) => algebraMap Real Complex (A (u i)) + 1

/-- Coordinate errors are zero on `q` and time and are supplied by the
chosen derivative/Hermite mode on each jet coordinate. -/
def centralTransferCoordinateError {h : Nat} {A : Real → Real}
    {u : Fin h → Real} {d : Fin h → Nat}
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i)) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Complex
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl ⟨i, r⟩) => (jets i).error r
  | Sum.inr (Sum.inr _) => 0

/-- The normalized value actually supplied to the finite weighted expansion. -/
def centralTransferPerturbedValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat)
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i)) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Complex :=
  fun i => centralTransferMainValue A u d i +
    centralTransferCoordinateError jets i

/-- The literal evaluation of the shifted source polynomial: `q_i=exp u_i`,
the selected old jets at `E(u_i)`, and the old times `A(E(u_i))`. -/
def centralTransferActualValue {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat)
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i)) :
    (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) → Complex
  | Sum.inl i => algebraMap Real Complex (Real.exp (u i))
  | Sum.inr (Sum.inl ⟨i, r⟩) => (jets i).sourceJet r
  | Sum.inr (Sum.inr i) => algebraMap Real Complex (A (E (u i)))

theorem centralTransferPhiValue_central_block {R : Type*} [CommRing R]
    (c : R →+* Complex) {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat)
    (i : Fin h) (r : Fin (d i)) :
    centralTransferPhiValue c (centralTransferCentralValue A u d)
        (Sum.inl ⟨i, r⟩) = centralStirlingJet A (u i) (d i) r := by
  rw [centralStirlingJet_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjr : j ≤ r
  · simp [centralTransferPhiValue, centralTransferCentralValue, hjr]
  · simp [centralTransferPhiValue, centralTransferCentralValue, hjr]

@[simp]
theorem centralTransferPhiValue_central_time {R : Type*} [CommRing R]
    (c : R →+* Complex) {h : Nat} (A : Real → Real)
    (u : Fin h → Real) (d : Fin h → Nat) (i : Fin h) :
    centralTransferPhiValue c (centralTransferCentralValue A u d)
        (Sum.inr i) = algebraMap Real Complex (A (u i)) + 1 := by
  simp [centralTransferPhiValue, centralTransferCentralValue]

/-- The all-main coefficientwise valuation is exactly the evaluated `Phi`
substitution with all independent `q` variables put at one. -/
theorem centralTransferMainValue_eq_phiSourceValue
    {R : Type*} [CommRing R] (c : R →+* Complex)
    {h : Nat} (A : Real → Real) (u : Fin h → Real) (d : Fin h → Nat) :
    centralTransferMainValue A u d =
      centralTransferPhiSourceValue c (centralTransferCentralValue A u d) := by
  funext x
  cases x with
  | inl i => rfl
  | inr x =>
      cases x with
      | inl x =>
          rcases x with ⟨i, r⟩
          exact (centralTransferPhiValue_central_block c A u d i r).symm
      | inr i =>
          exact (centralTransferPhiValue_central_time c A u d i).symm

@[simp]
theorem centralTransferPerturbedValue_eq_main_add_error
    {h : Nat} (A : Real → Real) (u : Fin h → Real) (d : Fin h → Nat)
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i)) (x) :
    centralTransferPerturbedValue A u d jets x =
      centralTransferMainValue A u d x + centralTransferCoordinateError jets x := rfl

theorem algebraMap_exp_mul_exp_neg (x : Real) :
    algebraMap Real Complex (Real.exp x) *
      algebraMap Real Complex (Real.exp (-x)) = 1 := by
  rw [← map_mul, ← Real.exp_add]
  simp

/-- Character scaling of the perturbed normalized valuation recovers the
literal source valuation.  This is where the Abel time identity is used. -/
theorem IsAbel.centralTransferPerturbed_scaled_eq_actual
    {A : Real → Real} (hA : IsAbel A) {h : Nat}
    (u : Fin h → Real) (hu : ∀ i, 0 < u i) (d : Fin h → Nat)
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i)) (x) :
    centralTransferPerturbedValue A u d jets x *
        algebraMap Real Complex
          (Real.exp (-lexicographicDot
            (centralLaurentWeight (centralTransferShear d) x) u)) =
      centralTransferActualValue A u d jets x := by
  cases x with
  | inl i =>
      simp [centralTransferPerturbedValue, centralTransferMainValue,
        centralTransferCoordinateError, centralTransferActualValue]
  | inr x =>
      cases x with
      | inl x =>
          rcases x with ⟨i, r⟩
          rw [lexicographicDot_centralTransfer_block]
          change (centralStirlingJet A (u i) (d i) r + (jets i).error r) *
              algebraMap Real Complex
                (Real.exp (-(((r.val + 1 : Nat) : Real) * u i))) =
            (jets i).sourceJet r
          rw [← (jets i).normalized_sourceJet r]
          calc
            (algebraMap Real Complex
                  (Real.exp (((r.val + 1 : Nat) : Real) * u i)) *
                (jets i).sourceJet r) *
                algebraMap Real Complex
                  (Real.exp (-(((r.val + 1 : Nat) : Real) * u i))) =
              (algebraMap Real Complex
                  (Real.exp (((r.val + 1 : Nat) : Real) * u i)) *
                algebraMap Real Complex
                  (Real.exp (-(((r.val + 1 : Nat) : Real) * u i)))) *
                (jets i).sourceJet r := by ring
            _ = (jets i).sourceJet r := by
              rw [algebraMap_exp_mul_exp_neg]
              simp
      | inr i =>
          rw [lexicographicDot_centralTransfer_time]
          simp only [centralTransferPerturbedValue, centralTransferMainValue,
            centralTransferCoordinateError, centralTransferActualValue,
            Real.exp_zero, map_one, mul_one, add_zero]
          simpa using congrArg (algebraMap Real Complex) (hA.abel (u i) (hu i)).symm

/-! ## The coefficientwise generator expansion -/

/-- The exact finite expansion after substituting any mixture of derivative
and Hermite blocks.  Its first error is a finite polynomial perturbation by
the coordinate errors.  Every summand in the second error has the strictly
positive lexicographic weight difference furnished by
`lexicographicWeightDifference_pos_of_mem_tail`.

No ring-homomorphic evaluation of the coefficient ring is assumed here. -/
theorem IsAbel.normalized_exponential_finiteSupport_jetSubstitution
    {R : Type*} [CommRing R] {A : Real → Real} (hA : IsAbel A)
    {h : Nat} (u : Fin h → Real) (hu : ∀ i, 0 < u i)
    (d : Fin h → Nat)
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i))
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R)
    (a : ((Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) →₀ Nat) → Complex) :
    algebraMap Real Complex
        (Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight
            (centralLaurentWeight (centralTransferShear d)) f)) u)) *
      finiteSupportPolynomialEvaluation f a
        (centralTransferActualValue A u d jets) =
      finiteSupportInitialEvaluation
          (centralLaurentWeight (centralTransferShear d)) f a
          (centralTransferMainValue A u d) +
        (finiteSupportInitialEvaluation
            (centralLaurentWeight (centralTransferShear d)) f a
            (centralTransferPerturbedValue A u d jets) -
          finiteSupportInitialEvaluation
            (centralLaurentWeight (centralTransferShear d)) f a
            (centralTransferMainValue A u d)) +
        ∑ e ∈ lexicographicTailSupport
            (centralLaurentWeight (centralTransferShear d)) f,
          algebraMap Real Complex
              (Real.exp (-lexicographicDot
                (lexicographicWeightDifference
                  (centralLaurentWeight (centralTransferShear d)) f e) u)) *
            (a e * e.prod (fun i n =>
              centralTransferPerturbedValue A u d jets i ^ n)) := by
  have hscaled :
      (fun x => centralTransferPerturbedValue A u d jets x *
        algebraMap Real Complex
          (Real.exp (-lexicographicDot
            (centralLaurentWeight (centralTransferShear d) x) u))) =
        centralTransferActualValue A u d jets := by
    funext x
    exact hA.centralTransferPerturbed_scaled_eq_actual u hu d jets x
  have hexpand :=
    normalized_exponential_finiteSupportEvaluation_eq_initial_add_tail
      (A := Complex) (centralLaurentWeight (centralTransferShear d)) f a
      (centralTransferPerturbedValue A u d jets) u
  rw [hscaled] at hexpand
  calc
    algebraMap Real Complex
          (Real.exp (lexicographicDot
            (ofLex (lexicographicMinimumWeight
              (centralLaurentWeight (centralTransferShear d)) f)) u)) *
        finiteSupportPolynomialEvaluation f a
          (centralTransferActualValue A u d jets) =
      finiteSupportInitialEvaluation
          (centralLaurentWeight (centralTransferShear d)) f a
          (centralTransferPerturbedValue A u d jets) +
        ∑ e ∈ lexicographicTailSupport
            (centralLaurentWeight (centralTransferShear d)) f,
          algebraMap Real Complex
              (Real.exp (-lexicographicDot
                (lexicographicWeightDifference
                  (centralLaurentWeight (centralTransferShear d)) f e) u)) *
            (a e * e.prod (fun i n =>
              centralTransferPerturbedValue A u d jets i ^ n)) := hexpand
    _ = _ := by ring

/-- With homomorphic coefficient values, the all-main coefficientwise term is
the value of the actual canonical central generator selected by the finite
initial-form certificate. -/
theorem finiteSupportInitialEvaluation_centralMain_eq_centralGenerator
    {R : Type*} [CommRing R] (c : R →+* Complex)
    {h : Nat} (A : Real → Real) (u : Fin h → Real) (d : Fin h → Nat)
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R) :
    finiteSupportInitialEvaluation
        (centralLaurentWeight (centralTransferShear d)) f
        (fun e => c (f.coeff e)) (centralTransferMainValue A u d) =
      MvPolynomial.eval₂Hom c (centralTransferCentralValue A u d)
        (centralPolynomialPhi R (Fin h) d (Fin h)
          (centralNormalizedInitialPolynomial (centralTransferShear d) f)) := by
  rw [finiteSupportInitialEvaluation_eq_eval₂Hom_initial,
    centralTransferMainValue_eq_phiSourceValue (R := R) c A u d]
  exact (eval₂Hom_centralGenerator_eq_initial c
    (centralTransferCentralValue A u d) (centralTransferShear d) f).symm

/-- Ring-homomorphic specialization of the preceding coefficientwise
identity, with the main term rewritten as the actual central generator. -/
theorem IsAbel.normalized_exponential_eval₂_jetSubstitution
    {R : Type*} [CommRing R] {A : Real → Real} (hA : IsAbel A)
    (c : R →+* Complex) {h : Nat}
    (u : Fin h → Real) (hu : ∀ i, 0 < u i) (d : Fin h → Nat)
    (jets : ∀ i, CentralJetSubstitutionData A (u i) (d i))
    (f : MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R) :
    algebraMap Real Complex
        (Real.exp (lexicographicDot
          (ofLex (lexicographicMinimumWeight
            (centralLaurentWeight (centralTransferShear d)) f)) u)) *
      MvPolynomial.eval₂Hom c (centralTransferActualValue A u d jets) f =
      MvPolynomial.eval₂Hom c (centralTransferCentralValue A u d)
          (centralPolynomialPhi R (Fin h) d (Fin h)
            (centralNormalizedInitialPolynomial (centralTransferShear d) f)) +
        (MvPolynomial.eval₂Hom c
            (centralTransferPerturbedValue A u d jets)
            (lexicographicInitialForm
              (centralLaurentWeight (centralTransferShear d)) f) -
          MvPolynomial.eval₂Hom c (centralTransferCentralValue A u d)
            (centralPolynomialPhi R (Fin h) d (Fin h)
              (centralNormalizedInitialPolynomial (centralTransferShear d) f))) +
        ∑ e ∈ lexicographicTailSupport
            (centralLaurentWeight (centralTransferShear d)) f,
          algebraMap Real Complex
              (Real.exp (-lexicographicDot
                (lexicographicWeightDifference
                  (centralLaurentWeight (centralTransferShear d)) f e) u)) *
            MvPolynomial.eval₂Hom c (centralTransferPerturbedValue A u d jets)
              (MvPolynomial.monomial e (f.coeff e)) := by
  have hscaled :
      (fun x => centralTransferPerturbedValue A u d jets x *
        algebraMap Real Complex
          (Real.exp (-lexicographicDot
            (centralLaurentWeight (centralTransferShear d) x) u))) =
        centralTransferActualValue A u d jets := by
    funext x
    exact hA.centralTransferPerturbed_scaled_eq_actual u hu d jets x
  have hexpand := normalized_exponential_eval₂_eq_base_add_errors
    c (centralTransferPerturbedValue A u d jets)
    (centralTransferPhiSourceValue c (centralTransferCentralValue A u d))
    (centralLaurentWeight (centralTransferShear d)) f u
  rw [hscaled] at hexpand
  rw [← eval₂Hom_centralGenerator_eq_initial c
    (centralTransferCentralValue A u d) (centralTransferShear d) f] at hexpand
  exact hexpand

end AbelFormalization
