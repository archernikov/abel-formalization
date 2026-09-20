import AbelFormalization.WeightedPolynomialModulePieces
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Max
import Mathlib.Order.WellFounded
import Mathlib.Algebra.MvPolynomial.CommRing

set_option autoImplicit false

/-!
# Leading terms of actual finite free polynomial modules

A position-first module order combines the finite component order with an
actual mathlib monomial order. The chosen leading
term is the maximum of the actual finite coefficient support. Translation
by a polynomial monomial preserves this order, and cancellation of matching
leading coefficients strictly decreases every remaining term.

The order is independent of ordinary variable degrees and component shifts.
Later homogeneous-component selection can therefore use arbitrary positive
ordinary degrees and integer component shifts without altering this module.
-/

noncomputable section

namespace AbelFormalization

variable {n r : ℕ}

/-- The ordered synonym for position-first module terms. -/
abbrev PolynomialModuleTermSyn (m : MonomialOrder (Fin n)) (r : ℕ) :=
  Lex (Fin r × m.syn)

/-- The component is compared first, and the polynomial exponent second. -/
def polynomialModuleTermKey (m : MonomialOrder (Fin n))
    (t : Fin r × (Fin n →₀ ℕ)) : PolynomialModuleTermSyn m r :=
  toLex (t.1, m.toSyn t.2)

theorem polynomialModuleTermKey_injective (m : MonomialOrder (Fin n)) :
    Function.Injective (polynomialModuleTermKey (r := r) m) := by
  intro t u h
  have hpair : (t.1, m.toSyn t.2) = (u.1, m.toSyn u.2) :=
    congrArg ofLex h
  have hfirst : t.1 = u.1 :=
    congrArg (fun p : Fin r × m.syn => p.1) hpair
  have hsecond : t.2 = u.2 :=
    m.toSyn.injective (congrArg (fun p : Fin r × m.syn => p.2) hpair)
  exact Prod.ext hfirst hsecond

/-- The actual strict module-term order is well-founded. -/
theorem polynomialModuleTermKey_wellFounded (m : MonomialOrder (Fin n)) :
    WellFounded (fun t u : Fin r × (Fin n →₀ ℕ) =>
      polynomialModuleTermKey m t < polynomialModuleTermKey m u) :=
  InvImage.wf (polynomialModuleTermKey m) wellFounded_lt

/-- Multiplication by a monomial adds its exponent and keeps the component. -/
def polynomialModuleTermTranslate (d : Fin n →₀ ℕ)
    (t : Fin r × (Fin n →₀ ℕ)) : Fin r × (Fin n →₀ ℕ) :=
  (t.1, d + t.2)

theorem polynomialModuleTermKey_translate_le_iff (m : MonomialOrder (Fin n))
    (d : Fin n →₀ ℕ) (t u : Fin r × (Fin n →₀ ℕ)) :
    polynomialModuleTermKey m (polynomialModuleTermTranslate d t) ≤
        polynomialModuleTermKey m (polynomialModuleTermTranslate d u) ↔
      polynomialModuleTermKey m t ≤ polynomialModuleTermKey m u := by
  simp only [polynomialModuleTermKey, polynomialModuleTermTranslate,
    Prod.Lex.toLex_le_toLex, map_add, add_le_add_iff_left]

theorem polynomialModuleTermKey_translate_lt_iff (m : MonomialOrder (Fin n))
    (d : Fin n →₀ ℕ) (t u : Fin r × (Fin n →₀ ℕ)) :
    polynomialModuleTermKey m (polynomialModuleTermTranslate d t) <
        polynomialModuleTermKey m (polynomialModuleTermTranslate d u) ↔
      polynomialModuleTermKey m t < polynomialModuleTermKey m u := by
  simp only [polynomialModuleTermKey, polynomialModuleTermTranslate,
    Prod.Lex.toLex_lt_toLex, map_add, add_lt_add_iff_left]

variable {K : Type*} [Field K]

/-- Actual nonzero component coefficients, via the proved coefficient equivalence. -/
def polynomialModuleSupport (P : Fin r → MvPolynomial (Fin n) K) :
    Finset (Fin r × (Fin n →₀ ℕ)) :=
  (polynomialModuleCoeffEquiv P).support

@[simp]
theorem mem_polynomialModuleSupport (P : Fin r → MvPolynomial (Fin n) K)
    (t : Fin r × (Fin n →₀ ℕ)) :
    t ∈ polynomialModuleSupport P ↔ (P t.1).coeff t.2 ≠ 0 := by
  rw [polynomialModuleSupport, Finsupp.mem_support_iff]
  change polynomialModuleCoeffEquiv P (t.1, t.2) ≠ 0 ↔ _
  rw [polynomialModuleCoeffEquiv_apply]

theorem polynomialModuleSupport_nonempty_iff (P : Fin r → MvPolynomial (Fin n) K) :
    (polynomialModuleSupport P).Nonempty ↔ P ≠ 0 := by
  rw [polynomialModuleSupport, Finsupp.support_nonempty_iff]
  exact polynomialModuleCoeffEquiv.map_ne_zero_iff

/-- Being the actual largest nonzero coefficient term. -/
def IsPolynomialModuleLeadingTerm (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (t : Fin r × (Fin n →₀ ℕ)) : Prop :=
  (P t.1).coeff t.2 ≠ 0 ∧
    ∀ u : Fin r × (Fin n →₀ ℕ), (P u.1).coeff u.2 ≠ 0 →
      polynomialModuleTermKey m u ≤ polynomialModuleTermKey m t

theorem exists_polynomialModuleLeadingTerm (m : MonomialOrder (Fin n))
    {P : Fin r → MvPolynomial (Fin n) K} (hP : P ≠ 0) :
    ∃ t, IsPolynomialModuleLeadingTerm m P t := by
  classical
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (polynomialModuleSupport P)
    (polynomialModuleTermKey m) ((polynomialModuleSupport_nonempty_iff P).mpr hP)
  exact ⟨t, (mem_polynomialModuleSupport P t).mp ht,
    fun u hu => hmax u ((mem_polynomialModuleSupport P u).mpr hu)⟩

theorem IsPolynomialModuleLeadingTerm.ne_zero {m : MonomialOrder (Fin n)}
    {P : Fin r → MvPolynomial (Fin n) K} {t : Fin r × (Fin n →₀ ℕ)}
    (h : IsPolynomialModuleLeadingTerm m P t) : P ≠ 0 := by
  intro hP
  exact h.1 (by simp [hP])

theorem IsPolynomialModuleLeadingTerm.unique {m : MonomialOrder (Fin n)}
    {P : Fin r → MvPolynomial (Fin n) K} {t u : Fin r × (Fin n →₀ ℕ)}
    (ht : IsPolynomialModuleLeadingTerm m P t)
    (hu : IsPolynomialModuleLeadingTerm m P u) : t = u :=
  polynomialModuleTermKey_injective m (le_antisymm (hu.2 t ht.1) (ht.2 u hu.1))

theorem IsPolynomialModuleLeadingTerm.coeff_eq_zero_of_lt {m : MonomialOrder (Fin n)}
    {P : Fin r → MvPolynomial (Fin n) K} {t u : Fin r × (Fin n →₀ ℕ)}
    (ht : IsPolynomialModuleLeadingTerm m P t)
    (hu : polynomialModuleTermKey m t < polynomialModuleTermKey m u) :
    (P u.1).coeff u.2 = 0 := by
  by_contra h
  exact (not_le_of_gt hu) (ht.2 u h)

/-- The actual leading term index. Its nonzero argument avoids any choice
of a fictitious component when the finite free module has rank zero. -/
def polynomialModuleLeadingTerm (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (hP : P ≠ 0) :
    Fin r × (Fin n →₀ ℕ) :=
  Classical.choose (exists_polynomialModuleLeadingTerm m hP)

theorem polynomialModuleLeadingTerm_spec (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (hP : P ≠ 0) :
    IsPolynomialModuleLeadingTerm m P (polynomialModuleLeadingTerm m P hP) :=
  Classical.choose_spec (exists_polynomialModuleLeadingTerm m hP)

theorem polynomialModuleLeadingTerm_eq_of_spec (m : MonomialOrder (Fin n))
    {P : Fin r → MvPolynomial (Fin n) K} (hP : P ≠ 0)
    {t : Fin r × (Fin n →₀ ℕ)} (ht : IsPolynomialModuleLeadingTerm m P t) :
    polynomialModuleLeadingTerm m P hP = t :=
  (polynomialModuleLeadingTerm_spec m P hP).unique ht

/-- The chosen leading coefficient is an actual coefficient of P. -/
def polynomialModuleLeadingCoeff (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (hP : P ≠ 0) : K :=
  (P (polynomialModuleLeadingTerm m P hP).1).coeff
    (polynomialModuleLeadingTerm m P hP).2

theorem polynomialModuleLeadingCoeff_ne_zero (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (hP : P ≠ 0) :
    polynomialModuleLeadingCoeff m P hP ≠ 0 :=
  (polynomialModuleLeadingTerm_spec m P hP).1

/-- The resulting strict order on actual nonzero module vectors is also
well-founded, which permits induction during actual leading-term cancellation. -/
theorem polynomialModuleLeadingTerm_wellFounded (m : MonomialOrder (Fin n)) :
    WellFounded (fun P Q : {P : Fin r → MvPolynomial (Fin n) K // P ≠ 0} =>
      polynomialModuleTermKey m (polynomialModuleLeadingTerm m P.val P.property) <
        polynomialModuleTermKey m (polynomialModuleLeadingTerm m Q.val Q.property)) :=
  InvImage.wf (fun P : {P : Fin r → MvPolynomial (Fin n) K // P ≠ 0} =>
    polynomialModuleTermKey m (polynomialModuleLeadingTerm m P.val P.property)) wellFounded_lt

/-- Translation of an actual leading term by coefficient-one monomial multiplication. -/
theorem IsPolynomialModuleLeadingTerm.monomial_smul {m : MonomialOrder (Fin n)}
    {P : Fin r → MvPolynomial (Fin n) K} {t : Fin r × (Fin n →₀ ℕ)}
    (hP : IsPolynomialModuleLeadingTerm m P t) (d : Fin n →₀ ℕ) :
    IsPolynomialModuleLeadingTerm m ((MvPolynomial.monomial d (1 : K)) • P)
      (polynomialModuleTermTranslate d t) := by
  classical
  constructor
  · change (MvPolynomial.monomial d (1 : K) * P t.1).coeff (d + t.2) ≠ 0
    simpa only [MvPolynomial.coeff_monomial_mul, one_mul] using hP.1
  · intro u hu
    change (MvPolynomial.monomial d (1 : K) * P u.1).coeff u.2 ≠ 0 at hu
    have hdu : d ≤ u.2 := by
      by_contra h
      exact hu (by rw [MvPolynomial.coeff_monomial_mul', ite_eq_right h])
    have hu' : (P u.1).coeff (u.2 - d) ≠ 0 := by
      simpa only [MvPolynomial.coeff_monomial_mul', ite_eq_left hdu, one_mul] using hu
    have h := (polynomialModuleTermKey_translate_le_iff m d (u.1, u.2 - d) t).mpr
      (hP.2 (u.1, u.2 - d) hu')
    simpa only [polynomialModuleTermTranslate, add_tsub_cancel_of_le hdu] using h

theorem polynomialModule_monomial_smul_ne_zero
    (m : MonomialOrder (Fin n)) {P : Fin r → MvPolynomial (Fin n) K}
    (hP : P ≠ 0) (d : Fin n →₀ ℕ) :
    (MvPolynomial.monomial d (1 : K)) • P ≠ 0 :=
  ((polynomialModuleLeadingTerm_spec m P hP).monomial_smul d).ne_zero

theorem polynomialModuleLeadingTerm_monomial_smul (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (hP : P ≠ 0) (d : Fin n →₀ ℕ) :
    polynomialModuleLeadingTerm m ((MvPolynomial.monomial d (1 : K)) • P)
        (polynomialModule_monomial_smul_ne_zero m hP d) =
      polynomialModuleTermTranslate d (polynomialModuleLeadingTerm m P hP) :=
  polynomialModuleLeadingTerm_eq_of_spec m _
    ((polynomialModuleLeadingTerm_spec m P hP).monomial_smul d)

theorem polynomialModuleLeadingCoeff_monomial_smul (m : MonomialOrder (Fin n))
    (P : Fin r → MvPolynomial (Fin n) K) (hP : P ≠ 0) (d : Fin n →₀ ℕ) :
    polynomialModuleLeadingCoeff m ((MvPolynomial.monomial d (1 : K)) • P)
        (polynomialModule_monomial_smul_ne_zero m hP d) =
      polynomialModuleLeadingCoeff m P hP := by
  unfold polynomialModuleLeadingCoeff
  rw [polynomialModuleLeadingTerm_monomial_smul]
  change (MvPolynomial.monomial d (1 : K) *
      P (polynomialModuleLeadingTerm m P hP).1).coeff
        (d + (polynomialModuleLeadingTerm m P hP).2) = _
  rw [MvPolynomial.coeff_monomial_mul, one_mul]

/-- Nonzero scalar multiplication preserves the actual largest coefficient index. -/
theorem IsPolynomialModuleLeadingTerm.smul {m : MonomialOrder (Fin n)}
    {P : Fin r → MvPolynomial (Fin n) K} {t : Fin r × (Fin n →₀ ℕ)}
    (hP : IsPolynomialModuleLeadingTerm m P t) {c : K} (hc : c ≠ 0) :
    IsPolynomialModuleLeadingTerm m (c • P) t := by
  constructor
  · simpa only [Pi.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul] using
      mul_ne_zero hc hP.1
  · intro u hu
    apply hP.2 u
    intro hzero
    apply hu
    simp only [Pi.smul_apply, MvPolynomial.coeff_smul, hzero, smul_zero]

/-- If the two leading coefficients match, every surviving coefficient
of the actual difference is strictly below their common leading term. -/
theorem polynomialModule_sub_terms_lt {m : MonomialOrder (Fin n)}
    {P Q : Fin r → MvPolynomial (Fin n) K} {t : Fin r × (Fin n →₀ ℕ)}
    (hP : IsPolynomialModuleLeadingTerm m P t)
    (hQ : IsPolynomialModuleLeadingTerm m Q t)
    (hcoeff : (P t.1).coeff t.2 = (Q t.1).coeff t.2)
    {u : Fin r × (Fin n →₀ ℕ)} (hu : ((P - Q) u.1).coeff u.2 ≠ 0) :
    polynomialModuleTermKey m u < polynomialModuleTermKey m t := by
  have hle : polynomialModuleTermKey m u ≤ polynomialModuleTermKey m t := by
    by_cases hp : (P u.1).coeff u.2 = 0
    · apply hQ.2 u
      intro hq
      apply hu
      simp only [Pi.sub_apply, MvPolynomial.coeff_sub, hp, hq, sub_self]
    · exact hP.2 u hp
  apply lt_of_le_of_ne hle
  intro heq
  have hut : u = t := polynomialModuleTermKey_injective m heq
  subst u
  exact hu (by simp only [Pi.sub_apply, MvPolynomial.coeff_sub, hcoeff, sub_self])

/-- The nonzero actual cancellation remainder has strictly smaller leading term. -/
theorem polynomialModuleLeadingTerm_sub_lt (m : MonomialOrder (Fin n))
    {P Q : Fin r → MvPolynomial (Fin n) K} {t : Fin r × (Fin n →₀ ℕ)}
    (hP : IsPolynomialModuleLeadingTerm m P t)
    (hQ : IsPolynomialModuleLeadingTerm m Q t)
    (hcoeff : (P t.1).coeff t.2 = (Q t.1).coeff t.2) (hsub : P - Q ≠ 0) :
    polynomialModuleTermKey m (polynomialModuleLeadingTerm m (P - Q) hsub) <
      polynomialModuleTermKey m t :=
  polynomialModule_sub_terms_lt hP hQ hcoeff
    (polynomialModuleLeadingTerm_spec m (P - Q) hsub).1

/-- Scaling the reducer by the actual quotient of leading coefficients
cancels the leading term; every surviving term is strictly smaller. -/
theorem polynomialModule_sub_scaled_terms_lt {m : MonomialOrder (Fin n)}
    {P Q : Fin r → MvPolynomial (Fin n) K} {t : Fin r × (Fin n →₀ ℕ)}
    (hP : IsPolynomialModuleLeadingTerm m P t)
    (hQ : IsPolynomialModuleLeadingTerm m Q t)
    {u : Fin r × (Fin n →₀ ℕ)}
    (hu : ((P - ((P t.1).coeff t.2 / (Q t.1).coeff t.2) • Q) u.1).coeff u.2 ≠ 0) :
    polynomialModuleTermKey m u < polynomialModuleTermKey m t := by
  apply polynomialModule_sub_terms_lt hP (hQ.smul (div_ne_zero hP.1 hQ.1)) ?_ hu
  simp only [Pi.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul,
    div_mul_cancel₀ _ hQ.1]

end AbelFormalization
