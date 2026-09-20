import AbelFormalization.AnalyticGerm
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Order.Filter.Finite

/-!
# Finite polynomial identities on analytic neighborhoods

Polynomial coefficients are actual analytic germs. The homomorphism below
takes them to germs of polynomial-valued functions, not to a purported
simultaneous evaluation homomorphism on all coefficient germs near the base
point. Finite identities hold on one neighborhood as polynomial identities,
so their independent symbols can be evaluated at arbitrary, unbounded values.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

section GenericGerms

variable {E R S ι : Type*} [CommSemiring R] [CommSemiring S]

/-- Applying a ring homomorphism to representatives descends to a ring
homomorphism on germs at every filter. -/
def germMapRingHom (l : Filter E) (φ : R →+* S) : Germ l R →+* Germ l S where
  toFun := Germ.map φ
  map_zero' := by
    change ((fun _ : E => φ 0) : Germ l S) = ((fun _ : E => (0 : S)) : Germ l S)
    simp
  map_one' := by
    change ((fun _ : E => φ 1) : Germ l S) = ((fun _ : E => (1 : S)) : Germ l S)
    simp
  map_add' a b := by
    refine Germ.inductionOn₂ a b ?_
    intro f g
    change ((fun x => φ (f x + g x)) : Germ l S) =
      ((fun x => φ (f x) + φ (g x)) : Germ l S)
    exact Germ.coe_eq.mpr (Eventually.of_forall fun x => φ.map_add _ _)
  map_mul' a b := by
    refine Germ.inductionOn₂ a b ?_
    intro f g
    change ((fun x => φ (f x * g x)) : Germ l S) =
      ((fun x => φ (f x) * φ (g x)) : Germ l S)
    exact Germ.coe_eq.mpr (Eventually.of_forall fun x => φ.map_mul _ _)

@[simp]
theorem germMapRingHom_coe (l : Filter E) (φ : R →+* S) (f : E → R) :
    germMapRingHom l φ (f : Germ l R) = ((fun x => φ (f x)) : Germ l S) := rfl

/-- Constant polynomial-valued germs form an actual coefficient ring map. -/
def germConstRingHom (l : Filter E) : R →+* Germ l R :=
  (Germ.coeRingHom l).comp (Pi.constRingHom E R)

@[simp]
theorem germConstRingHom_apply (l : Filter E) (r : R) :
    germConstRingHom l r = ((fun _ : E => r) : Germ l R) := rfl

/-- A polynomial in germs has a well-defined germ of polynomial-valued
functions. Symbols are sent to constant polynomial germs. -/
def polynomialGermHom (l : Filter E) :
    MvPolynomial ι (Germ l R) →+* Germ l (MvPolynomial ι R) :=
  MvPolynomial.eval₂Hom (germMapRingHom l MvPolynomial.C)
    (fun i => germConstRingHom l (MvPolynomial.X i))

theorem polynomialGermHom_monomial_coe (l : Filter E) (d : ι →₀ ℕ)
    (a : E → R) :
    polynomialGermHom l (MvPolynomial.monomial d (a : Germ l R)) =
      ((fun x => MvPolynomial.monomial d (a x)) : Germ l (MvPolynomial ι R)) := by
  classical
  unfold polynomialGermHom
  rw [MvPolynomial.eval₂Hom_monomial]
  have hprod : d.prod (fun i n => (germConstRingHom l (MvPolynomial.X i)) ^ n) =
      germConstRingHom l (d.prod (fun i n => (MvPolynomial.X i : MvPolynomial ι R) ^ n)) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hprod]
  change ((fun x => MvPolynomial.C (a x) *
    d.prod (fun i n => (MvPolynomial.X i : MvPolynomial ι R) ^ n)) :
      Germ l (MvPolynomial ι R)) = _
  exact Germ.coe_eq.mpr (Eventually.of_forall fun x => MvPolynomial.monomial_eq.symm)

/-- Coercion to germs preserves the literal finite sum of pointwise products. -/
theorem germ_coe_sum_mul {κ : Type*} (l : Filter E) (s : Finset κ)
    (A P : κ → E → R) :
    ((fun x => ∑ i ∈ s, A i x * P i x) : Germ l R) =
      ∑ i ∈ s, (A i : Germ l R) * (P i : Germ l R) := by
  have hfun : (fun x => ∑ i ∈ s, A i x * P i x) = ∑ i ∈ s, A i * P i := by
    funext x
    simp only [Finset.sum_apply, Pi.mul_apply]
  rw [hfun]
  change (Germ.coeRingHom l) (∑ i ∈ s, A i * P i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact map_mul (Germ.coeRingHom l) _ _

end GenericGerms

section AnalyticPolynomialGerms

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual polynomial-valued germ map for analytic coefficient germs. -/
def analyticPolynomialGermHom (x : E) :
    MvPolynomial ι (AnalyticGermAt x) →+* Germ (𝓝 x) (MvPolynomial ι ℝ) :=
  (polynomialGermHom (𝓝 x)).comp (MvPolynomial.map (analyticGermSubring x).subtype)

theorem analyticPolynomialGermHom_monomial_of (x : E) (d : ι →₀ ℕ)
    (a : E → ℝ) (ha : AnalyticAt ℝ a x) :
    analyticPolynomialGermHom x (MvPolynomial.monomial d (analyticGermOf a ha)) =
      ((fun w => MvPolynomial.monomial d (a w)) : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  unfold analyticPolynomialGermHom
  rw [RingHom.comp_apply, MvPolynomial.map_monomial]
  exact polynomialGermHom_monomial_coe (𝓝 x) d a

/-- A finite list of coefficient functions defines an actual polynomial at
every point, with the same fixed finite set of allowed exponents. -/
def polynomialFromCoefficientRepresentatives (s : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → E → ℝ) (w : E) : MvPolynomial ι ℝ :=
  ∑ d ∈ s, MvPolynomial.monomial d (a d w)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem polynomialFromCoefficientRepresentatives_coeff [DecidableEq ι]
    (s : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → E → ℝ) (w : E) (d : ι →₀ ℕ) :
    (polynomialFromCoefficientRepresentatives s a w).coeff d =
      if d ∈ s then a d w else 0 := by
  classical
  simp [polynomialFromCoefficientRepresentatives, MvPolynomial.coeff_monomial]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem polynomialFromCoefficientRepresentatives_support
    (s : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → E → ℝ) (w : E) :
    (polynomialFromCoefficientRepresentatives s a w).support ⊆ s := by
  classical
  intro d hd
  by_contra hds
  exact (MvPolynomial.mem_support_iff.mp hd)
    (by simp [polynomialFromCoefficientRepresentatives_coeff, hds])

/-- Any chosen analytic representatives of the finitely many supported
coefficients give the correct polynomial-valued germ. -/
theorem analyticPolynomialGermHom_eq_coefficientRepresentative
    (x : E) (P : MvPolynomial ι (AnalyticGermAt x))
    (a : (ι →₀ ℕ) → E → ℝ) (ha : ∀ d, AnalyticAt ℝ (a d) x)
    (hrep : ∀ d ∈ P.support, P.coeff d = analyticGermOf (a d) (ha d)) :
    analyticPolynomialGermHom x P =
      (polynomialFromCoefficientRepresentatives P.support a :
        Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  classical
  have hfun : polynomialFromCoefficientRepresentatives P.support a =
      ∑ d ∈ P.support, (fun w => MvPolynomial.monomial d (a d w)) := by
    funext w
    simp only [polynomialFromCoefficientRepresentatives, Finset.sum_apply]
  calc
    analyticPolynomialGermHom x P =
        ∑ d ∈ P.support, analyticPolynomialGermHom x (MvPolynomial.monomial d (P.coeff d)) := by
      rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
    _ = ∑ d ∈ P.support,
        ((fun w => MvPolynomial.monomial d (a d w)) : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hrep d hd, analyticPolynomialGermHom_monomial_of]
    _ = _ := by
      rw [hfun]
      exact (map_sum (Germ.coeRingHom (𝓝 x)) _ _).symm

/-- Every polynomial in analytic germs has an actual polynomial-valued
representative with fixed finite support and analytic coefficient functions
on one common open neighborhood. -/
theorem exists_analyticPolynomialRepresentative (x : E)
    (P : MvPolynomial ι (AnalyticGermAt x)) :
    ∃ F : E → MvPolynomial ι ℝ, ∃ U : Set E,
      IsOpen U ∧ x ∈ U ∧
      (∀ w, (F w).support ⊆ P.support) ∧
      (∀ d, AnalyticOnNhd ℝ (fun w => (F w).coeff d) U) ∧
      analyticPolynomialGermHom x P = (F : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  classical
  choose a ha hrep using fun d => exists_analyticGerm_representative (P.coeff d)
  let F := polynomialFromCoefficientRepresentatives P.support a
  have hlocal : ∀ᶠ w in 𝓝 x, ∀ d ∈ P.support, AnalyticAt ℝ (a d) w :=
    (eventually_all_finset P.support).mpr fun d hd => (ha d).eventually_analyticAt
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp hlocal
  refine ⟨F, U, hUopen, hxU, ?_, ?_, ?_⟩
  · exact polynomialFromCoefficientRepresentatives_support P.support a
  · intro d w hw
    by_cases hd : d ∈ P.support
    · have heq : (fun z => (F z).coeff d) = a d := by
        funext z
        simp [F, polynomialFromCoefficientRepresentatives_coeff, hd]
      rw [heq]
      exact hU w hw d hd
    · have heq : (fun z => (F z).coeff d) = (fun _ => (0 : ℝ)) := by
        funext z
        simp [F, polynomialFromCoefficientRepresentatives_coeff, hd]
      rw [heq]
      exact analyticAt_const
  · exact analyticPolynomialGermHom_eq_coefficientRepresentative x P a ha (fun d hd => hrep d)

/-- Finitely many polynomials have simultaneous analytic coefficient
representatives on one common neighborhood, retaining their individual
finite monomial supports. -/
theorem exists_analyticPolynomialRepresentatives {κ : Type*} [Finite κ]
    (x : E) (P : κ → MvPolynomial ι (AnalyticGermAt x)) :
    ∃ F : κ → E → MvPolynomial ι ℝ, ∃ U : Set E,
      IsOpen U ∧ x ∈ U ∧
      (∀ i w, (F i w).support ⊆ (P i).support) ∧
      (∀ i d, AnalyticOnNhd ℝ (fun w => (F i w).coeff d) U) ∧
      ∀ i, analyticPolynomialGermHom x (P i) =
        (F i : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  classical
  choose F U hUopen hxU hsupport hanalytic hrep using
    fun i => exists_analyticPolynomialRepresentative x (P i)
  have hall : ∀ᶠ w in 𝓝 x, ∀ i, w ∈ U i :=
    eventually_all.mpr fun i => (hUopen i).mem_nhds (hxU i)
  obtain ⟨V, hV, hVopen, hxV⟩ := eventually_nhds_iff.mp hall
  refine ⟨F, V, hVopen, hxV, hsupport, ?_, hrep⟩
  intro i d w hw
  exact hanalytic i d w (hV w hw i)

/-- Equality in the actual polynomial ring of germs gives eventual equality
of any polynomial-valued representatives. -/
theorem analyticPolynomialRepresentatives_eventually_eq (x : E)
    {P Q : MvPolynomial ι (AnalyticGermAt x)} {F G : E → MvPolynomial ι ℝ}
    (hF : analyticPolynomialGermHom x P = (F : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hG : analyticPolynomialGermHom x Q = (G : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hPQ : P = Q) : F =ᶠ[𝓝 x] G :=
  Germ.coe_eq.mp (hF.symm.trans ((congrArg (analyticPolynomialGermHom x) hPQ).trans hG))

/-- An ideal-membership identity is valid on one neighborhood as a literal
polynomial identity, before assigning any values to the symbols. -/
theorem analyticPolynomialIdentity_eventually {κ : Type*} (x : E) (s : Finset κ)
    (f : MvPolynomial ι (AnalyticGermAt x))
    (a p : κ → MvPolynomial ι (AnalyticGermAt x))
    (F : E → MvPolynomial ι ℝ) (A P : κ → E → MvPolynomial ι ℝ)
    (hF : analyticPolynomialGermHom x f = (F : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hA : ∀ i ∈ s, analyticPolynomialGermHom x (a i) =
      (A i : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hP : ∀ i ∈ s, analyticPolynomialGermHom x (p i) =
      (P i : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hidentity : f = ∑ i ∈ s, a i * p i) :
    ∀ᶠ w in 𝓝 x, F w = ∑ i ∈ s, A i w * P i w := by
  apply Germ.coe_eq.mp
  rw [germ_coe_sum_mul]
  calc
    (F : Germ (𝓝 x) (MvPolynomial ι ℝ)) = analyticPolynomialGermHom x f := hF.symm
    _ = analyticPolynomialGermHom x (∑ i ∈ s, a i * p i) := congrArg _ hidentity
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, hA i hi, hP i hi]

omit [NormedSpace ℝ E] in
/-- A finite family of polynomial equalities has one common open
neighborhood of validity. Its quantifier ranges over every real assignment
of the independent symbols, with no boundedness restriction. -/
theorem exists_open_polynomialIdentities_forall_eval {κ : Type*} [Finite κ]
    (x : E) (F G : κ → E → MvPolynomial ι ℝ)
    (h : ∀ i, F i =ᶠ[𝓝 x] G i) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      (∀ w ∈ U, ∀ i, F i w = G i w) ∧
      ∀ w ∈ U, ∀ i, ∀ z : ι → ℝ,
        MvPolynomial.eval z (F i w) = MvPolynomial.eval z (G i w) := by
  have hall : ∀ᶠ w in 𝓝 x, ∀ i, F i w = G i w := eventually_all.mpr h
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp hall
  refine ⟨U, hUopen, hxU, hU, ?_⟩
  intro w hw i z
  exact congrArg (MvPolynomial.eval z) (hU w hw i)

end AnalyticPolynomialGerms

end AbelFormalization
