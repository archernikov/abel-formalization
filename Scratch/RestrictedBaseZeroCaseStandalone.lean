import AbelFormalization.RestrictedBaseConvergentSequence
import AbelFormalization.RestrictedBaseFiniteSystemCompression
import AbelFormalization.RestrictedBoxTranslation
import AbelFormalization.AnalyticRankElimination
import AbelFormalization.AnalyticGermGenerators
import AbelFormalization.AnalyticGermPolynomialExtraction
import AbelFormalization.PolynomialGermIdealVanishing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi
import AbelFormalization.RestrictedBasePaperRankElimination

/-!
# The representative-count-zero base case: local algebraic control

This scratch file separates the last geometric/topological part of `P(0,0)`
from the analytic-germ elimination calculation.

The first theorem below records the algebraic consequence of the maintained
height theorem which is needed on the parameter side: an ideal of height at
least `p` in a polynomial ring with no polynomial variables contains a power
of each analytic parameter coordinate.

The second and third results show that coordinatewise nonzero real polynomial
relations give a finite set, and that such relations locally at every limit
point of the closed restricted box imply the full restricted base finiteness
statement for representative count zero.

The remaining construction is therefore a precise local certificate: apply
`exists_analyticRegularZeroElimination` after translating a chosen box point
to the analytic-germ origin, use the first theorem for the parameter
coordinates, and use the full unit-augmented ideal together with
`analyticGerm_polynomial_monic_extraction` for the auxiliary coordinates.
-/

noncomputable section

open Filter Set
open scoped Polynomial Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- A maximum-height analytic-germ ideal with no independent polynomial
variables contains a power of every parameter-coordinate germ. -/
theorem analyticGermCoordinate_pow_mem_of_isEmpty_polynomial_height
    (p : ℕ) {σ : Type*} [Fintype σ] [IsEmpty σ]
    (I : Ideal (MvPolynomial σ (RealAnalyticGerm p)))
    (hI : (p : ℕ∞) ≤ I.height) (i : Fin p) :
    ∃ n : ℕ, MvPolynomial.C (analyticGermCoordinate p i) ^ n ∈ I := by
  let e : MvPolynomial σ (RealAnalyticGerm p) ≃+* RealAnalyticGerm p :=
    MvPolynomial.isEmptyRingEquiv (RealAnalyticGerm p) σ
  let J : Ideal (RealAnalyticGerm p) := I.map e.toRingHom
  have hJ : (p : ℕ∞) ≤ J.height := by
    have he : (I.map e.toRingHom).height = I.height := e.height_map I
    rw [he]
    exact hI
  have hnat (n : ℕ) :
      (n : WithBot ℕ∞) ≠ ⊥ ∧ (n : WithBot ℕ∞) ≠ ⊤ := by
    refine ⟨by simp, ?_⟩
    change ((n : ℕ∞) : WithBot ℕ∞) ≠ ⊤
    exact fun h => ENat.natCast_ne_top n (WithBot.coe_eq_top.mp h)
  let : FiniteRingKrullDim (RealAnalyticGerm p) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr
      ((realAnalyticGerm_dimension p) ▸ hnat p)
  have hrad : analyticGermCoordinate p i ∈ J.radical := by
    rw [← J.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    letI : P.IsPrime := hP.isPrime
    have hlower : (p : ℕ∞) ≤ P.height :=
      hJ.trans (Ideal.height_mono hP.le)
    have hheight :
        (P.height : WithBot ℕ∞) = ringKrullDim (RealAnalyticGerm p) := by
      apply le_antisymm Ideal.height_le_ringKrullDim_of_isPrime
      rw [realAnalyticGerm_dimension p]
      exact_mod_cast hlower
    have hPmax : P = IsLocalRing.maximalIdeal (RealAnalyticGerm p) :=
      Ideal.height_eq_ringKrullDim_iff.mp hheight
    rw [hPmax]
    exact (analyticGerm_mem_maximalIdeal_iff
      (analyticGermCoordinate p i)).mpr rfl
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨n, ?_⟩
  have hpre : e.symm ((analyticGermCoordinate p i) ^ n) ∈ I :=
    (Ideal.symm_apply_mem_of_equiv_iff
      (I := I) (f := e) (y := (analyticGermCoordinate p i) ^ n)).2 hn
  simpa only [e, MvPolynomial.isEmptyRingEquiv_symm_apply, map_pow] using hpre

/-- Finite analytic representatives of a height-`p` ideal with no retained
polynomial variables isolate the analytic parameter origin.  This is the
direct output needed from the contracted ideal returned by
`exists_analyticRegularZeroElimination`. -/
theorem eventually_parameter_eq_zero_of_isEmpty_polynomial_height
    (p : ℕ) {σ κ : Type*} [Fintype σ] [IsEmpty σ] [Fintype κ]
    (I : Ideal (MvPolynomial σ (RealAnalyticGerm p)))
    (hI : (p : ℕ∞) ≤ I.height)
    (g : κ → MvPolynomial σ (RealAnalyticGerm p))
    (G : κ → (Fin p → ℝ) → MvPolynomial σ ℝ)
    (hspan : Ideal.span (Set.range g) = I)
    (hG : ∀ j, analyticPolynomialGermHom (0 : Fin p → ℝ) (g j) =
      (G j : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial σ ℝ))) :
    ∀ᶠ v in 𝓝 (0 : Fin p → ℝ), ∀ z : σ → ℝ,
      (∀ j, MvPolynomial.eval z (G j v) = 0) → v = 0 := by
  have hi (i : Fin p) :
      ∀ᶠ v in 𝓝 (0 : Fin p → ℝ), ∀ z : σ → ℝ,
        (∀ j, MvPolynomial.eval z (G j v) = 0) → v i = 0 := by
    obtain ⟨n, hn⟩ :=
      analyticGermCoordinate_pow_mem_of_isEmpty_polynomial_height p I hI i
    have hcoord : AnalyticAt ℝ (fun v : Fin p → ℝ => v i) 0 :=
      ((ContinuousLinearMap.proj (R := ℝ) i :
        (Fin p → ℝ) →L[ℝ] ℝ).analyticAt 0)
    have hpow : AnalyticAt ℝ (fun v : Fin p → ℝ => (v i) ^ n) 0 :=
      hcoord.pow n
    have hgerm :
        (analyticGermCoordinate p i) ^ n =
          analyticGermOf (fun v : Fin p → ℝ => (v i) ^ n) hpow := by
      unfold analyticGermCoordinate
      apply Subtype.ext
      exact Germ.coe_eq.mpr (Eventually.of_forall fun v => rfl)
    have hrep : analyticPolynomialGermHom (0 : Fin p → ℝ)
          (MvPolynomial.C (analyticGermCoordinate p i) ^ n) =
        ((fun v : Fin p → ℝ =>
          (MvPolynomial.C ((v i) ^ n) : MvPolynomial σ ℝ)) :
          Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial σ ℝ)) := by
      have hmono := analyticPolynomialGermHom_monomial_of
        (ι := σ) (0 : Fin p → ℝ) (0 : σ →₀ ℕ)
        (fun v : Fin p → ℝ => (v i) ^ n) hpow
      rw [← MvPolynomial.C_pow, hgerm]
      simpa only [MvPolynomial.C_apply] using hmono
    have hmem : MvPolynomial.C (analyticGermCoordinate p i) ^ n ∈
        Ideal.span (Set.range g) := by
      rw [hspan]
      exact hn
    have hevent := analyticPolynomial_mem_span_eventually_vanish
      (0 : Fin p → ℝ) g
      (MvPolynomial.C (analyticGermCoordinate p i) ^ n) G
      (fun v : Fin p → ℝ => MvPolynomial.C ((v i) ^ n))
      hG hrep hmem
    filter_upwards [hevent] with v hv
    intro z hz
    have hvpow := hv z hz
    simp only [MvPolynomial.eval_C] at hvpow
    exact eq_zero_of_pow_eq_zero hvpow
  have hall :
      ∀ᶠ v in 𝓝 (0 : Fin p → ℝ), ∀ i : Fin p, ∀ z : σ → ℝ,
        (∀ j, MvPolynomial.eval z (G j v) = 0) → v i = 0 :=
    eventually_all.mpr hi
  filter_upwards [hall] with v hv
  intro z hz
  funext i
  exact hv i z hz

/-- Taking the value at the base point of a polynomial-valued analytic germ
is coefficientwise analytic-germ evaluation.  This is the specialization
adapter needed for the full unit-augmented ideal. -/
theorem map_analyticGermValue_eq_value_analyticPolynomialGermHom
    {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (P : MvPolynomial σ (AnalyticGermAt x)) :
    MvPolynomial.map (analyticGermValue x) P =
      Filter.Germ.value (analyticPolynomialGermHom x P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative c
      rw [MvPolynomial.map_monomial, analyticGermValue_of,
        analyticPolynomialGermHom_monomial_of]
      rfl
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      exact (map_add (Filter.Germ.valueRingHom) _ _).symm

/-- A displayed polynomial-valued representative specializes at its base
point to coefficientwise analytic-germ evaluation. -/
theorem map_analyticGermValue_eq_of_analyticPolynomialGermHom_eq
    {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (P : MvPolynomial σ (AnalyticGermAt x))
    (F : E → MvPolynomial σ ℝ)
    (hF : analyticPolynomialGermHom x P =
      (F : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    MvPolynomial.map (analyticGermValue x) P = F x := by
  rw [map_analyticGermValue_eq_value_analyticPolynomialGermHom, hF]
  rfl

/-- The common zero set of one nonzero univariate polynomial in every
coordinate of a finite real tuple is finite. -/
theorem finite_pi_of_coordinatewise_polynomial_eq_zero
    {n : ℕ} (P : Fin n → ℝ[X]) (hP : ∀ i, P i ≠ 0) :
    {x : Fin n → ℝ | ∀ i, (P i).eval (x i) = 0}.Finite := by
  let roots : Fin n → Set ℝ := fun i => ((P i).roots.toFinset : Set ℝ)
  have hroots : ∀ i, (roots i).Finite := fun i => Finset.finite_toSet _
  refine (Set.Finite.pi' hroots).subset ?_
  intro x hx i
  change x i ∈ (P i).roots.toFinset
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hP i)]
  simpa only [Polynomial.IsRoot.def] using hx i

/-- A maximum-height ideal in analytic-germ polynomials has only finitely
many common zeros after specializing the germ coefficients at the origin.
This packages the auxiliary-coordinate use of
`analyticGerm_polynomial_monic_extraction`. -/
theorem finite_specialized_commonZero_of_analyticGerm_height
    (p m : ℕ)
    (I : Ideal (MvPolynomial (Fin m) (RealAnalyticGerm p)))
    (hI : (p + m : ℕ∞) ≤ I.height) :
    {z : Fin m → ℝ |
      ∀ f ∈ I, MvPolynomial.eval₂
        (analyticGermValueAlgHom (0 : Fin p → ℝ)).toRingHom z f = 0}.Finite := by
  choose q hqmonic hqmem using fun i : Fin m =>
    analyticGerm_polynomial_monic_extraction p m I hI i
  apply (finite_pi_of_coordinatewise_polynomial_eq_zero q
    (fun i => (hqmonic i).ne_zero)).subset
  intro z hz i
  have hzero := hz
    (scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i (q i)) (hqmem i)
  rw [MvPolynomial.eval₂_eq_eval_map,
    map_scalarUnivariateEmbedding,
    MvPolynomial.eval_toMvPolynomial] at hzero
  exact hzero

/-- The preceding finite-common-zero theorem for an arbitrary finite symbol
type.  Reindexing by `Fintype.equivFin` is the only extra step. -/
theorem finite_specialized_commonZero_of_analyticGerm_height_fintype
    (p : ℕ) {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ (RealAnalyticGerm p)))
    (hI : (p + Fintype.card σ : ℕ∞) ≤ I.height) :
    {z : σ → ℝ |
      ∀ f ∈ I, MvPolynomial.eval₂
        (analyticGermValueAlgHom (0 : Fin p → ℝ)).toRingHom z f = 0}.Finite := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let phi : MvPolynomial σ (RealAnalyticGerm p) ≃ₐ[RealAnalyticGerm p]
      MvPolynomial (Fin (Fintype.card σ)) (RealAnalyticGerm p) :=
    MvPolynomial.renameEquiv (RealAnalyticGerm p) e
  let J : Ideal
      (MvPolynomial (Fin (Fintype.card σ)) (RealAnalyticGerm p)) :=
    I.map phi.toRingHom
  have hJ : (p + Fintype.card σ : ℕ∞) ≤ J.height := by
    have hphi : (I.map phi.toRingEquiv.toRingHom).height = I.height :=
      phi.toRingEquiv.height_map I
    rw [hphi]
    exact hI
  have hfinite :=
    finite_specialized_commonZero_of_analyticGerm_height
      p (Fintype.card σ) J hJ
  let reindex : (σ → ℝ) → Fin (Fintype.card σ) → ℝ :=
    fun z => z ∘ e.symm
  have hreindex : Function.Injective reindex := by
    intro z z' hzz'
    funext i
    have hi := congrFun hzz' (e i)
    simpa only [reindex, Function.comp_apply, e.symm_apply_apply] using hi
  apply Set.Finite.of_finite_image
    (f := reindex) (hfinite.subset ?_) hreindex.injOn
  rintro v ⟨z, hz, rfl⟩
  intro Q hQ
  obtain ⟨f, hf, hphi⟩ :=
    (Ideal.mem_map_of_equiv phi Q).mp hQ
  subst Q
  change MvPolynomial.eval₂
      (analyticGermValueAlgHom (0 : Fin p → ℝ)).toRingHom
      (reindex z) (MvPolynomial.rename e f) = 0
  rw [MvPolynomial.eval₂_rename]
  have hreindexComp : reindex z ∘ e = z := by
    funext i
    simp only [reindex, Function.comp_apply, e.symm_apply_apply]
  rw [hreindexComp]
  exact hz f hf

/-- When the number of equations is the parameter dimension plus the number
of independent polynomial symbols, the unit-augmented Jacobian ideal has a
finite specialized common-zero set. -/
theorem finite_specialized_commonZero_unitAugmentedJacobian
    (p n : ℕ) {σ γ : Type*} [Fintype σ] [Fintype γ]
    (hn : n = p + Fintype.card σ)
    (P : Fin n → MvPolynomial σ (RealAnalyticGerm p))
    (D : γ → Derivation ℝ
      (MvPolynomial σ (RealAnalyticGerm p))
      (MvPolynomial σ (RealAnalyticGerm p))) :
    {z : Option σ → ℝ |
      ∀ f ∈ mvPolynomialUnitAugmentedIdeal P
          (derivationJacobianDenominator P D),
        MvPolynomial.eval₂
          (analyticGermValueAlgHom (0 : Fin p → ℝ)).toRingHom z f = 0}.Finite := by
  apply finite_specialized_commonZero_of_analyticGerm_height_fintype p
  have hheight := mvPolynomialUnitAugmentedIdeal_height P D
  have hcard : p + Fintype.card (Option σ) = n + 1 := by
    simp only [Fintype.card_option, hn, Nat.add_assoc]
  have hcard' : (p : ℕ∞) + (Fintype.card (Option σ) : ℕ∞) =
      ((n + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast hcard
  rw [hcard']
  exact hheight

/-- At the germ origin, an actual zero with nonzero Jacobian denominator
annihilates the full unit-augmented ideal.  The conclusion uses `eval₂`, so
the independent polynomial coordinates remain arbitrary real values. -/
theorem mvPolynomialUnitAugmentedIdeal_le_ker_eval₂_analyticGermValue
    (p n : ℕ) {σ : Type*}
    (P : Fin n → MvPolynomial σ (RealAnalyticGerm p))
    (d : MvPolynomial σ (RealAnalyticGerm p))
    (PRep : Fin n → (Fin p → ℝ) → MvPolynomial σ ℝ)
    (dRep : (Fin p → ℝ) → MvPolynomial σ ℝ)
    (hP : ∀ i, analyticPolynomialGermHom (0 : Fin p → ℝ) (P i) =
      (PRep i : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial σ ℝ)))
    (hd : analyticPolynomialGermHom (0 : Fin p → ℝ) d =
      (dRep : Germ (𝓝 (0 : Fin p → ℝ)) (MvPolynomial σ ℝ)))
    (z : σ → ℝ)
    (hzero : ∀ i, MvPolynomial.eval z (PRep i 0) = 0)
    (hdenominator : MvPolynomial.eval z (dRep 0) ≠ 0) :
    mvPolynomialUnitAugmentedIdeal P d ≤
      RingHom.ker (MvPolynomial.eval₂Hom
        (analyticGermValueAlgHom (0 : Fin p → ℝ)).toRingHom
        (fun o : Option σ => o.elim
          (MvPolynomial.eval z (dRep 0))⁻¹ z)) := by
  have hP0 : ∀ i, MvPolynomial.map
      (analyticGermValue (0 : Fin p → ℝ)) (P i) = PRep i 0 := by
    intro i
    exact map_analyticGermValue_eq_of_analyticPolynomialGermHom_eq
      (0 : Fin p → ℝ) (P i) (PRep i) (hP i)
  have hd0 : MvPolynomial.map
      (analyticGermValue (0 : Fin p → ℝ)) d = dRep 0 :=
    map_analyticGermValue_eq_of_analyticPolynomialGermHom_eq
      (0 : Fin p → ℝ) d dRep hd
  apply Ideal.span_le.mpr
  rintro q ⟨i, rfl⟩
  change MvPolynomial.eval₂
      (analyticGermValue (0 : Fin p → ℝ))
      (fun o : Option σ => o.elim
        (MvPolynomial.eval z (dRep 0))⁻¹ z)
      (mvPolynomialUnitAugmentedTuple P d i) = 0
  rw [MvPolynomial.eval₂_eq_eval_map]
  have hmap : MvPolynomial.map
        (analyticGermValue (0 : Fin p → ℝ))
        (mvPolynomialUnitAugmentedTuple P d i) =
      mvPolynomialUnitAugmentedTuple (fun j => PRep j 0) (dRep 0) i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mvPolynomialUnitAugmentedTuple, MvPolynomial.map_rename, hd0]
    · simp [mvPolynomialUnitAugmentedTuple, MvPolynomial.map_rename, hP0]
  rw [hmap]
  exact mvPolynomialUnitAugmentedTuple_eval_zero
    (fun j => PRep j 0) (dRep 0) z
    (MvPolynomial.eval z (dRep 0))⁻¹ hzero
    (inv_mul_cancel₀ hdenominator) i

/-- In representative dimension zero, coordinatewise nonzero polynomial
relations on the bounded and auxiliary coordinates force finiteness.  The
first `Fin 0` coordinate carries no information. -/
theorem finite_restrictedSource_zero_of_coordinatewise_polynomial_eq_zero
    {p a : ℕ} (Z : Set (RestrictedSource 0 p a))
    (w₀ : RestrictedBoxSpace p)
    (Pw : Fin p → ℝ[X]) (Py : Fin a → ℝ[X])
    (hPw : ∀ i, Pw i ≠ 0) (hPy : ∀ i, Py i ≠ 0)
    (hZ : ∀ x ∈ Z,
      (∀ i, (Pw i).eval (x.1.2 i - w₀ i) = 0) ∧
      ∀ i, (Py i).eval (x.2 i) = 0) :
    Z.Finite := by
  let W : Set (Fin p → ℝ) :=
    {w | ∀ i, (Pw i).eval (w i - w₀ i) = 0}
  let Y : Set (Fin a → ℝ) :=
    {y | ∀ i, (Py i).eval (y i) = 0}
  have hW : W.Finite := by
    let shift : (Fin p → ℝ) → (Fin p → ℝ) := fun w i => w i - w₀ i
    have htarget :
        {v : Fin p → ℝ | ∀ i, (Pw i).eval (v i) = 0}.Finite :=
      finite_pi_of_coordinatewise_polynomial_eq_zero Pw hPw
    have hinj : Function.Injective shift := by
      intro u v huv
      funext i
      have hi := congrFun huv i
      dsimp only [shift] at hi
      linarith
    apply Set.Finite.of_finite_image
      (f := shift) (htarget.subset ?_) hinj.injOn
    rintro v ⟨w, hw, rfl⟩
    exact hw
  have hY : Y.Finite :=
    finite_pi_of_coordinatewise_polynomial_eq_zero Py hPy
  let projection : RestrictedSource 0 p a →
      (Fin p → ℝ) × (Fin a → ℝ) := fun x => (x.1.2, x.2)
  have hprojection : Function.Injective projection := by
    rintro ⟨⟨s, w⟩, y⟩ ⟨⟨s', w'⟩, y'⟩ h
    change (w, y) = (w', y') at h
    obtain ⟨rfl, rfl⟩ := h
    have hs : s = s' := Subsingleton.elim _ _
    subst s'
    rfl
  apply Set.Finite.of_finite_image
    (f := projection) ((hW.prod hY).subset ?_) hprojection.injOn
  rintro z ⟨x, hx, rfl⟩
  exact hZ x hx

/-- With representative dimension zero, fixing the bounded parameter and
placing the auxiliary tuple in a finite set makes the source set finite. -/
theorem finite_restrictedSource_zero_of_fixed_parameter_finite_aux
    {p a : ℕ} (Z : Set (RestrictedSource 0 p a))
    (w₀ : RestrictedBoxSpace p) (Y : Set (Fin a → ℝ)) (hY : Y.Finite)
    (hZ : ∀ x ∈ Z, x.1.2 = w₀ ∧ x.2 ∈ Y) :
    Z.Finite := by
  let aux : RestrictedSource 0 p a → (Fin a → ℝ) := fun x => x.2
  have haux : Set.InjOn aux Z := by
    intro x hx y hy hxy
    rcases x with ⟨⟨s, w⟩, z⟩
    rcases y with ⟨⟨s', w'⟩, z'⟩
    change z = z' at hxy
    obtain rfl := hxy
    have hw : w = w' := (hZ _ hx).1.trans (hZ _ hy).1.symm
    subst w'
    have hs : s = s' := Subsingleton.elim _ _
    subst s'
    rfl
  apply Set.Finite.of_finite_image
    (f := aux) (hY.subset ?_) haux
  rintro z ⟨x, hx, rfl⟩
  exact (hZ x hx).2

/-- The local finite-fiber conclusion produced directly by the contracted
and full unit-augmented ideals. -/
def RestrictedBaseZeroLocalFiniteFiberControl
    (A : ℝ → ℝ) {ι : Type*} {p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin 0)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) : Prop :=
  ∀ {a : ℕ} (R : ℝ)
    (_hDomain : restrictedBaseClosedDomain (m := 0) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin ((0 + p) + a) → RestrictedSource 0 p a → ℝ),
    (∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) →
    ∀ w₀ ∈ D.closedBox,
      ∃ U : Set (RestrictedBoxSpace p), U ∈ 𝓝 w₀ ∧
      ∃ Y : Set (Fin a → ℝ), Y.Finite ∧
        ∀ x ∈ regularZeroSet (restrictedBaseOpenDomain D R)
            (constraintMap F),
          x.1.2 ∈ U → x.1.2 = w₀ ∧ x.2 ∈ Y

/-- The exact local finite-fiber output of analytic elimination closes the
fixed-data representative-count-zero base assertion. -/
theorem restrictedBaseRegularZeroFinite_zero_of_localFiniteFiberControl
    {A : ℝ → ℝ} {ι : Type*} {p : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin 0}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (hcontrol : RestrictedBaseZeroLocalFiniteFiberControl
      A D representative offset) :
    RestrictedBaseRegularZeroFinite A D representative offset := by
  rw [restrictedBaseRegularZeroFinite_iff_no_boxConvergent_sequence]
  intro a R hDomain F hF x w₀ hxinj hxmem hw₀ hlim
  obtain ⟨U, hU, Y, hY, hlocal⟩ :=
    hcontrol R hDomain F hF w₀ hw₀
  have hevent : ∀ᶠ n in atTop, (x n).1.2 ∈ U := hlim hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let y : ℕ → RestrictedSource 0 p a := fun n => x (N + n)
  have hyinj : Function.Injective y := by
    intro n k hnk
    exact Nat.add_left_cancel (hxinj hnk)
  let Z : Set (RestrictedSource 0 p a) :=
    {z | z ∈ regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F) ∧ z.1.2 ∈ U}
  have hZfinite : Z.Finite :=
    finite_restrictedSource_zero_of_fixed_parameter_finite_aux
      Z w₀ Y hY (by
        intro z hz
        exact hlocal z hz.1 hz.2)
  have hymem : ∀ n, y n ∈ Z := by
    intro n
    exact ⟨hxmem (N + n), hN (N + n) (Nat.le_add_right N n)⟩
  exact (Set.infinite_of_injective_forall_mem hyinj hymem) hZfinite

/-- Uniform local finite-fiber control is exactly enough for the global
representative-count-zero assertion. -/
theorem restrictedBaseRegularZeroFiniteForRepresentativeCount_zero_of_localFiniteFiberControl
    {A : ℝ → ℝ}
    (hcontrol : ∀ {ι : Type} [Finite ι] {p : ℕ} (D : RestrictedBox p)
      (representative : ι → Fin 0)
      (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D),
      RestrictedBaseZeroLocalFiniteFiberControl A D representative offset) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 := by
  intro ι _ p D representative offset
  exact restrictedBaseRegularZeroFinite_zero_of_localFiniteFiberControl
    (hcontrol (ι := ι) (p := p) D representative offset)

/-- The exact local certificate left by analytic elimination in the
representative-count-zero case.  The bounded-coordinate relations are
centered at `w₀`, matching translation to `RealAnalyticGerm p`; the
auxiliary relations are ordinary real polynomial equations. -/
def RestrictedBaseZeroLocalPolynomialControl
    (A : ℝ → ℝ) {ι : Type*} {p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin 0)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) : Prop :=
  ∀ {a : ℕ} (R : ℝ)
    (_hDomain : restrictedBaseClosedDomain (m := 0) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin ((0 + p) + a) → RestrictedSource 0 p a → ℝ),
    (∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) →
    ∀ w₀ ∈ D.closedBox,
      ∃ U : Set (RestrictedBoxSpace p), U ∈ 𝓝 w₀ ∧
      ∃ Pw : Fin p → ℝ[X], ∃ Py : Fin a → ℝ[X],
        (∀ i, Pw i ≠ 0) ∧ (∀ i, Py i ≠ 0) ∧
        ∀ x ∈ regularZeroSet (restrictedBaseOpenDomain D R)
            (constraintMap F),
          x.1.2 ∈ U →
            (∀ i, (Pw i).eval (x.1.2 i - w₀ i) = 0) ∧
            ∀ i, (Py i).eval (x.2 i) = 0

/-- Local coordinate-polynomial control at every point of the compact
closed box proves the full fixed-data level-zero assertion. -/
theorem restrictedBaseRegularZeroFinite_zero_of_localPolynomialControl
    {A : ℝ → ℝ} {ι : Type*} {p : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin 0}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (hcontrol : RestrictedBaseZeroLocalPolynomialControl
      A D representative offset) :
    RestrictedBaseRegularZeroFinite A D representative offset := by
  rw [restrictedBaseRegularZeroFinite_iff_no_boxConvergent_sequence]
  intro a R hDomain F hF x w₀ hxinj hxmem hw₀ hlim
  obtain ⟨U, hU, Pw, Py, hPw, hPy, hrelations⟩ :=
    hcontrol R hDomain F hF w₀ hw₀
  have hevent : ∀ᶠ n in atTop, (x n).1.2 ∈ U := hlim hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let y : ℕ → RestrictedSource 0 p a := fun n => x (N + n)
  have hyinj : Function.Injective y := by
    intro n k hnk
    exact Nat.add_left_cancel (hxinj hnk)
  let Z : Set (RestrictedSource 0 p a) :=
    {z | z ∈ regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F) ∧ z.1.2 ∈ U}
  have hZfinite : Z.Finite :=
    finite_restrictedSource_zero_of_coordinatewise_polynomial_eq_zero
      Z w₀ Pw Py hPw hPy (by
        intro z hz
        exact hrelations z hz.1 hz.2)
  have hymem : ∀ n, y n ∈ Z := by
    intro n
    exact ⟨hxmem (N + n), hN (N + n) (Nat.le_add_right N n)⟩
  exact (Set.infinite_of_injective_forall_mem hyinj hymem) hZfinite

/-- A uniform local certificate proves the global representative-count-zero
base assertion.  This is the smallest remaining target for the elimination
adapter, with no o-minimality hypothesis. -/
theorem restrictedBaseRegularZeroFiniteForRepresentativeCount_zero_of_localPolynomialControl
    {A : ℝ → ℝ}
    (hcontrol : ∀ {ι : Type} [Finite ι] {p : ℕ} (D : RestrictedBox p)
      (representative : ι → Fin 0)
      (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D),
      RestrictedBaseZeroLocalPolynomialControl A D representative offset) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 := by
  intro ι _ p D representative offset
  exact restrictedBaseRegularZeroFinite_zero_of_localPolynomialControl
    (hcontrol (ι := ι) (p := p) D representative offset)

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
      (𝓝 (0 : RestrictedBoxSpace p)) := by
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
  simp only [Finset.card_empty, Nat.zero_add] at hC hQ hI hheight hspan hsupport hanalytic hG hvanish
  letI : IsEmpty
      (PaperRankRetainedSymbols 0 (∅ : Finset (ι × ℕ)).card) :=
    ⟨fun s ↦ s.elim Fin.elim0 Fin.elim0⟩

  have hheightI : (p : ℕ∞) ≤ I.height := by
    exact hheight
  have hparameterLocal :
      ∀ᶠ v in 𝓝 (0 : RestrictedBoxSpace p),
        ∀ z : PaperRankRetainedSymbols 0
            (∅ : Finset (ι × ℕ)).card → ℝ,
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
          (restrictedJetEnumeration (∅ : Finset (ι × ℕ)))) (x₀ n)) hzero

  let P : Fin ((0 + p) + a) →
      MvPolynomial (PaperRankSymbols 0 a
        (∅ : Finset (ι × ℕ)).card) (RealAnalyticGerm p) :=
    fun i ↦ restrictedPaperGermPolynomial D₀ h0D₀ (Q i)
  let coeff : Fin ((0 + p) + a) →
      (PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card →₀ ℕ) →
      RestrictedBoxSpace p → ℝ :=
    restrictedPaperCoefficientRepresentative Q
  let PRep : Fin ((0 + p) + a) → RestrictedBoxSpace p →
      MvPolynomial (PaperRankSymbols 0 a
        (∅ : Finset (ι × ℕ)).card) ℝ :=
    fun i ↦ polynomialFromCoefficientRepresentatives
      (P i).support (coeff i)
  let d : MvPolynomial
      (PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card)
      (RealAnalyticGerm p) :=
    derivationJacobianDenominator P (analyticGermFormalDerivations p)
  let dRep : RestrictedBoxSpace p →
      MvPolynomial (PaperRankSymbols 0 a
        (∅ : Finset (ι × ℕ)).card) ℝ :=
    analyticGermJacobianDenominatorRepresentative P coeff
  let V : PaperRankParameterSpace 0 p →
      PaperRankRealSpace (∅ : Finset (ι × ℕ)).card :=
    restrictedSelectedAbelJets A representative offset₀
      (restrictedJetEnumeration (∅ : Finset (ι × ℕ)))

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
        (PRep i : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankSymbols 0 a
            (∅ : Finset (ι × ℕ)).card) ℝ)) := by
    intro i
    exact analyticPolynomialGermHom_eq_coefficientRepresentative
      (0 : RestrictedBoxSpace p) (P i) (coeff i) (hcoeff0 i) (hrep i)
  have hdRep :
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p) d =
        (dRep : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankSymbols 0 a
            (∅ : Finset (ι × ℕ)).card) ℝ)) := by
    exact analyticPolynomialGermHom_formalJacobianDenominator
      P coeff hcoeff0 hrep

  let J : Ideal
      (MvPolynomial
        (Option (PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card))
        (RealAnalyticGerm p)) :=
    mvPolynomialUnitAugmentedIdeal P d
  let Z : Set
      (Option (PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card) → ℝ) :=
    {z | ∀ f ∈ J,
      MvPolynomial.eval₂
        (analyticGermValueAlgHom (0 : RestrictedBoxSpace p)).toRingHom z f = 0}
  have hZfinite : Z.Finite := by
    dsimp only [Z, J, d]
    apply finite_specialized_commonZero_unitAugmentedJacobian
      p ((0 + p) + a)
        (σ := PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card)
        (γ := Fin p ⊕ PaperRankSymbols 0 a
          (∅ : Finset (ι × ℕ)).card)
        (P := P) (D := analyticGermFormalDerivations p)
    rw [Fintype.card_congr (Equiv.sumEmpty (Fin a)
      (PaperRankRetainedSymbols 0 (∅ : Finset (ι × ℕ)).card))]
    simp only [Fintype.card_fin, Nat.zero_add]

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
        (restrictedJetEnumeration (∅ : Finset (ι × ℕ))) Ω Set.inter_subset_left
  have heqOn : ∀ y ∈ Ω,
      paperRankEquation P coeff V y = constraintMap F₀ y := by
    intro y hy
    exact paperRankEquation_restricted_eq_constraintMap
      A D₀ h0D₀ representative offset₀
        (restrictedJetEnumeration (∅ : Finset (ι × ℕ)))
        Q F₀ hQ W₀ hpolyW₀ y hy.2

  let augmentedAssignment : ℕ →
      Option (PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card) → ℝ :=
    fun n o ↦ o.elim
      (MvPolynomial.eval (paperRankSymbolArgument V (x₀ n))
        (dRep 0))⁻¹
      (paperRankSymbolArgument V (x₀ n))
  have haugmented : ∀ᶠ n in atTop, augmentedAssignment n ∈ Z := by
    filter_upwards [hparameterSequence] with n hn
    have hxnΩ : x₀ n ∈ Ω := by
      refine ⟨(hx₀ n).1, ?_⟩
      change (x₀ n).1.2 ∈ W₀
      rw [hn]
      exact h0W₀
    have hzeroPaper : paperRankEquation P coeff V (x₀ n) = 0 := by
      rw [heqOn (x₀ n) hxnΩ]
      exact (hx₀ n).2.1
    have heventuallyEq : paperRankEquation P coeff V =ᶠ[𝓝 (x₀ n)]
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
        p ((0 + p) + a) P d PRep dRep hPRep hdRep
        (paperRankSymbolArgument V (x₀ n)) hzeroRep hdenominator
    intro f hf
    exact hker hf

  have hboth : ∀ᶠ n in atTop,
      (x₀ n).1.2 = 0 ∧ augmentedAssignment n ∈ Z :=
    hparameterSequence.and haugmented
  obtain ⟨N, hN⟩ := eventually_atTop.mp hboth
  let tailAssignment : ℕ →
      Option (PaperRankSymbols 0 a (∅ : Finset (ι × ℕ)).card) → ℝ :=
    fun n ↦ augmentedAssignment (N + n)
  have htailInjective : Function.Injective tailAssignment := by
    intro n k hnk
    have hnData := hN (N + n) (Nat.le_add_right N n)
    have hkData := hN (N + k) (Nat.le_add_right N k)
    have hy : (x₀ (N + n)).2 = (x₀ (N + k)).2 := by
      funext i
      have hi := congrFun hnk (some (Sum.inl i))
      simpa only [tailAssignment, augmentedAssignment,
        Option.elim_some, paperRankSymbolArgument_aux] using hi
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
