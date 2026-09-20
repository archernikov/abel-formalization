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
open scoped Polynomial Topology

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
    rw [J, e.height_map]
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
      (ContinuousLinearMap.proj (R := ℝ) i).analyticAt 0
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
          MvPolynomial.C ((v i) ^ n)) :
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
  apply RingHom.congr_fun
    (MvPolynomial.ringHom_ext (f := MvPolynomial.map (analyticGermValue x))
      (g := (Filter.Germ.valueRingHom).comp
        (analyticPolynomialGermHom x)) (by
          intro c
          change MvPolynomial.C (analyticGermValue x c) = _
          rfl) (by
          intro i
          rw [MvPolynomial.map_X, analyticPolynomialGermHom_X]
          rfl))

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
  exact Multiset.mem_toFinset.mpr ((P i).mem_roots (hP i)).mpr (hx i)

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
    rw [J, phi.toRingEquiv.height_map]
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
  simpa only [phi, MvPolynomial.renameEquiv_apply,
    MvPolynomial.eval₂_rename, reindex, Function.comp_apply,
    e.symm_apply_apply] using hz f hf

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
  simpa only [Fintype.card_option, hn, Nat.add_assoc] using hheight

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
    · simp [mvPolynomialUnitAugmentedTuple, hd0]
    · simp [mvPolynomialUnitAugmentedTuple, hP0]
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
    (hcontrol : ∀ {ι : Type*} [Finite ι] {p : ℕ} (D : RestrictedBox p)
      (representative : ι → Fin 0)
      (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D),
      RestrictedBaseZeroLocalFiniteFiberControl A D representative offset) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 := by
  intro ι _ p D representative offset
  exact restrictedBaseRegularZeroFinite_zero_of_localFiniteFiberControl
    (hcontrol D representative offset)

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
    (hcontrol : ∀ {ι : Type*} [Finite ι] {p : ℕ} (D : RestrictedBox p)
      (representative : ι → Fin 0)
      (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D),
      RestrictedBaseZeroLocalPolynomialControl A D representative offset) :
    RestrictedBaseRegularZeroFiniteForRepresentativeCount A 0 := by
  intro ι _ p D representative offset
  exact restrictedBaseRegularZeroFinite_zero_of_localPolynomialControl
    (hcontrol D representative offset)

end AbelFormalization
