import AbelFormalization.MaxwellFirstOrderAnalyticAdapter
import AbelFormalization.MaxwellScalarDiscontinuity
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Maxwell's chosen representative: the differentiability mechanism

This file separates the two parts of Figueiredo--Maxwell Lemma 2.3.10.

First, it proves the finite-dimensional calculus statement used at the end
of the lemma: continuous coordinate line derivatives on an open set imply
Fréchet differentiability there.  Second, it records the genuinely
slope-theoretic input in its pointwise form, namely existence of the
coordinate line derivatives of the canonical representative.  Continuity
of those derivatives is not retained as a source hypothesis: it follows
from closedness and single-valuedness of the zero-step trace, together with
the elementary bounded/unbounded sequence dichotomy already proved in
`MaxwellScalarDiscontinuity`.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Continuous coordinate line derivatives imply differentiability -/

/-- The continuous linear functional whose values on the standard basis are
the prescribed coordinate derivatives. -/
def maxwellCoordinateDifferential {p : ℕ}
    (d : Fin p → RealEuclidean p → ℝ)
    (x : RealEuclidean p) : RealEuclidean p →L[ℝ] ℝ :=
  continuousLinearMapFromBasis (Pi.basisFun ℝ (Fin p))
    (fun i ↦ d i x)

@[simp]
theorem maxwellCoordinateDifferential_apply_basis {p : ℕ}
    (d : Fin p → RealEuclidean p → ℝ)
    (x : RealEuclidean p) (i : Fin p) :
    maxwellCoordinateDifferential d x
        ((Pi.basisFun ℝ (Fin p)) i) = d i x := by
  exact continuousLinearMapFromBasis_apply_basis
    (Pi.basisFun ℝ (Fin p)) (fun j ↦ d j x) i

private theorem fin_castSucc_eq_castAdd_one {p : ℕ} (i : Fin p) :
    i.castSucc = Fin.castAdd 1 i := by
  apply Fin.ext
  rfl

private theorem fin_natAdd_zero_eq_last (p : ℕ) :
    Fin.natAdd p (0 : Fin 1) = Fin.last p := by
  apply Fin.ext
  rfl

private theorem fin_castAdd_one_ne_last {p : ℕ} (i : Fin p) :
    Fin.castAdd 1 i ≠ Fin.last p := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

/-- Splitting off the last coordinate sends an old standard basis vector to
the corresponding product basis vector. -/
private theorem realEuclideanAppendLinearEquiv_symm_basis_castSucc
    {p : ℕ} (i : Fin p) :
    (realEuclideanAppendLinearEquiv p 1).symm
        ((Pi.basisFun ℝ (Fin (p + 1))) i.castSucc) =
      ((Pi.basisFun ℝ (Fin p)) i, (0 : RealEuclidean 1)) := by
  ext j
  · simp [realEuclideanAppendLinearEquiv, realEuclideanTakeLeft,
      Pi.basisFun_apply, Pi.single_apply,
      fin_castSucc_eq_castAdd_one, Fin.castAdd_inj]
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp [realEuclideanAppendLinearEquiv, realEuclideanTakeRight,
      Pi.basisFun_apply, Pi.single_apply,
      fin_castSucc_eq_castAdd_one, fin_natAdd_zero_eq_last,
      fin_castAdd_one_ne_last]

/-- Splitting off the last coordinate sends the last standard basis vector
to the scalar product basis vector. -/
private theorem realEuclideanAppendLinearEquiv_symm_basis_last
    (p : ℕ) :
    (realEuclideanAppendLinearEquiv p 1).symm
        ((Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p)) =
      ((0 : RealEuclidean p), (1 : RealEuclidean 1)) := by
  ext j
  · simp [realEuclideanAppendLinearEquiv, realEuclideanTakeLeft,
      Pi.basisFun_apply, Pi.single_apply, fin_castAdd_one_ne_last]
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp [realEuclideanAppendLinearEquiv, realEuclideanTakeRight,
      Pi.basisFun_apply, Pi.single_apply, fin_natAdd_zero_eq_last]

/-- A first-block coordinate line in product coordinates is the same line
after flattening. -/
private theorem realEuclideanAppend_add_basis_castSucc
    {p : ℕ} (a : RealEuclidean p) (b : RealEuclidean 1)
    (i : Fin p) (t : ℝ) :
    realEuclideanAppend
        (a + t • (Pi.basisFun ℝ (Fin p)) i) b =
      realEuclideanAppend a b +
        t • (Pi.basisFun ℝ (Fin (p + 1))) i.castSucc := by
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp [realEuclideanAppend_last_one, Pi.basisFun_apply,
      Pi.single_apply, fin_castSucc_eq_castAdd_one,
      fin_castAdd_one_ne_last]
  · simp [realEuclideanAppend_castAdd, Pi.basisFun_apply,
      Pi.single_apply, fin_castSucc_eq_castAdd_one, Fin.castAdd_inj]

/-- The scalar line in the second product factor is the last coordinate line
after flattening. -/
private theorem realEuclideanAppend_add_basis_last
    {p : ℕ} (a : RealEuclidean p) (b t : ℝ) :
    realEuclideanAppend a (fun _ : Fin 1 ↦ b + t) =
      realEuclideanAppend a (fun _ : Fin 1 ↦ b) +
        t • (Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p) := by
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp [realEuclideanAppend_last_one, Pi.basisFun_apply,
      Pi.single_apply]
  · simp [realEuclideanAppend_castAdd, Pi.basisFun_apply,
      Pi.single_apply, fin_castSucc_eq_castAdd_one,
      fin_castAdd_one_ne_last]

/-- The standard multivariable calculus theorem in the exact coordinate
form used by Maxwell: on an open set, existence and continuity of all
coordinate line derivatives imply strict Fréchet differentiability.

The proof is by induction on the dimension.  At the successor step, the
last coordinate is split off and `hasStrictFDerivAt_uncurry_coprod` joins
the two continuous partial derivatives. -/
theorem hasStrictFDerivAt_of_continuous_coordinateLineDerivatives :
    ∀ {p : ℕ} {V : Set (RealEuclidean p)}
      {f : RealEuclidean p → ℝ}
      {d : Fin p → RealEuclidean p → ℝ},
      IsOpen V →
      (∀ x ∈ V, ∀ i : Fin p,
        HasLineDerivAt ℝ f (d i x) x
          ((Pi.basisFun ℝ (Fin p)) i)) →
      (∀ i : Fin p, ContinuousOn (d i) V) →
      ∀ x ∈ V,
        HasStrictFDerivAt f (maxwellCoordinateDifferential d x) x := by
  intro p
  induction p with
  | zero =>
      intro V f d hV hline hcont x hx
      have hf : f = fun _ ↦ f x := by
        funext y
        exact congrArg f (Subsingleton.elim y x)
      have hzero : maxwellCoordinateDifferential d x = 0 := by
        apply ContinuousLinearMap.ext
        intro z
        calc
          maxwellCoordinateDifferential d x z =
              maxwellCoordinateDifferential d x 0 :=
            congrArg (maxwellCoordinateDifferential d x)
              (Subsingleton.elim z 0)
          _ = 0 := map_zero _
      rw [hf]
      rw [hzero]
      simpa using
        (hasStrictFDerivAt_const (x := x) (c := f x))
  | succ p ih =>
      intro V f d hV hline hcont x hx
      let E : (RealEuclidean p × RealEuclidean 1) ≃L[ℝ]
          RealEuclidean (p + 1) :=
        (realEuclideanAppendLinearEquiv p 1).toContinuousLinearEquiv
      let u : RealEuclidean p × RealEuclidean 1 := E.symm x
      let g : RealEuclidean p → RealEuclidean 1 → ℝ :=
        fun a b ↦ f (E (a, b))
      let d₁ : RealEuclidean p → RealEuclidean 1 →
          RealEuclidean p →L[ℝ] ℝ :=
        fun a b ↦ maxwellCoordinateDifferential
          (fun i z ↦ d i.castSucc (E (z, b))) a
      let d₂ : RealEuclidean p → RealEuclidean 1 →
          RealEuclidean 1 →L[ℝ] ℝ :=
        fun a b ↦ d (Fin.last p) (E (a, b)) •
          (realEuclideanOneEquivReal : RealEuclidean 1 →L[ℝ] ℝ)
      have hEu : E u = x := by
        exact E.apply_symm_apply x
      have hpre : E ⁻¹' V ∈ 𝓝 u := by
        exact E.continuous.continuousAt (hV.mem_nhds (hEu.symm ▸ hx))
      have hd₁ : ∀ᶠ v in 𝓝 u,
          HasFDerivAt (g · v.2) (↿d₁ v) v.1 := by
        filter_upwards [hpre] with v hv
        let V₁ : Set (RealEuclidean p) :=
          {a | E (a, v.2) ∈ V}
        have hV₁ : IsOpen V₁ := by
          exact hV.preimage
            (E.continuous.comp (continuous_id.prodMk continuous_const))
        have hv₁ : v.1 ∈ V₁ := hv
        have hline₁ : ∀ a ∈ V₁, ∀ i : Fin p,
            HasLineDerivAt ℝ (g · v.2)
              (d i.castSucc (E (a, v.2))) a
              ((Pi.basisFun ℝ (Fin p)) i) := by
          intro a ha i
          have h := hline (E (a, v.2)) ha i.castSucc
          rw [HasLineDerivAt] at h ⊢
          have hfun :
              (fun t : ℝ ↦
                f (E (a, v.2) +
                  t • (Pi.basisFun ℝ (Fin (p + 1))) i.castSucc)) =
                (fun t : ℝ ↦
                  g (a + t • (Pi.basisFun ℝ (Fin p)) i) v.2) := by
            funext t
            change f (realEuclideanAppend a v.2 +
                t • (Pi.basisFun ℝ (Fin (p + 1))) i.castSucc) =
              f (realEuclideanAppend
                (a + t • (Pi.basisFun ℝ (Fin p)) i) v.2)
            rw [realEuclideanAppend_add_basis_castSucc]
          rwa [hfun] at h
        have hcont₁ : ∀ i : Fin p,
            ContinuousOn (fun a ↦ d i.castSucc (E (a, v.2))) V₁ := by
          intro i a ha
          change ContinuousWithinAt
            (fun z ↦ d i.castSucc (E (z, v.2)))
            ((fun z ↦ E (z, v.2)) ⁻¹' V) a
          exact
            (hcont i.castSucc (E (a, v.2)) ha).comp
              (f := fun z ↦ E (z, v.2))
              ((E.continuous.comp
                (continuous_id.prodMk continuous_const)).continuousWithinAt)
              (fun z hz ↦ hz)
        exact (ih hV₁ hline₁ hcont₁ v.1 hv₁).hasFDerivAt
      have hd₂ : ∀ᶠ v in 𝓝 u,
          HasFDerivAt (g v.1 ·) (↿d₂ v) v.2 := by
        filter_upwards [hpre] with v hv
        have h := hline (E v) hv (Fin.last p)
        rw [HasLineDerivAt] at h
        let q : ℝ → ℝ := fun t ↦
          f (E v + t •
            (Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p))
        have hq : HasDerivAt q (d (Fin.last p) (E v)) 0 := h
        have hq' : HasDerivAt q (d (Fin.last p) (E v))
            (v.2 0 - v.2 0) := by
          simpa using hq
        have hshift :
            HasDerivAt (fun t ↦ q (t - v.2 0))
              (d (Fin.last p) (E v)) (v.2 0) := by
          exact HasDerivAt.comp_sub_const (v.2 0) (v.2 0) hq'
        have hscalar :
            HasDerivAt (fun t : ℝ ↦ g v.1 (fun _ : Fin 1 ↦ t))
              (d (Fin.last p) (E v)) (v.2 0) := by
          convert hshift using 1
          funext t
          change f (realEuclideanAppend v.1
              (fun _ : Fin 1 ↦ t)) =
            f (realEuclideanAppend v.1 v.2 +
              (t - v.2 0) •
                (Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p))
          have hv₂ : v.2 = fun _ : Fin 1 ↦ v.2 0 := by
            funext j
            rw [show j = 0 from Fin.eq_zero j]
          rw [hv₂, ← realEuclideanAppend_add_basis_last]
          congr 2
          ring
        have hvector : HasFDerivAt (g v.1 ·)
            (d (Fin.last p) (E v) •
              (realEuclideanOneEquivReal :
                RealEuclidean 1 →L[ℝ] ℝ)) v.2 := by
          have hcomp := hscalar.hasFDerivAt.comp v.2
            realEuclideanOneEquivReal.hasFDerivAt
          have hfun :
              ((fun t : ℝ ↦ g v.1 (fun _ : Fin 1 ↦ t)) ∘
                  realEuclideanOneEquivReal) = g v.1 := by
            funext z
            change g v.1
                (fun _ : Fin 1 ↦ realEuclideanOneEquivReal z) = g v.1 z
            congr 2
            funext j
            rw [show j = 0 from Fin.eq_zero j]
            simp [realEuclideanOneEquivReal]
          have hmap :
              (ContinuousLinearMap.toSpanSingleton ℝ
                  (d (Fin.last p) (E v))).comp
                  (realEuclideanOneEquivReal :
                    RealEuclidean 1 →L[ℝ] ℝ) =
                d (Fin.last p) (E v) •
                  (realEuclideanOneEquivReal :
                    RealEuclidean 1 →L[ℝ] ℝ) := by
            apply ContinuousLinearMap.ext
            intro z
            simp [realEuclideanOneEquivReal, mul_comm]
          rw [hfun, hmap] at hcomp
          exact hcomp
        exact hvector
      have cd₁ : ContinuousAt ↿d₁ u := by
        change ContinuousAt
          (fun v ↦ ∑ i, d i.castSucc (E v) •
            LinearMap.toContinuousLinearMap
              ((Pi.basisFun ℝ (Fin p)).coord i)) u
        exact tendsto_finsetSum Finset.univ fun i _ ↦ by
          have hcoeff : ContinuousAt (fun v ↦ d i.castSucc (E v)) u :=
            (hcont i.castSucc (E u) (hEu.symm ▸ hx)).continuousAt
              (hV.mem_nhds (hEu.symm ▸ hx)) |>.comp E.continuous.continuousAt
          exact hcoeff.smul continuousAt_const
      have cd₂ : ContinuousAt ↿d₂ u := by
        have hcoeff : ContinuousAt
            (fun v ↦ d (Fin.last p) (E v)) u :=
          (hcont (Fin.last p) (E u) (hEu.symm ▸ hx)).continuousAt
            (hV.mem_nhds (hEu.symm ▸ hx)) |>.comp E.continuous.continuousAt
        exact hcoeff.smul continuousAt_const
      have hg : HasStrictFDerivAt (↿g)
          ((↿d₁ u).coprod (↿d₂ u)) u :=
        hasStrictFDerivAt_uncurry_coprod hd₁ hd₂ cd₁ cd₂
      have hback : HasStrictFDerivAt f
          (((↿d₁ u).coprod (↿d₂ u)).comp
            (E.symm : RealEuclidean (p + 1) →L[ℝ]
              (RealEuclidean p × RealEuclidean 1))) x := by
        have hcomp := hg.comp x E.symm.hasStrictFDerivAt
        change HasStrictFDerivAt
          (fun z ↦ Function.uncurry g (E.symm z)) _ x at hcomp
        have hfun :
            (fun z ↦ Function.uncurry g (E.symm z)) = f := by
          funext z
          change f (E (E.symm z)) = f z
          rw [E.apply_symm_apply]
        rw [hfun] at hcomp
        exact hcomp
      have hderivEq :
          (((↿d₁ u).coprod (↿d₂ u)).comp
              (E.symm : RealEuclidean (p + 1) →L[ℝ]
                (RealEuclidean p × RealEuclidean 1))) =
            maxwellCoordinateDifferential d x := by
        apply ContinuousLinearMap.coe_injective
        apply (Pi.basisFun ℝ (Fin (p + 1))).ext
        intro j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · have hEsymm : E.symm
              ((Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p)) =
              ((0 : RealEuclidean p), (1 : RealEuclidean 1)) := by
            change (realEuclideanAppendLinearEquiv p 1).symm
                ((Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p)) = _
            exact realEuclideanAppendLinearEquiv_symm_basis_last p
          calc
            (((↿d₁ u).coprod (↿d₂ u)).comp
                (E.symm : RealEuclidean (p + 1) →L[ℝ]
                  (RealEuclidean p × RealEuclidean 1)))
                ((Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p)) =
                (↿d₂ u) (1 : RealEuclidean 1) := by
              rw [ContinuousLinearMap.comp_apply]
              change ((↿d₁ u).coprod (↿d₂ u))
                (E.symm
                  ((Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p))) = _
              rw [hEsymm,
                ContinuousLinearMap.coprod_apply, map_zero, zero_add]
            _ = d (Fin.last p) x := by
              dsimp only [d₂, Function.uncurry_apply_pair]
              change (d (Fin.last p) (E (u.1, u.2)) •
                (realEuclideanOneEquivReal :
                  RealEuclidean 1 →L[ℝ] ℝ))
                  (1 : RealEuclidean 1) = d (Fin.last p) x
              have hone : realEuclideanOneEquivReal
                  (1 : RealEuclidean 1) = (1 : ℝ) := by
                rfl
              change d (Fin.last p) (E (u.1, u.2)) *
                realEuclideanOneEquivReal (1 : RealEuclidean 1) =
                  d (Fin.last p) x
              rw [hone, mul_one]
              simpa only [Prod.eta] using
                congrArg (d (Fin.last p)) hEu
            _ = maxwellCoordinateDifferential d x
                ((Pi.basisFun ℝ (Fin (p + 1))) (Fin.last p)) :=
              (maxwellCoordinateDifferential_apply_basis
                d x (Fin.last p)).symm
        · have hEsymm : E.symm
              ((Pi.basisFun ℝ (Fin (p + 1))) i.castSucc) =
              ((Pi.basisFun ℝ (Fin p)) i,
                (0 : RealEuclidean 1)) := by
            change (realEuclideanAppendLinearEquiv p 1).symm
                ((Pi.basisFun ℝ (Fin (p + 1))) i.castSucc) = _
            exact realEuclideanAppendLinearEquiv_symm_basis_castSucc i
          calc
            (((↿d₁ u).coprod (↿d₂ u)).comp
                (E.symm : RealEuclidean (p + 1) →L[ℝ]
                  (RealEuclidean p × RealEuclidean 1)))
                ((Pi.basisFun ℝ (Fin (p + 1))) i.castSucc) =
                (↿d₁ u) ((Pi.basisFun ℝ (Fin p)) i) := by
              rw [ContinuousLinearMap.comp_apply]
              change ((↿d₁ u).coprod (↿d₂ u))
                (E.symm
                  ((Pi.basisFun ℝ (Fin (p + 1))) i.castSucc)) = _
              rw [hEsymm,
                ContinuousLinearMap.coprod_apply, map_zero, add_zero]
            _ = d i.castSucc x := by
              dsimp only [d₁, Function.uncurry_apply_pair]
              change maxwellCoordinateDifferential
                (fun j z ↦ d j.castSucc (E (z, u.2))) u.1
                  ((Pi.basisFun ℝ (Fin p)) i) = d i.castSucc x
              rw [maxwellCoordinateDifferential_apply_basis]
              simpa only [Prod.eta] using
                congrArg (d i.castSucc) hEu
            _ = maxwellCoordinateDifferential d x
                ((Pi.basisFun ℝ (Fin (p + 1))) i.castSucc) :=
              (maxwellCoordinateDifferential_apply_basis
                d x i.castSucc).symm
      rwa [← hderivEq]

/-- Pointwise differentiability is the only conclusion needed by the
first-order assembly. -/
theorem differentiableAt_of_continuous_coordinateLineDerivatives
    {p : ℕ} {V : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ}
    {d : Fin p → RealEuclidean p → ℝ}
    (hV : IsOpen V)
    (hline : ∀ x ∈ V, ∀ i : Fin p,
      HasLineDerivAt ℝ f (d i x) x
        ((Pi.basisFun ℝ (Fin p)) i))
    (hcont : ∀ i : Fin p, ContinuousOn (d i) V)
    {x : RealEuclidean p} (hx : x ∈ V) :
    DifferentiableAt ℝ f x :=
  (hasStrictFDerivAt_of_continuous_coordinateLineDerivatives
    hV hline hcont x hx).differentiableAt

/-! ## A line derivative belongs to the zero-step trace -/

/-- A coordinate line derivative, without any prior total
differentiability assumption, belongs to the zero-step difference-quotient
trace of the corresponding scalar graph. -/
theorem maxwellDifferenceQuotientZeroTrace_functionGraph_lineDeriv_mem
    {p : ℕ} {U : Set (RealEuclidean p)} (hU : IsOpen U)
    {x : RealEuclidean p} (hx : x ∈ U)
    (f : RealEuclidean p → ℝ) (i : Fin p) {d : ℝ}
    (hline : HasLineDerivAt ℝ f d x
      ((Pi.basisFun ℝ (Fin p)) i)) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ d) ∈
      maxwellDifferenceQuotientZeroTrace U
        (maxwellFunctionGraph U (fun u _ ↦ f u)) i := by
  let v : RealEuclidean p := Pi.single i 1
  let quotientPoint : ℝ → RealEuclidean ((p + 1) + 1) := fun epsilon ↦
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
      (fun _ : Fin 1 ↦
        epsilon⁻¹ • (f (x + epsilon • v) - f x))
  have hline' : HasLineDerivAt ℝ f d x v := by
    simpa only [v, pi_basisFun_eq_single] using hline
  have hepsilonZero :
      Tendsto (fun epsilon : ℝ ↦ epsilon) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hquotient :
      Tendsto
        (fun epsilon : ℝ ↦
          epsilon⁻¹ • (f (x + epsilon • v) - f x))
        (𝓝[≠] 0) (𝓝 d) :=
    hline'.tendsto_slope_zero
  have hpath :
      Tendsto quotientPoint (𝓝[≠] 0)
        (𝓝 (realEuclideanAppend
          (realEuclideanAppend x (0 : RealEuclidean 1))
          (fun _ : Fin 1 ↦ d))) := by
    apply tendsto_pi_nhds.2
    intro j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k
      · simpa [quotientPoint, realEuclideanAppend] using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ ↦ x l) (𝓝[≠] 0) (𝓝 (x l)))
      · simpa [quotientPoint, realEuclideanAppend] using hepsilonZero
    · simpa [quotientPoint, realEuclideanAppend] using hquotient
  have hshift :
      Tendsto (fun epsilon : ℝ ↦ x + epsilon • v)
        (𝓝[≠] 0) (𝓝 x) := by
    simpa using
      (tendsto_const_nhds.add
        (hepsilonZero.smul
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ ↦ v) (𝓝[≠] 0) (𝓝 v))))
  have hshiftU : ∀ᶠ epsilon : ℝ in 𝓝[≠] 0,
      x + epsilon • v ∈ U :=
    hshift.eventually (hU.mem_nhds hx)
  have hne : ∀ᶠ epsilon : ℝ in 𝓝[≠] 0, epsilon ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with epsilon hepsilon
    simpa using hepsilon
  have hmem : ∀ᶠ epsilon : ℝ in 𝓝[≠] 0,
      quotientPoint epsilon ∈
        maxwellDifferenceQuotientRelation U
          (maxwellFunctionGraph U (fun u _ ↦ f u)) i := by
    filter_upwards [hshiftU, hne] with epsilon hepsilonU hepsilon
    rw [show quotientPoint epsilon =
        realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦
            epsilon⁻¹ • (f (x + epsilon • v) - f x)) by rfl]
    rw [realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_functionGraph_iff]
    refine ⟨hx, ?_, hepsilon, ?_⟩
    · simpa [v] using hepsilonU
    · simp only [v]
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hepsilon, one_mul]
  apply
    (realEuclideanAppend_scalar_mem_maxwellDifferenceQuotientZeroTrace_iff
      U (maxwellFunctionGraph U (fun u _ ↦ f u)) i x d).mpr
  exact mem_closure_of_tendsto hpath hmem

/-- The preceding containment for the canonical representative of a
pseudofunction. -/
theorem IsMaxwellPseudofunctionOn.chosenScalar_coordinateLineDeriv_mem_trace
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (i : Fin p) {x : RealEuclidean p} (hx : x ∈ U) {d : ℝ}
    (hline : HasLineDerivAt ℝ (maxwellChosenScalarValue R) d x
      ((Pi.basisFun ℝ (Fin p)) i)) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ d) ∈
      maxwellDifferenceQuotientZeroTrace U R i := by
  have hgraph :=
    maxwellDifferenceQuotientZeroTrace_functionGraph_lineDeriv_mem
      hU hx (maxwellChosenScalarValue R) i hline
  exact maxwellDifferenceQuotientZeroTrace_mono
    hR.chosenScalarGraph_subset i hgraph

/-! ## Closed traces force continuity of the coordinate derivatives -/

theorem maxwellPositiveReciprocalRelation_mono
    {p : ℕ} {G H : MaxwellRelation p 1} (hGH : G ⊆ H) :
    maxwellPositiveReciprocalRelation G ⊆
      maxwellPositiveReciprocalRelation H := by
  intro w hw
  simp only [maxwellPositiveReciprocalRelation, Set.mem_setOf_eq] at hw ⊢
  rcases hw with ⟨y, hy, hyr, hr⟩
  exact ⟨y, hGH hy, hyr, hr⟩

theorem maxwellNegativeReciprocalRelation_mono
    {p : ℕ} {G H : MaxwellRelation p 1} (hGH : G ⊆ H) :
    maxwellNegativeReciprocalRelation G ⊆
      maxwellNegativeReciprocalRelation H := by
  intro w hw
  simp only [maxwellNegativeReciprocalRelation, Set.mem_setOf_eq] at hw ⊢
  rcases hw with ⟨y, hy, hyr, hr⟩
  exact ⟨y, hGH hy, hyr, hr⟩

theorem maxwellPositiveInfinityBase_mono
    {p : ℕ} {G H : MaxwellRelation p 1} (hGH : G ⊆ H) :
    maxwellPositiveInfinityBase G ⊆ maxwellPositiveInfinityBase H := by
  intro x hx
  exact closure_mono (maxwellPositiveReciprocalRelation_mono hGH) hx

theorem maxwellNegativeInfinityBase_mono
    {p : ℕ} {G H : MaxwellRelation p 1} (hGH : G ⊆ H) :
    maxwellNegativeInfinityBase G ⊆ maxwellNegativeInfinityBase H := by
  intro x hx
  exact closure_mono (maxwellNegativeReciprocalRelation_mono hGH) hx

/-- The derivative value chosen canonically from a line-differentiable
coordinate. -/
def maxwellChosenCoordinateLineDerivative {p : ℕ}
    (R : MaxwellRelation p 1) (i : Fin p)
    (x : RealEuclidean p) : ℝ :=
  lineDeriv ℝ (maxwellChosenScalarValue R) x
    ((Pi.basisFun ℝ (Fin p)) i)

/-- Exact first half of Lemma 2.3.10 left after the elementary compactness
and closed-graph arguments: every coordinate line derivative exists on the
good open set. -/
def MaxwellChosenCoordinateLineDifferentiability {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) : Prop :=
  ∀ x ∈ U \ maxwellFirstOrderExceptionalLocus U R,
    ∀ i : Fin p,
      LineDifferentiableAt ℝ (maxwellChosenScalarValue R) x
        ((Pi.basisFun ℝ (Fin p)) i)

/-- Once the coordinate line derivatives exist, their continuity is forced
by the closed zero-step trace.  A discontinuity would give either two finite
closed-graph values or a signed infinite value.  Monotonicity into the
closed trace puts the base point in the raw coordinate bad locus in all
three cases. -/
theorem maxwellChosenCoordinateLineDerivative_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (hline : MaxwellChosenCoordinateLineDifferentiability U R)
    (i : Fin p) :
    ContinuousOn (maxwellChosenCoordinateLineDerivative R i)
      (U \ maxwellFirstOrderExceptionalLocus U R) := by
  let V : Set (RealEuclidean p) :=
    U \ maxwellFirstOrderExceptionalLocus U R
  let d : RealEuclidean p → ℝ :=
    maxwellChosenCoordinateLineDerivative R i
  let D : RealEuclidean p → RealEuclidean 1 :=
    fun x _ ↦ d x
  let G : MaxwellRelation p 1 :=
    maxwellDifferenceQuotientZeroTrace U R i
  have hgraph : maxwellFunctionGraph V D ⊆ G := by
    rintro _ ⟨x, hx, rfl⟩
    change realEuclideanAppend x (fun _ : Fin 1 ↦ d x) ∈ G
    exact hR.chosenScalar_coordinateLineDeriv_mem_trace hU i hx.1
      ((hline x hx i).hasLineDerivAt)
  have hclosure : closure (maxwellFunctionGraph V D) ⊆ G := by
    exact isClosed_maxwellDifferenceQuotientZeroTrace U R i |>.closure_subset_iff.mpr
      hgraph
  intro x hx
  have hnotRaw : x ∉ maxwellCoordinateRawBadLocus U R i := by
    intro hraw
    exact hx.2
      (maxwellCoordinateExceptionalLocus_subset_firstOrder U R i
        (subset_closure hraw))
  have hDcontinuous : ContinuousWithinAt D V x := by
    by_contra hbad
    rcases maxwellScalarClosureSequenceDichotomy_mathlib V D x hx hbad with
      hfinite | hpositive | hnegative
    ·
      rcases hfinite with ⟨y₁, y₂, hy₁, hy₂, hne⟩
      have hGmulti : x ∈ maxwellMultivaluedLocus G :=
        ⟨y₁, y₂, hclosure hy₁, hclosure hy₂, hne⟩
      apply hnotRaw
      unfold maxwellCoordinateRawBadLocus
      aesop
    ·
      have hGpositive : x ∈ maxwellPositiveInfinityBase G :=
        maxwellPositiveInfinityBase_mono hgraph hpositive
      apply hnotRaw
      unfold maxwellCoordinateRawBadLocus
      aesop
    ·
      have hGnegative : x ∈ maxwellNegativeInfinityBase G :=
        maxwellNegativeInfinityBase_mono hgraph hnegative
      apply hnotRaw
      unfold maxwellCoordinateRawBadLocus
      aesop
  have hscalar : ContinuousWithinAt d V x := by
    have h := (continuous_apply (0 : Fin 1)).continuousAt.comp_continuousWithinAt
      hDcontinuous
    simpa [D, d, Function.comp_def] using h
  simpa [V, d] using hscalar

/-- Lemma 2.3.10 from the pointwise coordinate-line existence assertion.
The continuity of all partials and the passage to the Fréchet derivative
are theorems above. -/
theorem maxwellChosenScalarValue_differentiableAt_of_coordinateLineDifferentiability
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : IsOpen U) (hR : IsMaxwellPseudofunctionOn U R)
    (hline : MaxwellChosenCoordinateLineDifferentiability U R)
    {x : RealEuclidean p}
    (hx : x ∈ U \ maxwellFirstOrderExceptionalLocus U R) :
    DifferentiableAt ℝ (maxwellChosenScalarValue R) x := by
  let V : Set (RealEuclidean p) :=
    U \ maxwellFirstOrderExceptionalLocus U R
  have hV : IsOpen V :=
    hU.sdiff (isClosed_maxwellFirstOrderExceptionalLocus U R)
  apply differentiableAt_of_continuous_coordinateLineDerivatives
    (V := V) (d := fun i ↦ maxwellChosenCoordinateLineDerivative R i)
    hV
  · intro y hy i
    exact (hline y hy i).hasLineDerivAt
  · intro i
    exact maxwellChosenCoordinateLineDerivative_continuousOn
      hU hR hline i
  · exact hx

/-! ## Family-wide source adapter -/

/-- The source mechanisms with the old Fréchet-differentiability field
replaced by the strictly weaker pointwise assertion that the coordinate
line derivatives exist. -/
structure MaxwellScalarFirstOrderSourceMechanismsWithLineDerivatives
    (C : EuclideanSetFamily) : Prop where
  coordinate_mechanisms : ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∀ i : Fin p, MaxwellCoordinateFirstOrderAnalyticMechanisms U R i
  chosen_coordinateLineDifferentiable : ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      MaxwellChosenCoordinateLineDifferentiability U R

/-- Convert the source-faithful coordinate-line package to the adapter's
previous source mechanisms. -/
theorem MaxwellScalarFirstOrderSourceMechanismsWithLineDerivatives.toSourceMechanisms
    {C : EuclideanSetFamily}
    (h : MaxwellScalarFirstOrderSourceMechanismsWithLineDerivatives C) :
    MaxwellScalarFirstOrderSourceMechanisms C := by
  constructor
  · exact h.coordinate_mechanisms
  · intro p hp U R hU hUmem hRmem hR x hx
    exact
      maxwellChosenScalarValue_differentiableAt_of_coordinateLineDifferentiability
        hU hR
          (h.chosen_coordinateLineDifferentiable hp U R hU hUmem hRmem hR)
        hx

/-- The exact analytic core follows with no residual total-differentiability
assumption. -/
theorem maxwellScalarFirstOrderAnalyticCore_of_sourceMechanismsWithLineDerivatives
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarFirstOrderSourceMechanismsWithLineDerivatives
      (charbonnelClosure S)) :
    MaxwellScalarFirstOrderAnalyticCore (charbonnelClosure S) :=
  maxwellScalarFirstOrderAnalyticCore_of_sourceMechanisms
    hC hmem h21 h22 hsource.toSourceMechanisms

end AbelFormalization
