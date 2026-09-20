import AbelFormalization.StirlingParameterHom
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# The bounded terminal block derivations

This continuation of `StirlingParameterHom` records the exact finite-block vector fields,
identifies the first two logarithmic parameter coefficients with `-V₁` and
`V₂ / 2`, and isolates the commutator induction which produces every `V_q`.

Ideal preservation is introduced only through
`terminalBlockVectorFields_preserve_of_global_components`.  Its hypotheses
separate the two facts which the eventual application must prove:

* the actual global parameter homomorphism preserves the global ideal;
* that ideal is closed under its actual global multigraded components.

In particular, no invariance under the one-block homomorphism
`stirlingParameterHom` is assumed.
-/

noncomputable section

namespace AbelFormalization

section Extensionality

variable {Q R ι : Type*} [CommRing Q] [CommRing R] [Algebra Q R]

/-- Two derivations over a smaller scalar ring agree on a multivariate
polynomial ring once they agree on coefficients and variables.  The standard
`MvPolynomial.derivation_ext` cannot be used directly here: it applies to
derivations over the coefficient ring, whereas the terminal derivations are
over `ℚ`. -/
theorem mvPolynomial_derivation_ext_C_X
    {D E : Derivation Q (MvPolynomial ι R) (MvPolynomial ι R)}
    (hC : ∀ a : R, D (MvPolynomial.C a) = E (MvPolynomial.C a))
    (hX : ∀ i : ι, D (MvPolynomial.X i) = E (MvPolynomial.X i)) :
    D = E := by
  apply Derivation.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C a => exact hC a
  | add P S hP hS => simp only [map_add, hP, hS]
  | mul_X P i hP =>
      simp only [Derivation.leibniz, smul_eq_mul, hP, hX]

end Extensionality

section VectorFields

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- The manuscript's bounded block vector field, characterized here by

`V_q(v_r) = choose(r+1,q+1) v_{r-q}` for `q ≤ r`,

with a `Fin d` variable indexed by `r` representing derivative order `r+1`.
The definition is first made as an `R`-derivation (so it really fixes every
coefficient) and then restricted to `ℚ`. -/
def terminalBlockVectorField (q : ℕ) :
    Derivation ℚ (MvPolynomial (Keep ⊕ Fin d) R)
      (MvPolynomial (Keep ⊕ Fin d) R) :=
  (MvPolynomial.mkDerivation R fun z =>
    match z with
    | Sum.inl _ => 0
    | Sum.inr r =>
        if q ≤ r.val then
          ((r.val + 1).choose (q + 1) : MvPolynomial (Keep ⊕ Fin d) R) *
            MvPolynomial.X (Sum.inr
              (⟨r.val - q, (Nat.sub_le r.val q).trans_lt r.isLt⟩ : Fin d))
        else 0).restrictScalars ℚ

@[simp]
theorem terminalBlockVectorField_C (q : ℕ) (a : R) :
    terminalBlockVectorField R Keep d q (MvPolynomial.C a) = 0 := by
  simp [terminalBlockVectorField]

@[simp]
theorem terminalBlockVectorField_X_keep (q : ℕ) (k : Keep) :
    terminalBlockVectorField R Keep d q (MvPolynomial.X (Sum.inl k)) = 0 := by
  simp [terminalBlockVectorField]

/-- Exact action on a block generator, including the boundary where no
variable with nonpositive derivative order is introduced. -/
theorem terminalBlockVectorField_X_block (q : ℕ) (r : Fin d) :
    terminalBlockVectorField R Keep d q (MvPolynomial.X (Sum.inr r)) =
      if q ≤ r.val then
        ((r.val + 1).choose (q + 1) : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr
            (⟨r.val - q, (Nat.sub_le r.val q).trans_lt r.isLt⟩ : Fin d))
      else 0 := by
  simp [terminalBlockVectorField]

/-- Every positive lowering field annihilates the first-derivative variable.
This is the denominator check needed before extending the fields across the
eventual localization. -/
theorem terminalBlockVectorField_X_first
    (q : ℕ) (hq : 1 ≤ q) (r : Fin d) (hr : r.val = 0) :
    terminalBlockVectorField R Keep d q (MvPolynomial.X (Sum.inr r)) = 0 := by
  rw [terminalBlockVectorField_X_block, ite_eq_right (by omega)]

/-- On the diagonal `r=q`, the coefficient is one and the output is the
first-derivative variable.  This is the unit triangular entry used in the
later descending partial-derivative extraction. -/
theorem terminalBlockVectorField_X_block_diagonal
    (q : ℕ) (r : Fin d) (hr : r.val = q) :
    terminalBlockVectorField R Keep d q (MvPolynomial.X (Sum.inr r)) =
      MvPolynomial.X (Sum.inr (⟨0, by omega⟩ : Fin d)) := by
  rw [terminalBlockVectorField_X_block, ite_eq_left (by omega)]
  simp [hr]

/-- There are only `d-1` potentially nonzero positive lowering fields in a
block of size `d`. -/
theorem terminalBlockVectorField_eq_zero_of_blockSize_le
    (q : ℕ) (hdq : d ≤ q) :
    terminalBlockVectorField R Keep d q = 0 := by
  apply mvPolynomial_derivation_ext_C_X
  · intro a
    simp
  · rintro (k | r)
    · simp
    · rw [terminalBlockVectorField_X_block]
      simp only [Derivation.zero_apply]
      rw [ite_eq_right (by omega)]

end VectorFields

section LogarithmicActions

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- The unreduced signed-Stirling form of the first logarithmic component.
It is useful when the first component is iterated in the proof for `L₂`. -/
theorem stirlingParameterFirstDerivation_X_block_signed (r : Fin d) :
    stirlingParameterFirstDerivation R Keep d (MvPolynomial.X (Sum.inr r)) =
      if hr : 1 ≤ r.val then
        (signedStirling (r.val + 1) r.val : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr (⟨r.val - 1, by omega⟩ : Fin d))
      else 0 := by
  simp only [stirlingParameterFirstDerivation,
    polynomialParameterFirstDerivation_apply, stirlingParameterHom_X_block]
  rw [stirlingParameterVariable_coeff]
  split_ifs with hr
  · rw [Nat.sub_add_cancel hr]
  · rfl

@[simp]
theorem stirlingParameterSecondLogDerivation_C (a : R) :
    stirlingParameterSecondLogDerivation R Keep d (MvPolynomial.C a) = 0 := by
  change polynomialParameterSecondLogDerivation
      (stirlingParameterHom R Keep d)
      (stirlingParameterHom_coeff_zero R Keep d) (MvPolynomial.C a) = 0
  rw [polynomialParameterSecondLogDerivation_apply_coeff,
    stirlingParameterHom_C,
    Polynomial.coeff_C_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0),
    Polynomial.coeff_C_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0), map_zero]
  simp only [Polynomial.coeff_zero, mul_zero, sub_zero]

@[simp]
theorem stirlingParameterSecondLogDerivation_X_keep (k : Keep) :
    stirlingParameterSecondLogDerivation R Keep d
      (MvPolynomial.X (Sum.inl k)) = 0 := by
  change polynomialParameterSecondLogDerivation
      (stirlingParameterHom R Keep d)
      (stirlingParameterHom_coeff_zero R Keep d)
      (MvPolynomial.X (Sum.inl k)) = 0
  rw [polynomialParameterSecondLogDerivation_apply_coeff,
    stirlingParameterHom_X_keep,
    Polynomial.coeff_C_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0),
    Polynomial.coeff_C_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0), map_zero]
  simp only [Polynomial.coeff_zero, mul_zero, sub_zero]

/-- The second logarithmic coefficient has exactly half the `V₂`
coefficient on every block variable.  The inactive cases `r=0,1` are dealt
with separately, so no out-of-range `Fin d` index is ever formed. -/
theorem stirlingParameterSecondLogDerivation_X_block (r : Fin d) :
    stirlingParameterSecondLogDerivation R Keep d
        (MvPolynomial.X (Sum.inr r)) =
      if hr : 2 ≤ r.val then
        algebraMap ℚ (MvPolynomial (Keep ⊕ Fin d) R) (1 / 2) *
          ((r.val + 1).choose 3 : MvPolynomial (Keep ⊕ Fin d) R) *
          MvPolynomial.X (Sum.inr (⟨r.val - 2, by omega⟩ : Fin d))
      else 0 := by
  classical
  let A := MvPolynomial (Keep ⊕ Fin d) R
  let D₁ := stirlingParameterFirstDerivation R Keep d
  change (stirlingParameterHom R Keep d
      (MvPolynomial.X (Sum.inr r))).coeff 2 -
      (1 / 2 : ℚ) • D₁ (D₁ (MvPolynomial.X (Sum.inr r))) = _
  rw [stirlingParameterHom_X_block,
    stirlingParameterVariable_coeff_two]
  by_cases hr : 2 ≤ r.val
  · rw [dite_eq_left hr]
    have hsub : r.val - 2 + 1 = r.val - 1 := by omega
    rw [hsub]
    let r₁ : Fin d := ⟨r.val - 1, by omega⟩
    let r₂ : Fin d := ⟨r.val - 2, by omega⟩
    have hrpos : 1 ≤ r.val := by omega
    have hr₁ : 1 ≤ r₁.val := by
      dsimp [r₁]
      omega
    have hr₁_succ : r₁.val + 1 = r.val := by
      dsimp [r₁]
      omega
    have hr₁_pred : r₁.val - 1 = r.val - 2 := by
      dsimp [r₁]
      omega
    have hD₁r :
        D₁ (MvPolynomial.X (Sum.inr r)) =
          (signedStirling (r.val + 1) r.val : A) *
            MvPolynomial.X (Sum.inr r₁) := by
      simpa [D₁, r₁, hrpos] using
        stirlingParameterFirstDerivation_X_block_signed R Keep d r
    have hD₁r₁ :
        D₁ (MvPolynomial.X (Sum.inr r₁)) =
          (signedStirling r.val (r.val - 1) : A) *
            MvPolynomial.X (Sum.inr r₂) := by
      simpa [D₁, r₁, r₂, hr₁, hr₁_succ, hr₁_pred] using
        stirlingParameterFirstDerivation_X_block_signed R Keep d r₁
    have hiterate :
        D₁ (D₁ (MvPolynomial.X (Sum.inr r))) =
          (signedStirling (r.val + 1) r.val : A) *
            (signedStirling r.val (r.val - 1) : A) *
            MvPolynomial.X (Sum.inr r₂) := by
      rw [hD₁r, Derivation.leibniz, hD₁r₁]
      simp only [smul_eq_mul, Derivation.map_intCast, mul_zero, add_zero]
      ring
    rw [hiterate]
    simp only [Algebra.smul_def]
    have hcoefficient :=
      signedStirling_log_second_subdiagonal_qAlgebra A (r.val - 1)
    have hcoefficient' :
        (signedStirling (r.val + 1) (r.val - 1) : A) -
            algebraMap ℚ A (1 / 2) *
              (signedStirling (r.val + 1) r.val : A) *
              (signedStirling r.val (r.val - 1) : A) =
          algebraMap ℚ A (1 / 2) * ((r.val + 1).choose 3 : A) := by
      simpa only [show r.val - 1 + 2 = r.val + 1 by omega,
        show r.val - 1 + 1 = r.val by omega] using hcoefficient
    change
      (signedStirling (r.val + 1) (r.val - 1) : A) *
          MvPolynomial.X (Sum.inr r₂) -
        algebraMap ℚ A (1 / 2) *
          ((signedStirling (r.val + 1) r.val : A) *
            (signedStirling r.val (r.val - 1) : A) *
            MvPolynomial.X (Sum.inr r₂)) = _
    calc
      _ = ((signedStirling (r.val + 1) (r.val - 1) : A) -
            algebraMap ℚ A (1 / 2) *
              (signedStirling (r.val + 1) r.val : A) *
              (signedStirling r.val (r.val - 1) : A)) *
            MvPolynomial.X (Sum.inr r₂) := by ring
      _ = (algebraMap ℚ A (1 / 2) * ((r.val + 1).choose 3 : A)) *
            MvPolynomial.X (Sum.inr r₂) := by rw [hcoefficient']
      _ = _ := by
        rw [dite_eq_left hr]
  · rw [dite_eq_right hr]
    by_cases hr₁ : 1 ≤ r.val
    · have hrval : r.val = 1 := by omega
      rw [stirlingParameterFirstDerivation_X_block_signed,
        dite_eq_left hr₁, Derivation.leibniz]
      simp only [smul_eq_mul, Derivation.map_intCast, mul_zero, add_zero]
      rw [stirlingParameterFirstDerivation_X_block_signed]
      simp [hrval]
    · rw [stirlingParameterFirstDerivation_X_block_signed,
        dite_eq_right hr₁]
      simp only [map_zero, smul_zero, sub_zero]
      rw [dite_eq_right hr]

/-- The first logarithmic derivation is `-V₁` on the whole polynomial
ring, not merely on the displayed generators. -/
theorem stirlingParameterFirstDerivation_eq_neg_vectorField :
    stirlingParameterFirstDerivation R Keep d =
      -terminalBlockVectorField R Keep d 1 := by
  apply mvPolynomial_derivation_ext_C_X
  · intro a
    simp
  · rintro (k | r)
    · simp
    · simp only [Derivation.neg_apply]
      rw [stirlingParameterFirstDerivation_X_block,
        terminalBlockVectorField_X_block]
      by_cases hr : 1 ≤ r.val
      · rw [dite_eq_left hr, ite_eq_left hr]
        ring
      · rw [dite_eq_right hr, ite_eq_right hr]
        ring

/-- The second logarithmic derivation is `V₂ / 2` on the whole polynomial
ring.  The scalar is a genuine `ℚ`-scalar, so this remains valid for every
commutative `ℚ`-algebra, including rings with zero divisors. -/
theorem stirlingParameterSecondLogDerivation_eq_half_vectorField :
    stirlingParameterSecondLogDerivation R Keep d =
      (1 / 2 : ℚ) • terminalBlockVectorField R Keep d 2 := by
  apply mvPolynomial_derivation_ext_C_X
  · intro a
    simp
  · rintro (k | r)
    · simp
    · simp only [Derivation.smul_apply, Algebra.smul_def]
      rw [stirlingParameterSecondLogDerivation_X_block,
        terminalBlockVectorField_X_block]
      by_cases hr : 2 ≤ r.val
      · rw [dite_eq_left hr, ite_eq_left hr]
        ring
      · rw [dite_eq_right hr, ite_eq_right hr]
        ring

end LogarithmicActions

section Commutators

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- Generator-level form of the commutator calculation.  Its coefficient is
the transported rational identity in `TerminalCoefficientIdentities`; the
two inactive branches are retained explicitly to cover every boundary. -/
theorem terminalBlockVectorField_commutator_one_X_block
    (q : ℕ) (r : Fin d) :
    ⁅terminalBlockVectorField R Keep d 1,
        terminalBlockVectorField R Keep d q⁆
        (MvPolynomial.X (Sum.inr r)) =
      (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)) •
        terminalBlockVectorField R Keep d (q + 1)
          (MvPolynomial.X (Sum.inr r)) := by
  classical
  let A := MvPolynomial (Keep ⊕ Fin d) R
  rw [Derivation.commutator_apply]
  by_cases hactive : q + 1 ≤ r.val
  · have hq : q ≤ r.val := by omega
    have h₁ : 1 ≤ r.val := by omega
    let rq : Fin d := ⟨r.val - q, by omega⟩
    let r₁ : Fin d := ⟨r.val - 1, by omega⟩
    let rout : Fin d := ⟨r.val - (q + 1), by omega⟩
    have hrq₁ : 1 ≤ rq.val := by
      dsimp [rq]
      omega
    have hr₁q : q ≤ r₁.val := by
      dsimp [r₁]
      omega
    have hrq_succ : rq.val + 1 = r.val + 1 - q := by
      dsimp [rq]
      omega
    have hr₁_succ : r₁.val + 1 = r.val := by
      dsimp [r₁]
      omega
    have hrq_index :
        (⟨rq.val - 1, by omega⟩ : Fin d) = rout := by
      apply Fin.ext
      dsimp [rq, rout]
      omega
    have hr₁_index :
        (⟨r₁.val - q, by omega⟩ : Fin d) = rout := by
      apply Fin.ext
      dsimp [r₁, rout]
      omega
    have hleft :
        terminalBlockVectorField R Keep d 1
            (terminalBlockVectorField R Keep d q
              (MvPolynomial.X (Sum.inr r))) =
          ((r.val + 1).choose (q + 1) : A) *
            ((r.val + 1 - q).choose 2 : A) *
            MvPolynomial.X (Sum.inr rout) := by
      rw [terminalBlockVectorField_X_block, ite_eq_left hq,
        Derivation.leibniz]
      simp only [smul_eq_mul, Derivation.map_natCast, mul_zero, add_zero]
      rw [terminalBlockVectorField_X_block, ite_eq_left hrq₁]
      rw [hrq_succ, hrq_index]
      norm_num
      simp only [mul_assoc]
    have hright :
        terminalBlockVectorField R Keep d q
            (terminalBlockVectorField R Keep d 1
              (MvPolynomial.X (Sum.inr r))) =
          ((r.val + 1).choose 2 : A) *
            (r.val.choose (q + 1) : A) *
            MvPolynomial.X (Sum.inr rout) := by
      rw [terminalBlockVectorField_X_block, ite_eq_left h₁,
        Derivation.leibniz]
      simp only [smul_eq_mul, Derivation.map_natCast, mul_zero, add_zero]
      rw [terminalBlockVectorField_X_block, ite_eq_left hr₁q]
      rw [hr₁_succ, hr₁_index]
      norm_num
      simp only [mul_assoc]
    rw [hleft, hright, terminalBlockVectorField_X_block,
      ite_eq_left hactive]
    simp only [Algebra.smul_def]
    have hcoefficient := terminal_binomial_bracket_qAlgebra A (r.val + 1) q
    have hpred : r.val + 1 - 1 = r.val := by omega
    rw [hpred] at hcoefficient
    calc
      ((r.val + 1).choose (q + 1) : A) *
            ((r.val + 1 - q).choose 2 : A) *
            MvPolynomial.X (Sum.inr rout) -
          ((r.val + 1).choose 2 : A) *
            (r.val.choose (q + 1) : A) *
            MvPolynomial.X (Sum.inr rout) =
        (((r.val + 1).choose (q + 1) : A) *
            ((r.val + 1 - q).choose 2 : A) -
          ((r.val + 1).choose 2 : A) *
            (r.val.choose (q + 1) : A)) *
            MvPolynomial.X (Sum.inr rout) := by ring
      _ = (algebraMap ℚ A
              (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)) *
            ((r.val + 1).choose (q + 2) : A)) *
            MvPolynomial.X (Sum.inr rout) := by rw [hcoefficient]
      _ = _ := by
        have hq_succ : q + 1 + 1 = q + 2 := by omega
        rw [hq_succ]
        change
          (algebraMap ℚ A
              (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)) *
            ((r.val + 1).choose (q + 2) : A)) *
              MvPolynomial.X (Sum.inr rout) =
            algebraMap ℚ A
                (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)) *
              (((r.val + 1).choose (q + 2) : A) *
                MvPolynomial.X (Sum.inr rout))
        rw [mul_assoc]
  · have hout : ¬ q + 1 ≤ r.val := hactive
    have hleft :
        terminalBlockVectorField R Keep d 1
            (terminalBlockVectorField R Keep d q
              (MvPolynomial.X (Sum.inr r))) = 0 := by
      by_cases hq : q ≤ r.val
      · have hrq : r.val = q := by omega
        rw [terminalBlockVectorField_X_block, ite_eq_left hq,
          Derivation.leibniz]
        simp [terminalBlockVectorField_X_block, hrq]
      · rw [terminalBlockVectorField_X_block, ite_eq_right hq]
        simp
    have hright :
        terminalBlockVectorField R Keep d q
            (terminalBlockVectorField R Keep d 1
              (MvPolynomial.X (Sum.inr r))) = 0 := by
      by_cases h₁ : 1 ≤ r.val
      · have hnq : ¬ q ≤ r.val - 1 := by omega
        rw [terminalBlockVectorField_X_block, ite_eq_left h₁,
          Derivation.leibniz]
        simp [terminalBlockVectorField_X_block, hnq]
      · rw [terminalBlockVectorField_X_block, ite_eq_right h₁]
        simp
    rw [hleft, hright, terminalBlockVectorField_X_block, ite_eq_right hout]
    simp

/-- The exact finite-block Lie relation.  For `q=1` the scalar vanishes,
and for `q ≥ d` both sides vanish by boundedness. -/
theorem terminalBlockVectorField_commutator_one (q : ℕ) :
    ⁅terminalBlockVectorField R Keep d 1,
        terminalBlockVectorField R Keep d q⁆ =
      (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)) •
        terminalBlockVectorField R Keep d (q + 1) := by
  apply mvPolynomial_derivation_ext_C_X
  · intro a
    simp [Derivation.commutator_apply]
  · rintro (k | r)
    · simp [Derivation.commutator_apply]
    · exact terminalBlockVectorField_commutator_one_X_block R Keep d q r

/-- The first nontrivial bracket is `[V₁,V₂] = -2 V₃`. -/
theorem terminalBlockVectorField_commutator_one_two :
    ⁅terminalBlockVectorField R Keep d 1,
        terminalBlockVectorField R Keep d 2⁆ =
      (-2 : ℚ) • terminalBlockVectorField R Keep d 3 := by
  have h := terminalBlockVectorField_commutator_one R Keep d 2
  norm_num at h ⊢
  exact h

/-- The commutator coefficient is a nonzero rational number from `q=2`
onward. -/
theorem terminalCommutatorScalar_ne_zero (q : ℕ) (hq : 2 ≤ q) :
    -(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2) ≠ 0 := by
  apply neg_ne_zero.mpr
  apply div_ne_zero
  · apply mul_ne_zero
    · apply sub_ne_zero.mpr
      exact_mod_cast (show q ≠ 1 by omega)
    · exact_mod_cast (show q + 2 ≠ 0 by omega)
  · norm_num

/-- Solving the bracket relation for its next field.  The inverse is taken in
the scalar field `ℚ`, so no regularity or domain hypothesis on `R` is used. -/
theorem terminalBlockVectorField_succ_eq_inv_smul_commutator
    (q : ℕ) (hq : 2 ≤ q) :
    terminalBlockVectorField R Keep d (q + 1) =
      (-(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2))⁻¹ •
        ⁅terminalBlockVectorField R Keep d 1,
          terminalBlockVectorField R Keep d q⁆ := by
  let c : ℚ := -(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)
  have hc : c ≠ 0 := by
    change -(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2) ≠ 0
    exact terminalCommutatorScalar_ne_zero q hq
  rw [terminalBlockVectorField_commutator_one R Keep d q]
  exact (inv_smul_smul₀ hc
    (terminalBlockVectorField R Keep d (q + 1))).symm

end Commutators

section Ideals

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The exact preservation predicate used below. -/
def derivationPreservesIdeal (I : Ideal A) (D : Derivation ℚ A A) : Prop :=
  ∀ a ∈ I, D a ∈ I

theorem derivationPreservesIdeal.neg {I : Ideal A} {D : Derivation ℚ A A}
    (hD : derivationPreservesIdeal I D) :
    derivationPreservesIdeal I (-D) := by
  intro a ha
  simpa only [Derivation.neg_apply] using I.neg_mem (hD a ha)

theorem derivationPreservesIdeal.smul {I : Ideal A} {D : Derivation ℚ A A}
    (hD : derivationPreservesIdeal I D) (c : ℚ) :
    derivationPreservesIdeal I (c • D) := by
  intro a ha
  rw [Derivation.smul_apply, Algebra.smul_def]
  exact I.mul_mem_left _ (hD a ha)

theorem derivationPreservesIdeal.of_smul {I : Ideal A}
    {D : Derivation ℚ A A} {c : ℚ}
    (hD : derivationPreservesIdeal I (c • D)) (hc : c ≠ 0) :
    derivationPreservesIdeal I D := by
  intro a ha
  have hm := I.mul_mem_left (algebraMap ℚ A c⁻¹) (hD a ha)
  simpa only [Derivation.smul_apply, Algebra.smul_def, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hc, map_one, one_mul] using hm

theorem derivationPreservesIdeal.commutator {I : Ideal A}
    {D E : Derivation ℚ A A}
    (hD : derivationPreservesIdeal I D)
    (hE : derivationPreservesIdeal I E) :
    derivationPreservesIdeal I ⁅D, E⁆ := by
  intro a ha
  rw [Derivation.commutator_apply]
  exact I.sub_mem (hD _ (hE a ha)) (hE _ (hD a ha))

/-- Starting with `V₁` and `V₂`, the nonzero rational commutator scalar
produces every positive `V_q`.  This uses only ideal closure under subtraction
and multiplication by elements of the ambient `ℚ`-algebra. -/
theorem terminalBlockVectorFields_preserve_of_one_two
    (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)
    (I : Ideal (MvPolynomial (Keep ⊕ Fin d) R))
    (hV₁ : derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d 1))
    (hV₂ : derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d 2)) :
    ∀ q, 1 ≤ q → derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d q) := by
  have hge₂ : ∀ n : ℕ, derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d (n + 2)) := by
    intro n
    induction n with
    | zero => exact hV₂
    | succ n ih =>
        let q := n + 2
        let c : ℚ := -(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2)
        have hq : 2 ≤ q := by omega
        have hc : c ≠ 0 := by
          change -(((q : ℚ) - 1) * ((q : ℚ) + 2) / 2) ≠ 0
          exact terminalCommutatorScalar_ne_zero q hq
        have hbracket : derivationPreservesIdeal I
            ⁅terminalBlockVectorField R Keep d 1,
              terminalBlockVectorField R Keep d q⁆ :=
          hV₁.commutator ih
        have hscaled : derivationPreservesIdeal I
            (c • terminalBlockVectorField R Keep d (q + 1)) := by
          rw [← terminalBlockVectorField_commutator_one R Keep d q]
          exact hbracket
        have := hscaled.of_smul hc
        exact this
  intro q hq
  by_cases hq₁ : q = 1
  · subst q
    exact hV₁
  · have hq₂ : 2 ≤ q := by omega
    have hsplit : q - 2 + 2 = q := Nat.sub_add_cancel hq₂
    rw [← hsplit]
    exact hge₂ (q - 2)

end Ideals

section GlobalExtraction

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- Coefficient membership for a one-block parameter homomorphism is derived
from an actual global parameter homomorphism.  `hglobal` is global ideal
preservation, `hcomponents` is closure under actual global multigraded
components, and `haxis` identifies the one-block coefficient with the
corresponding component of the global image. -/
theorem blockParameter_coeff_mem_of_global_components
    {Γ : Type*}
    (J : MvPolynomial (Keep ⊕ Fin d) R →ₐ[ℚ]
      MvPolynomial (Keep ⊕ Fin d) R)
    (I : Ideal (MvPolynomial (Keep ⊕ Fin d) R))
    (component : Γ → MvPolynomial (Keep ⊕ Fin d) R →
      MvPolynomial (Keep ⊕ Fin d) R)
    (axis : ℕ → Γ)
    (hglobal : ∀ a ∈ I, J a ∈ I)
    (hcomponents : ∀ a ∈ I, ∀ γ, component γ a ∈ I)
    (haxis : ∀ a k,
      (stirlingParameterHom R Keep d a).coeff k = component (axis k) (J a)) :
    ∀ a ∈ I, ∀ k, (stirlingParameterHom R Keep d a).coeff k ∈ I := by
  intro a ha k
  rw [haxis]
  exact hcomponents (J a) (hglobal a ha) (axis k)

/-- The first two logarithmic derivations preserve the ideal only after the
global preservation/component hypotheses have supplied their coefficient
closure. -/
theorem stirlingLogDerivations_preserve_of_global_components
    {Γ : Type*}
    (J : MvPolynomial (Keep ⊕ Fin d) R →ₐ[ℚ]
      MvPolynomial (Keep ⊕ Fin d) R)
    (I : Ideal (MvPolynomial (Keep ⊕ Fin d) R))
    (component : Γ → MvPolynomial (Keep ⊕ Fin d) R →
      MvPolynomial (Keep ⊕ Fin d) R)
    (axis : ℕ → Γ)
    (hglobal : ∀ a ∈ I, J a ∈ I)
    (hcomponents : ∀ a ∈ I, ∀ γ, component γ a ∈ I)
    (haxis : ∀ a k,
      (stirlingParameterHom R Keep d a).coeff k = component (axis k) (J a)) :
    derivationPreservesIdeal I
        (stirlingParameterFirstDerivation R Keep d) ∧
      derivationPreservesIdeal I
        (stirlingParameterSecondLogDerivation R Keep d) := by
  have hcoeff := blockParameter_coeff_mem_of_global_components R Keep d
    J I component axis hglobal hcomponents haxis
  constructor
  · exact polynomialParameterFirstDerivation_preserves_ideal
      (stirlingParameterHom R Keep d)
      (stirlingParameterHom_coeff_zero R Keep d) I
      (fun a ha => hcoeff a ha 1)
  · exact polynomialParameterSecondLogDerivation_preserves_ideal
      (stirlingParameterHom R Keep d)
      (stirlingParameterHom_coeff_zero R Keep d) I
      (fun a ha => hcoeff a ha 1)
      (fun a ha => hcoeff a ha 2)

/-- Global multigraded component closure and global parameter-hom ideal
preservation therefore imply preservation by every bounded block field.
No one-block ideal-invariance premise occurs in this statement. -/
theorem terminalBlockVectorFields_preserve_of_global_components
    {Γ : Type*}
    (J : MvPolynomial (Keep ⊕ Fin d) R →ₐ[ℚ]
      MvPolynomial (Keep ⊕ Fin d) R)
    (I : Ideal (MvPolynomial (Keep ⊕ Fin d) R))
    (component : Γ → MvPolynomial (Keep ⊕ Fin d) R →
      MvPolynomial (Keep ⊕ Fin d) R)
    (axis : ℕ → Γ)
    (hglobal : ∀ a ∈ I, J a ∈ I)
    (hcomponents : ∀ a ∈ I, ∀ γ, component γ a ∈ I)
    (haxis : ∀ a k,
      (stirlingParameterHom R Keep d a).coeff k = component (axis k) (J a)) :
    ∀ q, 1 ≤ q → derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d q) := by
  obtain ⟨hL₁, hL₂⟩ :=
    stirlingLogDerivations_preserve_of_global_components R Keep d
      J I component axis hglobal hcomponents haxis
  have hV₁ : derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d 1) := by
    rw [stirlingParameterFirstDerivation_eq_neg_vectorField R Keep d] at hL₁
    have hnegneg := hL₁.neg
    rw [neg_neg] at hnegneg
    exact hnegneg
  have hhalfV₂ : derivationPreservesIdeal I
      ((1 / 2 : ℚ) • terminalBlockVectorField R Keep d 2) := by
    rw [← stirlingParameterSecondLogDerivation_eq_half_vectorField R Keep d]
    exact hL₂
  have hV₂ : derivationPreservesIdeal I
      (terminalBlockVectorField R Keep d 2) :=
    hhalfV₂.of_smul (by norm_num)
  exact terminalBlockVectorFields_preserve_of_one_two R Keep d I hV₁ hV₂

end GlobalExtraction

end AbelFormalization
