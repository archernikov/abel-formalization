import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Completeness

/-! # Division by a small perturbation in a real Banach algebra

A continuous linear operator `Q` which is a left inverse to multiplication
by `s` provides division by every sufficiently small perturbation `f` of `s`.
The quotient is constructed from the convergent Neumann inverse of
`id - Q ∘ mulLeft (s - f)`. The remainder is the actual difference `g - f*q`
and belongs to the kernel of `Q`.

This is an abstract Banach algebra theorem. It does not assert that a space
of analytic coefficients has the required norm, product, or division map.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The error operator for division by a perturbation of `s`. -/
def divisionPerturbation (Q : B →L[ℝ] B) (s f : B) : B →L[ℝ] B :=
  Q.comp (ContinuousLinearMap.mul ℝ B (s - f))

@[simp]
theorem divisionPerturbation_apply (Q : B →L[ℝ] B) (s f a : B) :
    divisionPerturbation Q s f a = Q ((s - f) * a) := rfl

theorem norm_divisionPerturbation_le (Q : B →L[ℝ] B) (s f : B) :
    ‖divisionPerturbation Q s f‖ ≤ ‖Q‖ * ‖s - f‖ := by
  exact (Q.opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_apply_le ℝ B (s - f))
      (norm_nonneg Q))

/-- The invertible operator in the Neumann construction is exactly division
followed by multiplication by the perturbed element. -/
theorem one_sub_divisionPerturbation_apply (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (a : B) :
    (1 - divisionPerturbation Q s f : B →L[ℝ] B) a = Q (f * a) := by
  change a - Q ((s - f) * a) = Q (f * a)
  rw [sub_mul, map_sub, hs]
  abel

variable [CompleteSpace B]

/-- The actual quotient operator, obtained from the Neumann inverse. -/
def banachDivisionQuotient (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) : B →L[ℝ] B :=
  (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B).comp Q

/-- Multiplication by the perturbed element followed by `Q` inverts the
quotient operator on the right-hand side of the division equation. -/
theorem banachDivisionQuotient_equation (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    Q (f * banachDivisionQuotient Q s f hT g) = Q g := by
  rw [← one_sub_divisionPerturbation_apply Q s f hs]
  have he := congrArg (fun L : B →L[ℝ] B => L (Q g))
    (Units.oneSub (divisionPerturbation Q s f) hT).val_inv
  exact he

/-- The quotient of `f*a` is exactly `a`. -/
theorem banachDivisionQuotient_mul (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (a : B) :
    banachDivisionQuotient Q s f hT (f * a) = a := by
  change (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B) (Q (f * a)) = a
  rw [← one_sub_divisionPerturbation_apply Q s f hs]
  have he := congrArg (fun L : B →L[ℝ] B => L a)
    (Units.oneSub (divisionPerturbation Q s f) hT).inv_val
  exact he

/-- The constructed quotient makes the actual remainder belong to `ker Q`. -/
theorem banachDivisionQuotient_spec (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    Q (g - f * banachDivisionQuotient Q s f hT g) = 0 := by
  rw [map_sub, banachDivisionQuotient_equation Q s f hs hT, sub_self]

/-- The vanishing of `Q` on the remainder determines the quotient uniquely. -/
theorem banachDivisionQuotient_unique (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1)
    (g q : B) (hq : Q (g - f * q) = 0) :
    q = banachDivisionQuotient Q s f hT g := by
  rw [map_sub, sub_eq_zero] at hq
  calc
    q = banachDivisionQuotient Q s f hT (f * q) :=
      (banachDivisionQuotient_mul Q s f hs hT q).symm
    _ = banachDivisionQuotient Q s f hT g := by
      change (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B) (Q (f * q)) =
        (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B) (Q g)
      rw [hq]

theorem banachDivision_existsUnique (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ∃! q : B, Q (g - f * q) = 0 :=
  ⟨banachDivisionQuotient Q s f hT g, banachDivisionQuotient_spec Q s f hs hT g,
    fun q hq => banachDivisionQuotient_unique Q s f hs hT g q hq⟩

/-- The actual remainder operator. -/
def banachDivisionRemainder (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) : B →L[ℝ] B :=
  1 - (ContinuousLinearMap.mul ℝ B f).comp (banachDivisionQuotient Q s f hT)

@[simp]
theorem banachDivisionRemainder_apply (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    banachDivisionRemainder Q s f hT g = g - f * banachDivisionQuotient Q s f hT g := rfl

theorem banachDivision_identity (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    g = f * banachDivisionQuotient Q s f hT g + banachDivisionRemainder Q s f hT g := by
  rw [banachDivisionRemainder_apply]
  abel

theorem banachDivisionRemainder_mem_ker (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    banachDivisionRemainder Q s f hT g ∈ LinearMap.ker Q.toLinearMap :=
  banachDivisionQuotient_spec Q s f hs hT g

/-- Fixed-point form of the quotient, used to bound its norm. -/
theorem banachDivisionQuotient_fixed_point (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    banachDivisionQuotient Q s f hT g =
      Q g + divisionPerturbation Q s f (banachDivisionQuotient Q s f hT g) := by
  apply sub_eq_iff_eq_add.mp
  exact (one_sub_divisionPerturbation_apply Q s f hs _).trans
    (banachDivisionQuotient_equation Q s f hs hT g)

/-- The sharper quotient bound in terms of the norm of `Q g`. -/
theorem norm_banachDivisionQuotient_le (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ‖banachDivisionQuotient Q s f hT g‖ ≤ ‖Q g‖ / (1 - ‖divisionPerturbation Q s f‖) := by
  have hnorm : ‖banachDivisionQuotient Q s f hT g‖ ≤
      ‖Q g‖ + ‖divisionPerturbation Q s f‖ * ‖banachDivisionQuotient Q s f hT g‖ := by
    calc
      ‖banachDivisionQuotient Q s f hT g‖ =
          ‖Q g + divisionPerturbation Q s f (banachDivisionQuotient Q s f hT g)‖ :=
        congrArg norm (banachDivisionQuotient_fixed_point Q s f hs hT g)
      _ ≤ ‖Q g‖ + ‖divisionPerturbation Q s f (banachDivisionQuotient Q s f hT g)‖ :=
        norm_add_le _ _
      _ ≤ ‖Q g‖ + ‖divisionPerturbation Q s f‖ * ‖banachDivisionQuotient Q s f hT g‖ :=
        add_le_add le_rfl ((divisionPerturbation Q s f).le_opNorm _)
  apply (le_div_iff₀ (sub_pos.mpr hT)).mpr
  nlinarith

/-- A bound uniform in the right-hand side of the division problem. -/
theorem norm_banachDivisionQuotient_le_opNorm (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ‖banachDivisionQuotient Q s f hT g‖ ≤
      ‖Q‖ * ‖g‖ / (1 - ‖divisionPerturbation Q s f‖) :=
  (norm_banachDivisionQuotient_le Q s f hs hT g).trans
    (div_le_div_of_nonneg_right (Q.le_opNorm g) (sub_pos.mpr hT).le)

/-- The norm of the bounded quotient operator itself. -/
theorem opNorm_banachDivisionQuotient_le (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) :
    ‖banachDivisionQuotient Q s f hT‖ ≤ ‖Q‖ / (1 - ‖divisionPerturbation Q s f‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg Q) (sub_pos.mpr hT).le)
  intro g
  convert norm_banachDivisionQuotient_le_opNorm Q s f hs hT g using 1
  ring

/-- A corresponding bound for the actual remainder. -/
theorem norm_banachDivisionRemainder_le (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ‖banachDivisionRemainder Q s f hT g‖ ≤
      ‖g‖ + ‖f‖ * (‖Q‖ * ‖g‖ / (1 - ‖divisionPerturbation Q s f‖)) := by
  rw [banachDivisionRemainder_apply]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_banachDivisionQuotient_le_opNorm Q s f hs hT g) (norm_nonneg f))))

/-- A sufficient smallness condition expressed directly in `s-f` and `Q`. -/
theorem banachDivision_existsUnique_of_norm_mul_lt_one (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hsmall : ‖Q‖ * ‖s - f‖ < 1) (g : B) :
    ∃! q : B, Q (g - f * q) = 0 :=
  banachDivision_existsUnique Q s f hs ((norm_divisionPerturbation_le Q s f).trans_lt hsmall) g

end AbelFormalization
