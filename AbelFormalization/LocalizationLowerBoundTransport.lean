import AbelFormalization.TransferCoefficientBounds

/-!
# Quantitative transport through cleared localization identities

This module isolates the elementary estimate used after terminal
localization.  A scalar has an inverse-power lower bound when its absolute
value is eventually bounded below by a positive constant divided by a fixed
power of the ambient scale.  Such bounds are closed under finite products
and natural powers.  Consequently an identity

`(prod v)^a * c_k = sum_j b_kj * G_j`

transports an inverse-power lower bound from the finite family `c` to `G`
when the coefficients `b` have uniform polynomial upper bounds.
-/

noncomputable section

namespace AbelFormalization

open Filter Finset

set_option autoImplicit false

variable {X ι κ δ : Type*}

/-- A scalar-valued function is eventually bounded below in absolute value
by an inverse power of a scale. -/
def HasScalarInversePowerLowerBound (l : Filter X) (R : X → ℝ)
    (f : X → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ,
    ∀ᶠ x in l, c / (R x) ^ M ≤ |f x|

theorem hasScalarInversePowerLowerBound_one
    (l : Filter X) (R : X → ℝ) :
    HasScalarInversePowerLowerBound l R (fun _ => 1) := by
  refine ⟨1, zero_lt_one, 0, ?_⟩
  filter_upwards [] with x
  simp

/-- Products of two scalar inverse-power lower bounds retain such a bound. -/
theorem HasScalarInversePowerLowerBound.mul
    {l : Filter X} {R f g : X → ℝ}
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hf : HasScalarInversePowerLowerBound l R f)
    (hg : HasScalarInversePowerLowerBound l R g) :
    HasScalarInversePowerLowerBound l R (fun x => f x * g x) := by
  obtain ⟨c, hc, M, hf⟩ := hf
  obtain ⟨d, hd, P, hg⟩ := hg
  refine ⟨c * d, mul_pos hc hd, M + P, ?_⟩
  filter_upwards [hR, hf, hg] with x hxR hfx hgx
  have hRpos : 0 < R x := zero_lt_one.trans_le hxR
  have hleft_nonneg : 0 ≤ c / (R x) ^ M :=
    div_nonneg hc.le (pow_nonneg hRpos.le _)
  have hright_nonneg : 0 ≤ d / (R x) ^ P :=
    div_nonneg hd.le (pow_nonneg hRpos.le _)
  calc
    (c * d) / (R x) ^ (M + P) =
        (c / (R x) ^ M) * (d / (R x) ^ P) := by
      rw [pow_add]
      field_simp
    _ ≤ |f x| * |g x| :=
      mul_le_mul hfx hgx hright_nonneg (abs_nonneg _)
    _ = |f x * g x| := (abs_mul _ _).symm

/-- Natural powers preserve scalar inverse-power lower bounds. -/
theorem HasScalarInversePowerLowerBound.pow
    {l : Filter X} {R f : X → ℝ}
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hf : HasScalarInversePowerLowerBound l R f) (a : ℕ) :
    HasScalarInversePowerLowerBound l R (fun x => (f x) ^ a) := by
  induction a with
  | zero => simpa using hasScalarInversePowerLowerBound_one l R
  | succ a ih =>
      simpa [pow_succ] using ih.mul hR hf

/-- A finite product of scalar inverse-power lower bounds retains such a
bound.  This also covers the empty product. -/
theorem hasScalarInversePowerLowerBound_finset_prod
    {l : Filter X} {R : X → ℝ} {δ : Type*}
    (s : Finset δ) (f : δ → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hf : ∀ i ∈ s, HasScalarInversePowerLowerBound l R (f i)) :
    HasScalarInversePowerLowerBound l R
      (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasScalarInversePowerLowerBound_one l R
  | @insert i s his ih =>
      have hi := hf i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa [Finset.prod_insert his] using hi.mul hR hs

/-- Multiplying every member of a finite family by one scalar carrying an
inverse-power lower bound preserves a family lower bound. -/
theorem HasScalarInversePowerLowerBound.mul_family
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R w : X → ℝ} {f : ι → X → ℝ}
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hw : HasScalarInversePowerLowerBound l R w)
    (hf : HasInversePowerLowerBound l R f) :
    HasInversePowerLowerBound l R (fun i x => w x * f i x) := by
  obtain ⟨d, hd, P, hw⟩ := hw
  obtain ⟨c, hc, M, hf⟩ := hf
  refine ⟨d * c, mul_pos hd hc, P + M, ?_⟩
  filter_upwards [hR, hw, hf] with x hxR hwx hfx
  obtain ⟨i, hi⟩ := exists_abs_eq_finiteFamilyMaxAbs f x
  have hfi : c / (R x) ^ M ≤ |f i x| := by simpa [hi] using hfx
  have hRpos : 0 < R x := zero_lt_one.trans_le hxR
  have hleft_nonneg : 0 ≤ d / (R x) ^ P :=
    div_nonneg hd.le (pow_nonneg hRpos.le _)
  have hright_nonneg : 0 ≤ c / (R x) ^ M :=
    div_nonneg hc.le (pow_nonneg hRpos.le _)
  calc
    (d * c) / (R x) ^ (P + M) =
        (d / (R x) ^ P) * (c / (R x) ^ M) := by
      rw [pow_add]
      field_simp
    _ ≤ |w x| * |f i x| :=
      mul_le_mul hwx hfi hright_nonneg (abs_nonneg _)
    _ = |w x * f i x| := (abs_mul _ _).symm
    _ ≤ finiteFamilyMaxAbs (fun i x => w x * f i x) x :=
      abs_le_finiteFamilyMaxAbs (fun i x => w x * f i x) x i

/-- The quantitative consequence of a finite family of localization
identities with one common denominator power. -/
theorem hasInversePowerLowerBound_of_clearedLocalizationIdentities
    [Fintype δ] [Fintype κ] [Nonempty κ]
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → ℝ}
    (v : δ → X → ℝ) (a : ℕ)
    (c : κ → X → ℝ) (G : ι → X → ℝ)
    (b : κ → ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hv : ∀ d, HasScalarInversePowerLowerBound l R (v d))
    (hc : HasInversePowerLowerBound l R c)
    (hb : HasUniformPolynomialUpperBound l R b)
    (hidentity : ∀ᶠ x in l, ∀ k,
      (∏ d, v d x) ^ a * c k x = ∑ j, b k j x * G j x) :
    HasInversePowerLowerBound l R G := by
  have hproduct : HasScalarInversePowerLowerBound l R
      (fun x => ∏ d, v d x) := by
    simpa using hasScalarInversePowerLowerBound_finset_prod
      (Finset.univ : Finset δ) v hR (fun d _ => hv d)
  have hpower := hproduct.pow hR a
  have hleft := hpower.mul_family hR hc
  exact hasInversePowerLowerBound_of_linearCombinations
    G (fun k x => (∏ d, v d x) ^ a * c k x) b hR
    hidentity hb hleft

/-- Variant in which polynomial upper bounds are supplied separately for
each coefficient.  Finiteness makes the constants and exponents uniform. -/
theorem hasInversePowerLowerBound_of_clearedLocalizationIdentities_of_finite
    [Fintype δ] [Fintype κ] [Nonempty κ]
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → ℝ}
    (v : δ → X → ℝ) (a : ℕ)
    (c : κ → X → ℝ) (G : ι → X → ℝ)
    (b : κ → ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hv : ∀ d, HasScalarInversePowerLowerBound l R (v d))
    (hc : HasInversePowerLowerBound l R c)
    (hb : ∀ k j, HasPolynomialUpperBound l R (b k j))
    (hidentity : ∀ᶠ x in l, ∀ k,
      (∏ d, v d x) ^ a * c k x = ∑ j, b k j x * G j x) :
    HasInversePowerLowerBound l R G := by
  exact hasInversePowerLowerBound_of_clearedLocalizationIdentities
    v a c G b hR hv hc
      (hasUniformPolynomialUpperBound_of_finite b hR hb) hidentity

end AbelFormalization
