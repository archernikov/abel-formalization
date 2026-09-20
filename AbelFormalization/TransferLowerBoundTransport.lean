import AbelFormalization.TransferFiniteBounds
import AbelFormalization.TransferScaleHierarchy
import AbelFormalization.Basic

/-!
# Review additions for the quantitative transfer bounds

This scratch file is intended to be compiled after `TransferFiniteBounds` is
installed as `AbelFormalization.TransferFiniteBounds`.  It does not modify the
root scratch modules or any maintained project file.

The first two closure properties already occur in `TransferFiniteBounds`; the
combined theorem below is the useful finite-expansion adapter.  The remaining
lemmas supply the missing perturbation orientation and the exact
`R -> X`/diagonal-normalization passage used at the end of `lem:transfer`.
-/

noncomputable section

namespace AbelFormalization

open Filter Finset
open scoped Topology

variable {X ι J : Type*}

/-- A finite sum of rapidly decaying terms remains rapidly decaying when each
term is multiplied by its own polynomially bounded factor.  No uniform choice
of coefficient exponent is needed: the finite-sum closure is applied after
the pointwise multiplication closure. -/
theorem superpolynomialDecay_finset_sum_mul_of_polynomialBound
    {l : Filter X} {R : X → ℝ}
    (s : Finset J) (e p : J → X → ℝ)
    (he : ∀ j ∈ s, Asymptotics.SuperpolynomialDecay l R (e j))
    (hR : ∀ᶠ x in l, 0 ≤ R x)
    (C : J → ℝ) (P : J → ℕ)
    (hC : ∀ j ∈ s, 0 ≤ C j)
    (hp : ∀ j ∈ s, ∀ᶠ x in l, |p j x| ≤ C j * (R x) ^ P j) :
    Asymptotics.SuperpolynomialDecay l R
      (fun x => ∑ j ∈ s, e j x * p j x) := by
  apply superpolynomialDecay_finset_sum s (fun j x => e j x * p j x)
  intro j hj
  exact Asymptotics.SuperpolynomialDecay.mul_of_polynomialBound
    (he j hj) hR (hC j hj) (hp j hj)

/-- Real-valued superpolynomial decay is closed under negation. -/
theorem Asymptotics.SuperpolynomialDecay.neg_real
    {l : Filter X} {R e : X → ℝ}
    (he : Asymptotics.SuperpolynomialDecay l R e) :
    Asymptotics.SuperpolynomialDecay l R (fun x => -e x) := by
  exact (he.const_mul (-1)).congr (fun x => by simp)

/-- Adding a superpolynomially decaying error preserves an inverse-power
lower bound.  This is the orientation used immediately after the identity
`normalizedSource = central + error`. -/
theorem hasInversePowerLowerBound_add_superpolynomialPerturbation
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → ℝ}
    (f e : ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (he : ∀ i, Asymptotics.SuperpolynomialDecay l R (e i))
    (hf : HasInversePowerLowerBound l R f) :
    HasInversePowerLowerBound l R (fun i x => f i x + e i x) := by
  refine hasInversePowerLowerBound_of_superpolynomialPerturbation
    (f := fun i x => f i x + e i x) (g := f)
    (e := fun i x => -e i x) hR ?_ ?_ hf
  · exact Filter.Eventually.of_forall (fun x i => by ring)
  · intro i
    exact Asymptotics.SuperpolynomialDecay.neg_real (he i)

/-- Inverse-power lower bounds are invariant under a superpolynomially
decaying perturbation. -/
theorem hasInversePowerLowerBound_add_superpolynomialPerturbation_iff
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → ℝ}
    (f e : ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (he : ∀ i, Asymptotics.SuperpolynomialDecay l R (e i)) :
    HasInversePowerLowerBound l R (fun i x => f i x + e i x) ↔
      HasInversePowerLowerBound l R f := by
  constructor
  · intro h
    exact hasInversePowerLowerBound_of_superpolynomialPerturbation
      f (fun i x => f i x + e i x) e hR
      (Filter.Eventually.of_forall (fun _ _ => rfl)) he h
  · exact hasInversePowerLowerBound_add_superpolynomialPerturbation f e hR he

/-- An inverse-power lower bound at a smaller scale is also one at a larger
scale.  Eventual `1 ≤ R` makes all denominators positive and is exactly the
hypothesis already used by the generator-list estimates. -/
theorem hasInversePowerLowerBound_mono_scale
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R S : X → ℝ} {f : ι → X → ℝ}
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hRS : ∀ᶠ x in l, R x ≤ S x)
    (hf : HasInversePowerLowerBound l R f) :
    HasInversePowerLowerBound l S f := by
  obtain ⟨c, hc, M, hf⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hR, hRS, hf] with x hxR hxRS hxf
  have hRpow : 0 < (R x) ^ M := pow_pos (zero_lt_one.trans_le hxR) M
  have hpows : (R x) ^ M ≤ (S x) ^ M :=
    pow_le_pow_left₀ (zero_le_one.trans hxR) hxRS M
  exact (div_le_div_of_nonneg_left hc.le hRpow hpows).trans hxf

/-- If `E u = exp u - 1` is bounded by a scale at least two, then `u` is
bounded by twice the logarithm of that scale.  The factor two is deliberately
loose; it avoids carrying an additive constant through the normalization
bound. -/
theorem le_two_mul_log_of_E_le {u S : ℝ}
    (hS : 2 ≤ S) (huS : E u ≤ S) :
    u ≤ 2 * Real.log S := by
  have hexp : Real.exp u ≤ S ^ 2 := by
    calc
      Real.exp u = E u + 1 := by simp [E]
      _ ≤ S + 1 := by simpa [add_comm] using add_le_add_right huS 1
      _ ≤ S ^ 2 := by nlinarith [sq_nonneg (S - 1)]
  calc
    u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ Real.log (S ^ 2) := Real.log_le_log (Real.exp_pos u) hexp
    _ = 2 * Real.log S := by rw [Real.log_pow]; norm_num

/-- A fixed integer normalization exponent is polynomially bounded once all
coordinates are bounded by a fixed natural multiple of `log S`.  Passing an
explicit natural `P` for the `ℓ1` norm avoids fragile coercion normalization
of `Int.natAbs` in downstream calls. -/
theorem abs_exp_lexicographicDot_le_pow_of_coord_le_nat_mul_log
    {h : ℕ} (lambda : Fin h → ℤ) (u : Fin h → ℝ)
    (S : ℝ) (U P : ℕ)
    (hS : 1 < S) (hu0 : ∀ i, 0 ≤ u i)
    (huS : ∀ i, u i ≤ (U : ℝ) * Real.log S)
    (hlambda : (∑ i, |(lambda i : ℝ)|) ≤ (P : ℝ)) :
    |Real.exp (lexicographicDot lambda u)| ≤ S ^ (U * P) := by
  have hlog0 : 0 ≤ Real.log S := (Real.log_pos hS).le
  have hUlog0 : 0 ≤ (U : ℝ) * Real.log S :=
    mul_nonneg (Nat.cast_nonneg U) hlog0
  have habs := abs_lexicographicDot_le lambda u
    ((U : ℝ) * Real.log S) hu0 huS
  have hdot : lexicographicDot lambda u ≤
      ((U * P : ℕ) : ℝ) * Real.log S := by
    calc
      lexicographicDot lambda u ≤ |lexicographicDot lambda u| := le_abs_self _
      _ ≤ (∑ i, |(lambda i : ℝ)|) *
          ((U : ℝ) * Real.log S) := habs
      _ ≤ (P : ℝ) * ((U : ℝ) * Real.log S) :=
        mul_le_mul_of_nonneg_right hlambda hUlog0
      _ = ((U * P : ℕ) : ℝ) * Real.log S := by push_cast; ring
  calc
    |Real.exp (lexicographicDot lambda u)| =
        Real.exp (lexicographicDot lambda u) :=
      abs_of_pos (Real.exp_pos _)
    _ ≤ Real.exp (((U * P : ℕ) : ℝ) * Real.log S) :=
      Real.exp_le_exp.mpr hdot
    _ = S ^ (U * P) := by
      rw [Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hS)]

/-- The concrete polynomial upper bound for the manuscript's normalization
factor.  Here `E (u_i) ≤ S` follows directly from the definition of the
source maximum `S = X`; eventual positivity of the `u_i` supplies `hu0`. -/
theorem abs_exp_lexicographicDot_le_sourceScale
    {h : ℕ} (lambda : Fin h → ℤ) (u : Fin h → ℝ)
    (S : ℝ) (P : ℕ)
    (hS : 2 ≤ S) (hu0 : ∀ i, 0 ≤ u i)
    (hES : ∀ i, E (u i) ≤ S)
    (hlambda : (∑ i, |(lambda i : ℝ)|) ≤ (P : ℝ)) :
    |Real.exp (lexicographicDot lambda u)| ≤ S ^ (2 * P) := by
  apply abs_exp_lexicographicDot_le_pow_of_coord_le_nat_mul_log
    lambda u S 2 P (one_lt_two.trans_le hS) hu0
  · intro i
    exact le_two_mul_log_of_E_le hS (hES i)
  · exact hlambda

/-- Uniform eventual form of the preceding normalization estimate for a
family of fixed integer weights. -/
theorem eventually_abs_exp_lexicographicDot_le_sourceScale
    {h : ℕ} {l : Filter X}
    (lambda : ι → Fin h → ℤ) (u : Fin h → X → ℝ)
    (S : X → ℝ) (P : ℕ)
    (hS : ∀ᶠ x in l, 2 ≤ S x)
    (hu0 : ∀ᶠ x in l, ∀ i, 0 ≤ u i x)
    (hES : ∀ᶠ x in l, ∀ i, E (u i x) ≤ S x)
    (hlambda : ∀ a, (∑ i, |(lambda a i : ℝ)|) ≤ (P : ℝ)) :
    ∀ᶠ x in l, ∀ a,
      |Real.exp (lexicographicDot (lambda a) (fun i => u i x))| ≤
        (S x) ^ (2 * P) := by
  filter_upwards [hS, hu0, hES] with x hxS hxu hxE
  intro a
  exact abs_exp_lexicographicDot_le_sourceScale
    (lambda a) (fun i => u i x) (S x) P hxS hxu hxE (hlambda a)

/-- Removing a coordinatewise polynomially bounded diagonal factor preserves
an inverse-power lower bound.  This is a specialization of the matrix lemma;
keeping it separate avoids rebuilding a Kronecker-delta matrix at each call. -/
theorem hasInversePowerLowerBound_of_bounded_diagonal
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {S : X → ℝ}
    (f c : ι → X → ℝ)
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    {C : ℝ} (hC : 0 < C) {P : ℕ}
    (hc : ∀ᶠ x in l, ∀ i, |c i x| ≤ C * (S x) ^ P)
    (hcf : HasInversePowerLowerBound l S
      (fun i x => c i x * f i x)) :
    HasInversePowerLowerBound l S f := by
  classical
  let a : ι → ι → X → ℝ :=
    fun b i x => if i = b then c b x else 0
  apply hasInversePowerLowerBound_of_linearCombinations
    f (fun i x => c i x * f i x) a hS
  · exact Filter.Eventually.of_forall (fun x b => by simp [a])
  · refine ⟨C, hC, P, ?_⟩
    filter_upwards [hc] with x hx
    intro b i
    by_cases hib : i = b
    · subst i
      simpa [a] using hx b
    · have hnonneg : 0 ≤ C * (S x) ^ P :=
        (abs_nonneg (c b x)).trans (hx b)
      simpa [a, hib] using hnonneg
  · exact hcf

/-- The complete abstract normalization/scale passage used in quantitative
transfer.  A lower bound for `c_i * f_i` at scale `R` is first weakened to
the larger scale `S`, then the polynomially bounded diagonal factors are
removed. -/
theorem hasInversePowerLowerBound_of_normalization_and_scale
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R S : X → ℝ}
    (f c : ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hRS : ∀ᶠ x in l, R x ≤ S x)
    {C : ℝ} (hC : 0 < C) {P : ℕ}
    (hc : ∀ᶠ x in l, ∀ i, |c i x| ≤ C * (S x) ^ P)
    (hnormalized : HasInversePowerLowerBound l R
      (fun i x => c i x * f i x)) :
    HasInversePowerLowerBound l S f := by
  have hS : ∀ᶠ x in l, 1 ≤ S x := by
    filter_upwards [hR, hRS] with x hxR hxRS
    exact hxR.trans hxRS
  have hnormalizedS : HasInversePowerLowerBound l S
      (fun i x => c i x * f i x) :=
    hasInversePowerLowerBound_mono_scale hR hRS hnormalized
  exact hasInversePowerLowerBound_of_bounded_diagonal
    f c hS hC hc hnormalizedS

/-- Direct specialization of normalization-and-scale transfer to the factors
`exp (lambda_i · u)`.  This is the endpoint matching manuscript equation
`exp (lambda_a · u) f_a = g_a + epsilon_a`. -/
theorem hasInversePowerLowerBound_of_exp_normalization_and_scale
    [Fintype ι] [Nonempty ι]
    {h : ℕ} {l : Filter X} {R S : X → ℝ}
    (f : ι → X → ℝ)
    (lambda : ι → Fin h → ℤ) (u : Fin h → X → ℝ)
    (P : ℕ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hRS : ∀ᶠ x in l, R x ≤ S x)
    (hS : ∀ᶠ x in l, 2 ≤ S x)
    (hu0 : ∀ᶠ x in l, ∀ i, 0 ≤ u i x)
    (hES : ∀ᶠ x in l, ∀ i, E (u i x) ≤ S x)
    (hlambda : ∀ a, (∑ i, |(lambda a i : ℝ)|) ≤ (P : ℝ))
    (hnormalized : HasInversePowerLowerBound l R
      (fun a x =>
        Real.exp (lexicographicDot (lambda a) (fun i => u i x)) * f a x)) :
    HasInversePowerLowerBound l S f := by
  have hc : ∀ᶠ x in l, ∀ a,
      |Real.exp (lexicographicDot (lambda a) (fun i => u i x))| ≤
        1 * (S x) ^ (2 * P) := by
    filter_upwards
      [eventually_abs_exp_lexicographicDot_le_sourceScale
        lambda u S P hS hu0 hES hlambda] with x hx
    intro a
    simpa only [one_mul] using hx a
  exact hasInversePowerLowerBound_of_normalization_and_scale
    f (fun a x => Real.exp
      (lexicographicDot (lambda a) (fun i => u i x)))
      hR hRS (C := 1) one_pos hc hnormalized

end AbelFormalization
