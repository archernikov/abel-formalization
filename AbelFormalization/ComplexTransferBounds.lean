import AbelFormalization.TransferLowerBoundTransport
import Mathlib.Analysis.Complex.Basic

/-!
# Quantitative transfer bounds for complex evaluations

The analytic jet substitution is naturally complex-valued, while the scales
in the quantitative reduction are real.  This file is the norm-valued analogue
of `TransferFiniteBounds` and `TransferLowerBoundTransport`.

`ComplexSuperpolynomialDecay l R e` means that the real function `‖e‖`
has superpolynomial decay relative to the real scale `R`.  The remaining
definitions use the maximum complex norm in a nonempty finite family.  The
last theorem packages the complete abstract quantitative-transfer argument.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Finset
open scoped BigOperators Topology

variable {X ι κ J : Type*}

/-! ## Max norms and polynomial bounds -/

/-- The maximum norm in a nonempty finite complex family. -/
def finiteFamilyMaxNorm [Fintype ι] [Nonempty ι]
    (f : ι → X → Complex) (x : X) : Real :=
  (Finset.univ.image fun i => ‖f i x‖).max' (by simp)

theorem norm_le_finiteFamilyMaxNorm [Fintype ι] [Nonempty ι]
    (f : ι → X → Complex) (x : X) (i : ι) :
    ‖f i x‖ ≤ finiteFamilyMaxNorm f x := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem exists_norm_eq_finiteFamilyMaxNorm [Fintype ι] [Nonempty ι]
    (f : ι → X → Complex) (x : X) :
    ∃ i, ‖f i x‖ = finiteFamilyMaxNorm f x := by
  have hm := Finset.max'_mem (Finset.univ.image fun i => ‖f i x‖) (by simp)
  obtain ⟨i, _hi, himax⟩ := Finset.mem_image.mp hm
  exact ⟨i, himax⟩

theorem finiteFamilyMaxNorm_nonneg [Fintype ι] [Nonempty ι]
    (f : ι → X → Complex) (x : X) : 0 ≤ finiteFamilyMaxNorm f x := by
  obtain ⟨i, hi⟩ := exists_norm_eq_finiteFamilyMaxNorm f x
  rw [← hi]
  exact norm_nonneg _

/-- A nonempty complex family is eventually bounded below by an inverse
power of the real scale. -/
def HasComplexInversePowerLowerBound (l : Filter X) (R : X → Real)
    [Fintype ι] [Nonempty ι] (f : ι → X → Complex) : Prop :=
  ∃ c : Real, 0 < c ∧ ∃ M : Nat,
    ∀ᶠ x in l, c / (R x) ^ M ≤ finiteFamilyMaxNorm f x

/-- Uniform polynomial norm bounds for a finite matrix of complex
coefficient functions. -/
def HasUniformComplexPolynomialUpperBound (l : Filter X) (R : X → Real)
    (a : κ → ι → X → Complex) : Prop :=
  ∃ C : Real, 0 < C ∧ ∃ P : Nat,
    ∀ᶠ x in l, ∀ b i, ‖a b i x‖ ≤ C * (R x) ^ P

/-- A complex function decays superpolynomially when its real norm does. -/
def ComplexSuperpolynomialDecay (l : Filter X) (R : X → Real)
    (e : X → Complex) : Prop :=
  Asymptotics.SuperpolynomialDecay l R (fun x => ‖e x‖)

/-! ## Finite complex linear combinations -/

theorem norm_complexLinearCombination_le [Fintype ι] [Nonempty ι]
    (f : ι → Complex) (a : ι → Complex) (H : Real)
    (hH : 0 ≤ H) (ha : ∀ i, ‖a i‖ ≤ H) :
    ‖∑ i, a i * f i‖ ≤
      (Fintype.card ι : Real) * H *
        finiteFamilyMaxNorm (fun i (_ : Unit) => f i) () := by
  let F : Real := finiteFamilyMaxNorm (fun i (_ : Unit) => f i) ()
  have hF : 0 ≤ F := finiteFamilyMaxNorm_nonneg _ _
  calc
    ‖∑ i, a i * f i‖ ≤ ∑ i, ‖a i * f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, H * F := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (ha i)
        (norm_le_finiteFamilyMaxNorm (fun i (_ : Unit) => f i) () i)
        (norm_nonneg _) hH
    _ = (Fintype.card ι : Real) * H * F := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem finiteFamilyMaxNorm_linearCombination_le
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (f : ι → Complex) (g : κ → Complex)
    (a : κ → ι → Complex) (H : Real)
    (hH : 0 ≤ H) (ha : ∀ b i, ‖a b i‖ ≤ H)
    (hg : ∀ b, g b = ∑ i, a b i * f i) :
    finiteFamilyMaxNorm (fun b (_ : Unit) => g b) () ≤
      (Fintype.card ι : Real) * H *
        finiteFamilyMaxNorm (fun i (_ : Unit) => f i) () := by
  obtain ⟨b, hb⟩ := exists_norm_eq_finiteFamilyMaxNorm
    (fun b (_ : Unit) => g b) ()
  rw [← hb, hg b]
  exact norm_complexLinearCombination_le f (a b) H hH (ha b)

/-- The pointwise arithmetic for changing a finite complex generating list. -/
theorem complexInversePowerLowerBound_pointwise
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (R c C : Real) (M P : Nat)
    (f : ι → Complex) (g : κ → Complex)
    (a : κ → ι → Complex)
    (hR : 1 ≤ R) (_hc : 0 < c) (hC : 0 < C)
    (ha : ∀ b i, ‖a b i‖ ≤ C * R ^ P)
    (hg : ∀ b, g b = ∑ i, a b i * f i)
    (hlower : c / R ^ M ≤
      finiteFamilyMaxNorm (fun b (_ : Unit) => g b) ()) :
    (c / ((Fintype.card ι : Real) * C)) / R ^ (M + P) ≤
      finiteFamilyMaxNorm (fun i (_ : Unit) => f i) () := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hcard : (0 : Real) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hK : 0 < (Fintype.card ι : Real) * C := mul_pos hcard hC
  have hmax := finiteFamilyMaxNorm_linearCombination_le
    f g a (C * R ^ P) (mul_nonneg hC.le (pow_nonneg hRpos.le _)) ha hg
  have hraw : c / R ^ M ≤
      (Fintype.card ι : Real) * (C * R ^ P) *
        finiteFamilyMaxNorm (fun i (_ : Unit) => f i) () :=
    hlower.trans hmax
  apply (div_le_iff₀ (pow_pos hRpos (M + P))).2
  apply (div_le_iff₀ hK).2
  have hcraw : c ≤
      ((Fintype.card ι : Real) * (C * R ^ P) *
        finiteFamilyMaxNorm (fun i (_ : Unit) => f i) ()) * R ^ M :=
    (div_le_iff₀ (pow_pos hRpos M)).1 hraw
  calc
    c ≤ ((Fintype.card ι : Real) * (C * R ^ P) *
        finiteFamilyMaxNorm (fun i (_ : Unit) => f i) ()) * R ^ M := hcraw
    _ = finiteFamilyMaxNorm (fun i (_ : Unit) => f i) () * R ^ (M + P) *
        ((Fintype.card ι : Real) * C) := by rw [pow_add]; ring

theorem hasComplexInversePowerLowerBound_of_linearCombinations
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {l : Filter X} {R : X → Real}
    (f : ι → X → Complex) (g : κ → X → Complex)
    (a : κ → ι → X → Complex)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hg : ∀ᶠ x in l, ∀ b, g b x = ∑ i, a b i x * f i x)
    (ha : HasUniformComplexPolynomialUpperBound l R a)
    (hglower : HasComplexInversePowerLowerBound l R g) :
    HasComplexInversePowerLowerBound l R f := by
  obtain ⟨C, hC, P, ha⟩ := ha
  obtain ⟨c, hc, M, hglower⟩ := hglower
  refine ⟨c / ((Fintype.card ι : Real) * C), ?_, M + P, ?_⟩
  · have hcard : (0 : Real) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    positivity
  · filter_upwards [hR, hg, ha, hglower] with x hxR hxg hxa hxlower
    exact complexInversePowerLowerBound_pointwise
      (R x) c C M P (fun i => f i x) (fun b => g b x)
        (fun b i => a b i x) hxR hc hC hxa hxg hxlower

/-! ## Norm-superpolynomial closure properties -/

theorem ComplexSuperpolynomialDecay.congr
    {l : Filter X} {R : X → Real} {e f : X → Complex}
    (he : ComplexSuperpolynomialDecay l R e)
    (hef : ∀ x, e x = f x) :
    ComplexSuperpolynomialDecay l R f := by
  unfold ComplexSuperpolynomialDecay at he ⊢
  exact he.congr (fun x => congrArg norm (hef x))

theorem ComplexSuperpolynomialDecay.congr'
    {l : Filter X} {R : X → Real} {e f : X → Complex}
    (he : ComplexSuperpolynomialDecay l R e)
    (hef : e =ᶠ[l] f) :
    ComplexSuperpolynomialDecay l R f := by
  unfold ComplexSuperpolynomialDecay at he ⊢
  exact he.congr' (hef.mono (fun _ hx => congrArg norm hx))

theorem complexSuperpolynomialDecay_zero
    (l : Filter X) (R : X → Real) :
    ComplexSuperpolynomialDecay l R (fun _ => (0 : Complex)) := by
  unfold ComplexSuperpolynomialDecay
  exact (Asymptotics.superpolynomialDecay_zero l R).congr (fun x => by simp)

theorem ComplexSuperpolynomialDecay.neg
    {l : Filter X} {R : X → Real} {e : X → Complex}
    (he : ComplexSuperpolynomialDecay l R e) :
    ComplexSuperpolynomialDecay l R (fun x => -e x) := by
  unfold ComplexSuperpolynomialDecay at he ⊢
  exact he.congr (fun x => (norm_neg (e x)).symm)

theorem ComplexSuperpolynomialDecay.add
    {l : Filter X} {R : X → Real} {e f : X → Complex}
    (he : ComplexSuperpolynomialDecay l R e)
    (hf : ComplexSuperpolynomialDecay l R f) :
    ComplexSuperpolynomialDecay l R (fun x => e x + f x) := by
  unfold ComplexSuperpolynomialDecay at he hf ⊢
  have hsum : Asymptotics.SuperpolynomialDecay l R
      (fun x => ‖e x‖ + ‖f x‖) := by
    change Asymptotics.SuperpolynomialDecay l R
      ((fun x => ‖e x‖) + fun x => ‖f x‖)
    exact he.add hf
  apply hsum.trans_abs_le
  intro x
  simpa only [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using
    norm_add_le (e x) (f x)

theorem ComplexSuperpolynomialDecay.sub
    {l : Filter X} {R : X → Real} {e f : X → Complex}
    (he : ComplexSuperpolynomialDecay l R e)
    (hf : ComplexSuperpolynomialDecay l R f) :
    ComplexSuperpolynomialDecay l R (fun x => e x - f x) := by
  exact ComplexSuperpolynomialDecay.congr
    (ComplexSuperpolynomialDecay.add he (ComplexSuperpolynomialDecay.neg hf))
    (fun x => by simp [sub_eq_add_neg])

/-- Embed a nonnegative real rapidly decaying factor into `Complex`. -/
theorem ComplexSuperpolynomialDecay.of_real_nonneg
    {l : Filter X} {R r : X → Real}
    (hr : Asymptotics.SuperpolynomialDecay l R r)
    (hr0 : ∀ᶠ x in l, 0 ≤ r x) :
    ComplexSuperpolynomialDecay l R (fun x => (r x : Complex)) := by
  unfold ComplexSuperpolynomialDecay
  apply hr.congr'
  filter_upwards [hr0] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

/-- Multiplication by a complex function with a polynomial norm bound
preserves norm-superpolynomial decay. -/
theorem ComplexSuperpolynomialDecay.mul_of_polynomialBound
    {l : Filter X} {R : X → Real} {e p : X → Complex}
    {C : Real} {P : Nat}
    (he : ComplexSuperpolynomialDecay l R e)
    (hR : ∀ᶠ x in l, 0 ≤ R x) (hC : 0 ≤ C)
    (hp : ∀ᶠ x in l, ‖p x‖ ≤ C * (R x) ^ P) :
    ComplexSuperpolynomialDecay l R (fun x => e x * p x) := by
  unfold ComplexSuperpolynomialDecay at he ⊢
  have hp' : ∀ᶠ x in l, |‖p x‖| ≤ C * (R x) ^ P :=
    hp.mono (fun x hx => by simpa only [abs_of_nonneg (norm_nonneg _)] using hx)
  have hproduct :=
    Asymptotics.SuperpolynomialDecay.mul_of_polynomialBound he hR hC hp'
  exact hproduct.congr (fun x => (norm_mul (e x) (p x)).symm)

theorem complexSuperpolynomialDecay_finset_sum
    {l : Filter X} {R : X → Real}
    (s : Finset J) (e : J → X → Complex)
    (he : ∀ j ∈ s, ComplexSuperpolynomialDecay l R (e j)) :
    ComplexSuperpolynomialDecay l R (fun x => ∑ j ∈ s, e j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (complexSuperpolynomialDecay_zero l R).congr (by simp)
  | @insert j s hjs ih =>
      have hj := he j (Finset.mem_insert_self j s)
      have hs := ih (fun k hk => he k (Finset.mem_insert_of_mem hk))
      exact (hj.add hs).congr (fun x => by simp [Finset.sum_insert hjs])

theorem complexSuperpolynomialDecay_finset_sum_mul_of_polynomialBound
    {l : Filter X} {R : X → Real}
    (s : Finset J) (e p : J → X → Complex)
    (he : ∀ j ∈ s, ComplexSuperpolynomialDecay l R (e j))
    (hR : ∀ᶠ x in l, 0 ≤ R x)
    (C : J → Real) (P : J → Nat)
    (hC : ∀ j ∈ s, 0 ≤ C j)
    (hp : ∀ j ∈ s, ∀ᶠ x in l, ‖p j x‖ ≤ C j * (R x) ^ P j) :
    ComplexSuperpolynomialDecay l R
      (fun x => ∑ j ∈ s, e j x * p j x) := by
  apply complexSuperpolynomialDecay_finset_sum s
    (fun j x => e j x * p j x)
  intro j hj
  exact (he j hj).mul_of_polynomialBound hR (hC j hj) (hp j hj)

/-- A convenient inverse-power estimate extracted from norm-superpolynomial
decay. -/
theorem ComplexSuperpolynomialDecay.eventually_norm_le_div
    {l : Filter X} {R : X → Real} {e : X → Complex}
    (he : ComplexSuperpolynomialDecay l R e)
    (hR : ∀ᶠ x in l, 1 ≤ R x) {c : Real} (hc : 0 < c) (M : Nat) :
    ∀ᶠ x in l, ‖e x‖ ≤ c / (R x) ^ M := by
  have hibound := (he M).eventually (Metric.ball_mem_nhds 0 hc)
  filter_upwards [hibound, hR] with x hx hxR
  rw [Real.dist_eq, sub_zero, abs_mul, abs_pow,
    abs_of_nonneg (zero_le_one.trans hxR),
    abs_of_nonneg (norm_nonneg (e x))] at hx
  have hpow : 0 < (R x) ^ M := pow_pos (zero_lt_one.trans_le hxR) M
  apply (le_div_iff₀ hpow).2
  simpa only [mul_comm] using hx.le

/-! ## Perturbation and scale transport -/

theorem hasComplexInversePowerLowerBound_of_eventuallyEq
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → Real} {f g : ι → X → Complex}
    (hfg : ∀ᶠ x in l, ∀ i, f i x = g i x)
    (hf : HasComplexInversePowerLowerBound l R f) :
    HasComplexInversePowerLowerBound l R g := by
  obtain ⟨c, hc, M, hf⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hf, hfg] with x hx hxeq
  have hmax : finiteFamilyMaxNorm f x = finiteFamilyMaxNorm g x := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := exists_norm_eq_finiteFamilyMaxNorm f x
      rw [← hi, hxeq i]
      exact norm_le_finiteFamilyMaxNorm g x i
    · obtain ⟨i, hi⟩ := exists_norm_eq_finiteFamilyMaxNorm g x
      rw [← hi, ← hxeq i]
      exact norm_le_finiteFamilyMaxNorm f x i
  exact hx.trans_eq hmax

theorem hasComplexInversePowerLowerBound_of_superpolynomialPerturbation
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → Real}
    (f g e : ι → X → Complex)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hge : ∀ᶠ x in l, ∀ i, g i x = f i x + e i x)
    (he : ∀ i, ComplexSuperpolynomialDecay l R (e i))
    (hg : HasComplexInversePowerLowerBound l R g) :
    HasComplexInversePowerLowerBound l R f := by
  obtain ⟨c, hc, M, hg⟩ := hg
  have herr : ∀ᶠ x in l, ∀ i,
      ‖e i x‖ ≤ (c / 2) / (R x) ^ M := by
    apply Filter.eventually_all.mpr
    intro i
    exact (he i).eventually_norm_le_div hR (half_pos hc) M
  refine ⟨c / 2, half_pos hc, M, ?_⟩
  filter_upwards [hge, hg, herr] with x hxge hxg hxerr
  obtain ⟨j, hj⟩ := exists_norm_eq_finiteFamilyMaxNorm g x
  have hgj : c / (R x) ^ M ≤ ‖g j x‖ := by simpa only [hj] using hxg
  have htriangle : ‖g j x‖ ≤ ‖f j x‖ + ‖e j x‖ := by
    rw [hxge j]
    exact norm_add_le _ _
  have hfj : ‖f j x‖ ≤ finiteFamilyMaxNorm f x :=
    norm_le_finiteFamilyMaxNorm f x j
  have hsplit : c / (R x) ^ M =
      (c / 2) / (R x) ^ M + (c / 2) / (R x) ^ M := by ring
  rw [hsplit] at hgj
  linarith [hxerr j]

theorem hasComplexInversePowerLowerBound_add_superpolynomialPerturbation
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → Real}
    (f e : ι → X → Complex)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (he : ∀ i, ComplexSuperpolynomialDecay l R (e i))
    (hf : HasComplexInversePowerLowerBound l R f) :
    HasComplexInversePowerLowerBound l R (fun i x => f i x + e i x) := by
  refine hasComplexInversePowerLowerBound_of_superpolynomialPerturbation
    (f := fun i x => f i x + e i x) (g := f)
    (e := fun i x => -e i x) hR ?_ ?_ hf
  · exact Filter.Eventually.of_forall (fun _ _ => by simp)
  · intro i
    exact (he i).neg

theorem hasComplexInversePowerLowerBound_mono_scale
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R S : X → Real} {f : ι → X → Complex}
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hRS : ∀ᶠ x in l, R x ≤ S x)
    (hf : HasComplexInversePowerLowerBound l R f) :
    HasComplexInversePowerLowerBound l S f := by
  obtain ⟨c, hc, M, hf⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hR, hRS, hf] with x hxR hxRS hxf
  have hRpow : 0 < (R x) ^ M := pow_pos (zero_lt_one.trans_le hxR) M
  have hpows : (R x) ^ M ≤ (S x) ^ M :=
    pow_le_pow_left₀ (zero_le_one.trans hxR) hxRS M
  exact (div_le_div_of_nonneg_left hc.le hRpow hpows).trans hxf

theorem hasComplexInversePowerLowerBound_of_bounded_diagonal
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {S : X → Real}
    (f c : ι → X → Complex)
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    {C : Real} (hC : 0 < C) {P : Nat}
    (hc : ∀ᶠ x in l, ∀ i, ‖c i x‖ ≤ C * (S x) ^ P)
    (hcf : HasComplexInversePowerLowerBound l S
      (fun i x => c i x * f i x)) :
    HasComplexInversePowerLowerBound l S f := by
  classical
  let a : ι → ι → X → Complex :=
    fun b i x => if i = b then c b x else 0
  apply hasComplexInversePowerLowerBound_of_linearCombinations
    f (fun i x => c i x * f i x) a hS
  · exact Filter.Eventually.of_forall (fun x b => by simp [a])
  · refine ⟨C, hC, P, ?_⟩
    filter_upwards [hc] with x hx
    intro b i
    by_cases hib : i = b
    · subst i
      simpa [a] using hx b
    · have hnonneg : 0 ≤ C * (S x) ^ P :=
        (norm_nonneg (c b x)).trans (hx b)
      simpa [a, hib] using hnonneg
  · exact hcf

theorem hasComplexInversePowerLowerBound_of_normalization_and_scale
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R S : X → Real}
    (f c : ι → X → Complex)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hRS : ∀ᶠ x in l, R x ≤ S x)
    {C : Real} (hC : 0 < C) {P : Nat}
    (hc : ∀ᶠ x in l, ∀ i, ‖c i x‖ ≤ C * (S x) ^ P)
    (hnormalized : HasComplexInversePowerLowerBound l R
      (fun i x => c i x * f i x)) :
    HasComplexInversePowerLowerBound l S f := by
  have hS : ∀ᶠ x in l, 1 ≤ S x := by
    filter_upwards [hR, hRS] with x hxR hxRS
    exact hxR.trans hxRS
  have hnormalizedS : HasComplexInversePowerLowerBound l S
      (fun i x => c i x * f i x) :=
    hasComplexInversePowerLowerBound_mono_scale hR hRS hnormalized
  exact hasComplexInversePowerLowerBound_of_bounded_diagonal
    f c hS hC hc hnormalizedS

/-- Complex-valued version of the exponential normalization endpoint. -/
theorem hasComplexInversePowerLowerBound_of_exp_normalization_and_scale
    [Fintype ι] [Nonempty ι]
    {h : Nat} {l : Filter X} {R S : X → Real}
    (f : ι → X → Complex)
    (lambda : ι → Fin h → Int) (u : Fin h → X → Real)
    (P : Nat)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hRS : ∀ᶠ x in l, R x ≤ S x)
    (hS : ∀ᶠ x in l, 2 ≤ S x)
    (hu0 : ∀ᶠ x in l, ∀ i, 0 ≤ u i x)
    (hES : ∀ᶠ x in l, ∀ i, E (u i x) ≤ S x)
    (hlambda : ∀ a,
      (∑ i, |(lambda a i : Real)|) ≤ (P : Real))
    (hnormalized : HasComplexInversePowerLowerBound l R
      (fun a x =>
        (Real.exp (lexicographicDot (lambda a) (fun i => u i x)) : Complex) *
          f a x)) :
    HasComplexInversePowerLowerBound l S f := by
  have hc : ∀ᶠ x in l, ∀ a,
      ‖(Real.exp
        (lexicographicDot (lambda a) (fun i => u i x)) : Complex)‖ ≤
          1 * (S x) ^ (2 * P) := by
    filter_upwards
      [eventually_abs_exp_lexicographicDot_le_sourceScale
        lambda u S P hS hu0 hES hlambda] with x hx
    intro a
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using hx a
  exact hasComplexInversePowerLowerBound_of_normalization_and_scale
    f (fun a x =>
      (Real.exp
        (lexicographicDot (lambda a) (fun i => u i x)) : Complex))
      hR hRS (C := 1) one_pos hc hnormalized

/-! ## Abstract complex quantitative transfer -/

variable {Canonical Central Original : Type*}

/-- The complete numerical core of quantitative transfer for complex
evaluations and real scales. -/
theorem complexQuantitativeTransfer_of_normalizedExpansion
    [Fintype Canonical] [Nonempty Canonical]
    [Fintype Central] [Nonempty Central]
    [Fintype Original] [Nonempty Original]
    {l : Filter X} {Rscale Xscale : X → Real}
    (source central error normalization : Canonical → X → Complex)
    (centralGenerator : Central → X → Complex)
    (centralCoefficient : Central → Canonical → X → Complex)
    (originalGenerator : Original → X → Complex)
    (sourceCoefficient : Canonical → Original → X → Complex)
    (hR : ∀ᶠ x in l, 1 ≤ Rscale x)
    (hRX : ∀ᶠ x in l, Rscale x ≤ Xscale x)
    (hcentralIdentity : ∀ᶠ x in l, ∀ b,
      centralGenerator b x =
        ∑ a, centralCoefficient b a x * central a x)
    (hcentralCoefficient :
      HasUniformComplexPolynomialUpperBound l Rscale centralCoefficient)
    (hcentralLower :
      HasComplexInversePowerLowerBound l Rscale centralGenerator)
    (hexpansion : ∀ᶠ x in l, ∀ a,
      normalization a x * source a x = central a x + error a x)
    (herror : ∀ a, ComplexSuperpolynomialDecay l Rscale (error a))
    {Cnormalization : Real} (hCnormalization : 0 < Cnormalization)
    {Pnormalization : Nat}
    (hnormalization : ∀ᶠ x in l, ∀ a,
      ‖normalization a x‖ ≤
        Cnormalization * (Xscale x) ^ Pnormalization)
    (hsourceIdentity : ∀ᶠ x in l, ∀ a,
      source a x =
        ∑ j, sourceCoefficient a j x * originalGenerator j x)
    (hsourceCoefficient :
      HasUniformComplexPolynomialUpperBound l Xscale sourceCoefficient) :
    HasComplexInversePowerLowerBound l Xscale originalGenerator := by
  have hcentral : HasComplexInversePowerLowerBound l Rscale central :=
    hasComplexInversePowerLowerBound_of_linearCombinations
      central centralGenerator centralCoefficient hR hcentralIdentity
        hcentralCoefficient hcentralLower
  have hcentralError : HasComplexInversePowerLowerBound l Rscale
      (fun a x => central a x + error a x) :=
    hasComplexInversePowerLowerBound_add_superpolynomialPerturbation
      central error hR herror hcentral
  have hnormalized : HasComplexInversePowerLowerBound l Rscale
      (fun a x => normalization a x * source a x) :=
    hasComplexInversePowerLowerBound_of_eventuallyEq
      (hexpansion.mono (fun x hx a => (hx a).symm)) hcentralError
  have hsource : HasComplexInversePowerLowerBound l Xscale source :=
    hasComplexInversePowerLowerBound_of_normalization_and_scale
      source normalization hR hRX hCnormalization hnormalization hnormalized
  have hX : ∀ᶠ x in l, 1 ≤ Xscale x := by
    filter_upwards [hR, hRX] with x hxR hxRX
    exact hxR.trans hxRX
  exact hasComplexInversePowerLowerBound_of_linearCombinations
    originalGenerator source sourceCoefficient hX hsourceIdentity
      hsourceCoefficient hsource

end AbelFormalization
