import AbelFormalization.HermiteCoefficientReality
import AbelFormalization.RealTransferJetSubstitution
import AbelFormalization.TransferFiniteBounds
import AbelFormalization.TransferScaleHierarchy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Real Hermite jets along separated sequences

This module joins the two real/complex bridges used by quantitative transfer.
At a real node tuple, the real-part jet supplied by
`FullHermiteLemmaSpec.realHermiteJetSubstitutionData` is the original
Abel--Hermite coefficient, viewed in `Complex`.  Along a sequence whose center
is separated from the logarithm of the comparison scale, its coordinate
error has superpolynomial decay.

The decay statement keeps the necessary hypotheses visible.  Node tuples
remain in the fixed Hermite neighborhood, centers remain beyond `u0`, the
comparison scale is eventually at least two, and `u / log R` tends to
infinity.  Positivity of `u` by itself would not imply the conclusion.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Metric Set
open scoped Topology

/-! ## A real-node specialization of the Hermite jet data -/

/-- The canonical real substitution data associated to an Abel--Hermite
coefficient evaluated on a real node tuple. -/
def FullHermiteLemmaSpec.realNodeHermiteJetSubstitutionData
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) (δ : ι → Real)
    (hδ : (fun i => (δ i : Complex)) ∈ hermiteNodeNeighborhood B) :
    RealCentralJetSubstitutionData A u d :=
  H.realHermiteJetSubstitutionData d hd hu hδ

@[simp]
theorem FullHermiteLemmaSpec.realNodeHermiteJetSubstitutionData_sourceJet
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) (δ : ι → Real)
    (hδ : (fun i => (δ i : Complex)) ∈ hermiteNodeNeighborhood B)
    (r : Fin d) :
    (H.realNodeHermiteJetSubstitutionData d hd hu δ hδ).sourceJet r =
      (abelHermiteCoeff branch B m (E u)
        (fun i => (δ i : Complex)) (r.val + 1)).re := by
  rfl

/-- At real nodes, the real source coordinate is exactly the manuscript's
unsplit Abel--Hermite coefficient after coercion to `Complex`. -/
theorem FullHermiteLemmaSpec.coe_realNodeHermiteJetSubstitutionData_sourceJet
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (hB : 0 < B) (d : Nat) (hd : d + 1 = totalMultiplicity m)
    {u : Real} (hu : u0 < u) (δ : ι → Real)
    (hδ : (fun i => (δ i : Complex)) ∈ hermiteNodeNeighborhood B)
    (r : Fin d) :
    (((H.realNodeHermiteJetSubstitutionData d hd hu δ hδ).sourceJet r :
        Real) : Complex) =
      abelHermiteCoeff branch B m (E u)
        (fun i => (δ i : Complex)) (r.val + 1) := by
  change ((abelHermiteCoeff branch B m (E u)
      (fun i => (δ i : Complex)) (r.val + 1)).re : Complex) = _
  exact H.ofReal_re_abelHermiteCoeff_eq_of_real_nodes
    hB d hd hu δ hδ r

/-! ## The canonical sequence of real-node Hermite jets -/

/-- Pointwise real Hermite data along sequences of centers and real node
tuples. -/
def FullHermiteLemmaSpec.realNodeHermiteJetSequence
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    (u : Nat → Real) (hu : ∀ n, u0 < u n)
    (δ : Nat → ι → Real)
    (hδ : ∀ n, (fun i => (δ n i : Complex)) ∈ hermiteNodeNeighborhood B) :
    ∀ n, RealCentralJetSubstitutionData A (u n) d :=
  fun n => H.realNodeHermiteJetSubstitutionData d hd (hu n) (δ n) (hδ n)

/-- Every source coordinate in the canonical sequence is the unsplit
Abel--Hermite coefficient. -/
theorem FullHermiteLemmaSpec.coe_realNodeHermiteJetSequence_sourceJet
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (hB : 0 < B) (d : Nat) (hd : d + 1 = totalMultiplicity m)
    (u : Nat → Real) (hu : ∀ n, u0 < u n)
    (δ : Nat → ι → Real)
    (hδ : ∀ n, (fun i => (δ n i : Complex)) ∈ hermiteNodeNeighborhood B)
    (n : Nat) (r : Fin d) :
    (((H.realNodeHermiteJetSequence d hd u hu δ hδ n).sourceJet r :
        Real) : Complex) =
      abelHermiteCoeff branch B m (E (u n))
        (fun i => (δ n i : Complex)) (r.val + 1) := by
  exact H.coe_realNodeHermiteJetSubstitutionData_sourceJet
    hB d hd (hu n) (δ n) (hδ n) r

/-! ## Exponential error envelopes -/

/-- In the standard decreasing multiscale hierarchy, logarithmic separation
of the last (smallest) center implies the same separation for every center.
This is the form used to apply the one-block Hermite error theorem at each
coordinate. -/
theorem tendsto_scaleCoordinate_div_log_atTop_of_strictAnti
    {h : Nat} (u : Fin (h + 1) → Nat → Real) (R : Nat → Real)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hlast : Tendsto
      (fun n => u (Fin.last h) n / Real.log (R n)) atTop atTop)
    (i : Fin (h + 1)) :
    Tendsto (fun n => u i n / Real.log (R n)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hlast
  filter_upwards [horder, hR] with n hnorder hnR
  have hlog : 0 < Real.log (R n) :=
    Real.log_pos (one_lt_two.trans_le hnR)
  exact (div_le_div_iff_of_pos_right hlog).2
    (hnorder.antitone (Fin.le_last i))

/-- If `u / log R` tends to infinity and `R` is eventually at least two,
then the one-extra-scale Hermite envelope `exp (-u) * (1 + u)` has
superpolynomial decay in `R`.

The linear factor is absorbed by splitting `exp (-u)` into two half
exponentials.  One half is superpolynomial in `R`; the other makes
`(1 + u)` tend to zero and hence eventually bounded. -/
theorem exp_neg_mul_one_add_superpolynomialDecay_of_div_log
    {u R : Nat → Real}
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : Tendsto
      (fun n => u n / Real.log (R n)) atTop atTop) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n => Real.exp (-u n) * (1 + u n)) := by
  have huTop : Tendsto u atTop atTop := by
    have h := tendsto_sub_mul_log_atTop hseparated hR 0
    simpa using h
  have hhalf : Asymptotics.SuperpolynomialDecay atTop R
      (fun n => Real.exp (-(1 / 2 : Real) * u n)) := by
    intro M
    have hgap0 := tendsto_sub_mul_log_atTop hseparated hR
      (2 * (M : Real))
    have hgap : Tendsto
        (fun n => (1 / 2 : Real) *
          (u n - (2 * (M : Real)) * Real.log (R n)))
        atTop atTop :=
      hgap0.const_mul_atTop (by norm_num : (0 : Real) < 1 / 2)
    have hexp := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hgap)
    apply hexp.congr'
    filter_upwards [hR] with n hnR
    have hRpos : 0 < R n :=
      zero_lt_one.trans (one_lt_two.trans_le hnR)
    symm
    rw [← Real.exp_log hRpos, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [Function.comp_apply]
    ring
  have hfactorAtTop : Tendsto
      (fun x : Real => (1 + x) * Real.exp (-(1 / 2 : Real) * x))
      atTop (𝓝 0) := by
    have hzero := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (0 : Real) (1 / 2) (by norm_num : (0 : Real) < 1 / 2)
    have hone := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : Real) (1 / 2) (by norm_num : (0 : Real) < 1 / 2)
    simpa only [Real.rpow_zero, Real.rpow_one, add_mul, one_mul,
      zero_add] using hzero.add hone
  have hfactor : Tendsto
      (fun n => (1 + u n) * Real.exp (-(1 / 2 : Real) * u n))
      atTop (𝓝 0) := hfactorAtTop.comp huTop
  have hfactorBound : ∀ᶠ n in atTop,
      |(1 + u n) * Real.exp (-(1 / 2 : Real) * u n)| ≤
        (1 : Real) * R n ^ (0 : Nat) := by
    have hnear := hfactor.eventually
      (Metric.ball_mem_nhds (0 : Real) zero_lt_one)
    filter_upwards [hnear] with n hn
    have hn' : |(1 + u n) *
        Real.exp (-(1 / 2 : Real) * u n)| < 1 := by
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hn
    simpa only [pow_zero, mul_one] using hn'.le
  have hRnonneg : ∀ᶠ n in atTop, 0 ≤ R n :=
    hR.mono (fun n hn => (by linarith : 0 ≤ R n))
  have hproduct :=
    Asymptotics.SuperpolynomialDecay.mul_of_polynomialBound
      hhalf hRnonneg (show (0 : Real) ≤ 1 by norm_num) hfactorBound
  apply hproduct.congr
  intro n
  have hsplit : Real.exp (-u n) =
      Real.exp (-(1 / 2 : Real) * u n) *
        Real.exp (-(1 / 2 : Real) * u n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  ring

/-! ## Superpolynomial decay of the actual Hermite coordinate errors -/

/-- Each coordinate error of the real-node Hermite sequence has
superpolynomial decay.  The node-neighborhood hypothesis is exactly the
radius input used by `FullHermiteLemmaSpec.remainder_bound`; the logarithmic
separation hypothesis supplies the decay missing from mere positivity. -/
theorem FullHermiteLemmaSpec.realNodeHermiteJetSequence_error_superpolynomialDecay
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    (u : Nat → Real) (hu : ∀ n, u0 < u n)
    (δ : Nat → ι → Real)
    (hδ : ∀ n, (fun i => (δ n i : Complex)) ∈ hermiteNodeNeighborhood B)
    (R : Nat → Real)
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : Tendsto
      (fun n => u n / Real.log (R n)) atTop atTop)
    (r : Fin d) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n =>
        (H.realNodeHermiteJetSequence d hd u hu δ hδ n).error r) := by
  have henv0 := exp_neg_mul_one_add_superpolynomialDecay_of_div_log
    hR hseparated
  have henv : Asymptotics.SuperpolynomialDecay atTop R
      (fun n => Real.exp (-u n) * (Kr * (1 + u n))) := by
    apply (henv0.mul_const Kr).congr
    intro n
    ring
  apply henv.trans_eventually_abs_le
  filter_upwards with n
  simp only [Function.comp_apply]
  have herr := H.abs_realHermiteJetSubstitutionData_error_le
    d hd (hu n) (hδ n) r
  have hun : 0 < u n := H.centralThreshold_pos.trans (hu n)
  have henvnonneg :
      0 ≤ Real.exp (-u n) * (Kr * (1 + u n)) := by
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg H.remainderConstant_pos.le (by linarith))
  rw [abs_of_nonneg henvnonneg]
  simpa only [FullHermiteLemmaSpec.realNodeHermiteJetSequence,
    FullHermiteLemmaSpec.realNodeHermiteJetSubstitutionData] using herr

/-- The preceding result simultaneously for all finitely many jet
coordinates. -/
theorem FullHermiteLemmaSpec.realNodeHermiteJetSequence_errors_superpolynomialDecay
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (d : Nat) (hd : d + 1 = totalMultiplicity m)
    (u : Nat → Real) (hu : ∀ n, u0 < u n)
    (δ : Nat → ι → Real)
    (hδ : ∀ n, (fun i => (δ n i : Complex)) ∈ hermiteNodeNeighborhood B)
    (R : Nat → Real)
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : Tendsto
      (fun n => u n / Real.log (R n)) atTop atTop) :
    ∀ r : Fin d, Asymptotics.SuperpolynomialDecay atTop R
      (fun n =>
        (H.realNodeHermiteJetSequence d hd u hu δ hδ n).error r) := by
  intro r
  exact H.realNodeHermiteJetSequence_error_superpolynomialDecay
    d hd u hu δ hδ R hR hseparated r

/-- Coordinatewise decay of the jet errors is exactly what is needed for
the global error assignment: scale and time coordinates are identically
zero, while a jet coordinate selects one of the supplied errors. -/
theorem realCentralTransferCoordinateError_superpolynomialDecay_of_errors
    {h : Nat} {A : Real → Real}
    {u : Fin h → Nat → Real} {d : Fin h → Nat}
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    {R : Nat → Real}
    (herror : ∀ i (r : Fin (d i)),
      Asymptotics.SuperpolynomialDecay atTop R
        (fun n => (jets n i).error r))
    (x : Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n => realCentralTransferCoordinateError (jets n) x) := by
  cases x with
  | inl i =>
      apply (Asymptotics.superpolynomialDecay_zero atTop R).congr
      intro n
      rfl
  | inr x =>
      cases x with
      | inl ir =>
          rcases ir with ⟨i, r⟩
          simpa only [realCentralTransferCoordinateError] using herror i r
      | inr i =>
          apply (Asymptotics.superpolynomialDecay_zero atTop R).congr
          intro n
          rfl

/-! ## A single packaged integration statement -/

/-- The canonical real Hermite sequence, its exact source-coordinate
identification, and rapid decay of every coordinate error. -/
theorem FullHermiteLemmaSpec.exists_realNodeHermiteJetSequence
    {ι : Type*} [Fintype ι] {A : Real → Real} {B : Real}
    {m : ι → Nat} {X0 K K0 u0 ε Kr : Real}
    {branch : Real → Complex → Complex} {F : Complex → Complex}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (hB : 0 < B) (d : Nat) (hd : d + 1 = totalMultiplicity m)
    (u : Nat → Real) (hu : ∀ n, u0 < u n)
    (δ : Nat → ι → Real)
    (hδ : ∀ n, (fun i => (δ n i : Complex)) ∈ hermiteNodeNeighborhood B)
    (R : Nat → Real)
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : Tendsto
      (fun n => u n / Real.log (R n)) atTop atTop) :
    ∃ jets : ∀ n, RealCentralJetSubstitutionData A (u n) d,
      (∀ n r, (((jets n).sourceJet r : Real) : Complex) =
        abelHermiteCoeff branch B m (E (u n))
          (fun i => (δ n i : Complex)) (r.val + 1)) ∧
      (∀ r, Asymptotics.SuperpolynomialDecay atTop R
        (fun n => (jets n).error r)) := by
  let jets : ∀ n, RealCentralJetSubstitutionData A (u n) d :=
    H.realNodeHermiteJetSequence d hd u hu δ hδ
  refine ⟨jets, ?_, ?_⟩
  · intro n r
    exact H.coe_realNodeHermiteJetSequence_sourceJet
      hB d hd u hu δ hδ n r
  · intro r
    exact H.realNodeHermiteJetSequence_error_superpolynomialDecay
      d hd u hu δ hδ R hR hseparated r

/-- A closed real radius bound implies the open Hermite-neighborhood
hypothesis used above, thanks to the fixed quarter-unit margin. -/
theorem realNodeSequence_mem_hermiteNodeNeighborhood
    {ι : Type*} [Fintype ι] {B : Real}
    (δ : Nat → ι → Real) (hδ : ∀ n i, |δ n i| ≤ B) :
    ∀ n, (fun i => (δ n i : Complex)) ∈ hermiteNodeNeighborhood B := by
  intro n
  apply closed_nodes_subset_hermiteNodeNeighborhood B
  intro i
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hδ n i

end AbelFormalization
