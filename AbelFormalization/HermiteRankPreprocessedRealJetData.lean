import AbelFormalization.HermiteRankTopPrefixPreprocessedSequenceBoundary
import AbelFormalization.HermiteRankTopPrefixClusterValues
import AbelFormalization.RealHermiteJetIntegration
import AbelFormalization.OrderedClusterIndividualRealJetEvaluation
import AbelFormalization.OrderedClusterSimultaneousRealJetEvaluation
import AbelFormalization.IndividualCentralQuantitativeTransfer

/-!
# Concrete real Hermite jets for the preprocessed rank boundary

This module supplies the analytic data used to evaluate the individual and
simultaneous central operations selected by the preprocessed top-prefix
boundary.  The common-strip extension already chosen by that boundary is
first upgraded to a full central Hermite specification; no second complex
extension is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Metric Set
open scoped Topology

namespace AbelFormalization

/-- A common-strip Hermite family built from one fixed complex extension has
the full central-remainder structure for the same extension. -/
theorem IsAbel.exists_fullHermiteLemmaSpec_of_commonStripFamily
    {A : ℝ → ℝ} (hA : IsAbel A)
    {ι : Type*} [Fintype ι]
    {B X K K0 : ℝ} {m : ι → ℕ} {F : ℂ → ℂ}
    (hB : 0 < B) (hX : 1 < X)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)))
    (hreal : ∀ t : ℝ, X < t → F (t : ℂ) = (A t : ℂ))
    (family : AbelHermiteFamilySpec A B m (X + B + 3) K K0
      (fun _ ↦ F)) :
    ∃ u0 ε Kr : ℝ,
      FullHermiteLemmaSpec A B m (X + B + 3) K K0 u0 ε Kr
        (fun _ ↦ F) F := by
  let X0 : ℝ := X + B + 3
  let U : ℝ := X0 + 1
  let Kc : ℝ := 1 + K
  have hK : 0 < K := family.extensionConstant_pos
  have hKc : 0 < Kc := by dsimp [Kc]; linarith
  have hF2 : AnalyticOnNhd ℂ F (rightHalfStrip X0 2) := by
    apply hF.mono
    intro z hz
    change X0 < z.re ∧ |z.im| < 2 at hz
    change X < z.re ∧ |z.im| < B + 2
    dsimp only [X0] at hz
    exact ⟨by linarith, by linarith⟩
  have hFbound : ∀ z ∈ rightHalfStrip X0 2,
      ‖F z‖ ≤ K * Real.log z.re := by
    intro z hz
    have hzball : z ∈ ball (z.re : ℂ) (B + 2) := by
      rw [mem_ball]
      have hdist : dist z (z.re : ℂ) = |z.im| := by
        calc
          dist z (z.re : ℂ) = dist z.im (z.re : ℂ).im :=
            Complex.dist_of_re_eq rfl
          _ = |z.im| := by simp
      rw [hdist]
      change X0 < z.re ∧ |z.im| < 2 at hz
      dsimp only [X0] at hz
      linarith
    exact family.branch_bound z.re (by simpa only [X0] using hz.1)
      z hzball
  have hjoint : AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ ↦ centralComplexFunction F v.1 v.2)
      (rightHalfStrip U 1 ×ˢ ball (0 : ℂ) (1 / 2)) := by
    simpa only [U] using centralComplexFunction_joint_analyticOnNhd hF2
  have hjointBound : ∀ u ∈ rightHalfStrip U 1,
      ∀ η : ℂ, ‖η‖ < 1 / 2 →
        ‖centralComplexFunction F u η‖ ≤ Kc * (1 + u.re) := by
    intro u hu η hη
    simpa only [U, Kc] using
      centralComplexFunction_norm_le
        (show 1 < X0 by dsimp [X0]; linarith) hK hFbound hu hη
  obtain ⟨D, hD, hrem⟩ :=
    exists_uniform_centralCoefficient_remainder_bounds m hB
  have hqStar : 0 < centralScaleRadius B := centralScaleRadius_pos hB
  let ε : ℝ := min (1 / 2) (centralScaleRadius B / 4)
  have hε : 0 < ε :=
    lt_min (by norm_num) (div_pos hqStar (by norm_num))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεone : ε ≤ 1 := by linarith
  have hεqhalf : ε < centralScaleRadius B / 2 := by
    have hh : ε ≤ centralScaleRadius B / 4 := min_le_right _ _
    linarith
  have hεq : ε < centralScaleRadius B :=
    hεqhalf.trans (half_lt_self hqStar)
  obtain ⟨u0, hu0, hUu0, htail⟩ :=
    exists_central_threshold (X + B + 3) U B hε hB
  let Kr : ℝ := 2 * D * Kc / centralScaleRadius B
  have hKr : 0 < Kr :=
    div_pos (mul_pos (mul_pos (by norm_num) hD) hKc) hqStar
  have hstrip : rightHalfStrip u0 ε ⊆ rightHalfStrip U 1 := by
    intro u hu
    exact ⟨hUu0.trans hu.1, hu.2.trans_le hεone⟩
  have hquarter : ∀ u ∈ rightHalfStrip U 1,
      AnalyticOnNhd ℂ (centralComplexFunction F u)
        (closedBall (0 : ℂ) (1 / 4)) :=
    fun _ hu ↦ centralComplexFunction_analyticOnNhd_quarter hjoint hu
  obtain ⟨_, _, hEX0, hExp0, _⟩ := htail u0 le_rfl
  refine ⟨u0, ε, Kr, {
    family := family
    centralThreshold_pos := hu0
    parameterRadius_pos := hε
    remainderConstant_pos := hKr
    threshold_compatible := hEX0
    exponentialScale_lt_radius := hExp0
    central_extension_analytic := ?_
    central_extension_realAgreement := ?_
    remainder_holomorphic := ?_
    remainder_bound := ?_
    central_identity := ?_ }⟩
  · exact hF.mono fun z hz ↦
      ⟨by linarith [hUu0, hz.1], by linarith [hεone, hz.2]⟩
  · intro u hu
    exact hreal u (by linarith [hUu0])
  · intro r hr
    exact centralRemainder_differentiableOn_domain hB hjoint m hr
      hUu0.le hεone hεqhalf.le
  · intro r hr v hv
    have huv : v.1.1 ∈ rightHalfStrip U 1 := hstrip hv.1.1
    have hupos : 0 < v.1.1.re := hu0.trans hv.1.1.1
    have hqv : ‖v.2‖ < centralScaleRadius B := by
      have hqε : ‖v.2‖ < ε := by
        simpa only [mem_ball, dist_zero_right] using hv.2
      exact hqε.trans hεq
    exact ((hrem F Kc v.1.1 v.1.2 hKc hupos (hquarter _ huv)
      (hjointBound _ huv) (fun i ↦ (hv.1.2 i).le) r hr).2 v.2 hqv).2
  · intro u hu δ hδ r hr hrd
    obtain ⟨hupos, hUu, hEX, _, hscale⟩ := htail u hu.le
    have huc : (u : ℂ) ∈ rightHalfStrip U 1 := ⟨hUu, by simp⟩
    have hFat : AnalyticAt ℂ F (u : ℂ) := by
      apply hF
      change X < u ∧ |(u : ℂ).im| < B + 2
      exact ⟨by linarith [hUu], by simp; linarith [hB]⟩
    have hGat : AnalyticAt ℂ F (E u : ℂ) :=
      family.branch_analytic (E u) hEX _
        (mem_ball_self (by linarith : 0 < B + 2))
    have heFgerm : (fun y : ℝ ↦ F (y : ℂ)) =ᶠ[nhds u]
        fun y ↦ (A y : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds (by linarith [hUu] : X < u)]
        with y hy
      exact hreal y hy
    have heGgerm : (fun y : ℝ ↦ F (y : ℂ)) =ᶠ[nhds (E u)]
        fun y ↦ (A y : ℂ) := by
      filter_upwards [ball_mem_nhds (E u)
          (by linarith : 0 < B + 2)] with y hy
      exact family.branch_realAgreement (E u) hEX y hy
    have hnodes : ∀ i, δ i ∈ ball (0 : ℂ) (B + 1) := by
      intro i
      have hi := hδ i
      simp only [mem_ball, dist_zero_right]
      linarith
    exact hA.normalizedHermiteCoeff_stirling_remainder δ m hupos
      (by linarith : 0 < B + 1) hFat hGat heFgerm heGgerm
      (family.shifted_analytic (E u) hEX) (hquarter _ huc)
      hscale hnodes hr hrd

/-! ## A common block-indexed real Hermite jet API -/

/-- The paper-rank node tuple of any representative block lies in the
common Hermite neighborhood whenever the bounded parameter is in the box.
This isolates the only node-radius check needed by both the individual and
simultaneous cluster operations. -/
theorem paperRankHermiteNodes_mem_hermiteNodeNeighborhood
    {ι : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 : ℝ} {branch : ℝ → ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 branch)
    (hB : 0 < B) (w : RestrictedBoxSpace p)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B)
    (block : Fin m) :
    (fun node ↦ (paperRankHermiteNodes D representative offset S block w node : ℂ)) ∈
      hermiteNodeNeighborhood B := by
  apply H.neighborhood_contains
  intro node
  rcases node with _ | j
  · simpa [paperRankHermiteNodes] using hB.le
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    simp only [paperRankHermiteNodes]
    split_ifs
    · exact hoffset j
    · simpa using hB.le

/-- One canonical real central-jet sequence for every block in an arbitrary
finite family.  The block family may be the singleton selected by an
individual decrement or the whole active cluster of a simultaneous step.
The coefficient ring and the Hermite node type remain literal. -/
def FullHermiteLemmaSpec.paperRankRealJetSequence
    {ι κ : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (hu : ∀ n i, u0 < u i n)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B) :
    ∀ n i, RealCentralJetSubstitutionData A (u i n)
      (paperRankHermitePositiveDerivativeCount S) :=
  fun n i ↦ H.realNodeHermiteJetSequence
    (paperRankHermitePositiveDerivativeCount S)
    (paperRankHermitePositiveDerivativeCount_add_one S)
    (u i) (fun q ↦ hu q i)
    (fun q ↦ paperRankHermiteNodes D representative offset S (block i) (w q))
    (fun q ↦ paperRankHermiteNodes_mem_hermiteNodeNeighborhood
      D representative offset S H.family hB (w q) (hoffset q) (block i)) n

/-- Every source coordinate of the block-indexed sequence is exactly the
unsplit Abel--Hermite coefficient at the corresponding pre-log center. -/
theorem FullHermiteLemmaSpec.coe_paperRankRealJetSequence_sourceJet
    {ι κ : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (hu : ∀ n i, u0 < u i n)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (n : ℕ) (i : κ) (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    ((((H.paperRankRealJetSequence D representative offset S hB
        block u hu w hoffset n i).sourceJet r : ℝ) : ℂ)) =
      abelHermiteCoeff (fun _ ↦ F) B (paperRankHermiteNodeMultiplicity S)
        (E (u i n))
        (fun node ↦ (paperRankHermiteNodes D representative offset S
          (block i) (w n) node : ℂ)) (r.val + 1) := by
  exact H.coe_realNodeHermiteJetSequence_sourceJet hB
    (paperRankHermitePositiveDerivativeCount S)
    (paperRankHermitePositiveDerivativeCount_add_one S)
    (u i) (fun q ↦ hu q i)
    (fun q ↦ paperRankHermiteNodes D representative offset S (block i) (w q))
    (fun q ↦ paperRankHermiteNodes_mem_hermiteNodeNeighborhood
      D representative offset S H.family hB (w q) (hoffset q) (block i)) n r

/-- The positive coefficient with zero-based index `r`, in the dependent
coefficient-list type of an arbitrary split block. -/
def paperRankHermitePositiveCoefficientIndex
    {ι Active Coeff : Type*} (S : Finset (ι × ℕ))
    (block : Active ⊕ Coeff)
    (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    Fin (Sum.elim (paperRankHermiteBlockDerivativeCount S Active)
      (paperRankHermiteBlockDerivativeCount S Coeff) block + 1) :=
  Fin.cast (congrArg (fun q : ℕ ↦ q + 1)
    (sum_elim_paperRankHermiteBlockDerivativeCount S Active Coeff block).symm)
    r.succ

@[simp]
theorem paperRankHermitePositiveCoefficientIndex_val
    {ι Active Coeff : Type*} (S : Finset (ι × ℕ))
    (block : Active ⊕ Coeff)
    (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    (paperRankHermitePositiveCoefficientIndex S block r).val = r.val + 1 :=
  rfl

/-- If a paper-rank parameter carries the expected pre-log center and the
same bounded coordinate, a jet source coordinate is exactly its concrete
positive Hermite coefficient. -/
theorem FullHermiteLemmaSpec.paperRankRealJetSequence_sourceJet_eq_coefficientValue
    {ι κ : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (hu : ∀ n i, u0 < u i n)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (sw : ℕ → PaperRankParameterSpace m p)
    (hcenter : ∀ n i, (sw n).1 (block i) = E (u i n))
    (hparameter : ∀ n, (sw n).2 = w n)
    (n : ℕ) (i : κ) (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    (H.paperRankRealJetSequence D representative offset S hB
        block u hu w hoffset n i).sourceJet r =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ ↦ F) (sw n) (Sum.inr (block i))
          (paperRankHermitePositiveCoefficientIndex S
            (Sum.inr (block i)) r) := by
  have he : (paperRankAllCoefficientBlockEquiv m).symm
      (Sum.inr (block i)) = block i := by
    apply (paperRankAllCoefficientBlockEquiv m).injective
    simp
  change
    (abelHermiteCoeff (fun _ ↦ F) B (paperRankHermiteNodeMultiplicity S)
      (E (u i n))
      (fun node ↦ (paperRankHermiteNodes D representative offset S
        (block i) (w n) node : ℂ)) (r.val + 1)).re = _
  simp only [paperRankHermiteCoefficientValue,
    paperRankHermitePositiveCoefficientIndex_val, he]
  rw [hcenter n i, hparameter n]

/-- The error in each block and derivative coordinate inherits the already
proved Hermite superpolynomial estimate. -/
theorem FullHermiteLemmaSpec.paperRankRealJetSequence_error_superpolynomialDecay
    {ι κ : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (hu : ∀ n i, u0 < u i n)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i, Tendsto
      (fun n ↦ u i n / Real.log (R n)) atTop atTop)
    (i : κ) (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (H.paperRankRealJetSequence D representative offset S hB
        block u hu w hoffset n i).error r) := by
  exact H.realNodeHermiteJetSequence_error_superpolynomialDecay
    (paperRankHermitePositiveDerivativeCount S)
    (paperRankHermitePositiveDerivativeCount_add_one S)
    (u i) (fun q ↦ hu q i)
    (fun q ↦ paperRankHermiteNodes D representative offset S (block i) (w q))
    (fun q ↦ paperRankHermiteNodes_mem_hermiteNodeNeighborhood
      D representative offset S H.family hB (w q) (hoffset q) (block i))
    R hR (hseparated i) r

/-- In particular, every real-jet error coordinate has a polynomial upper
bound at the same comparison scale. -/
theorem FullHermiteLemmaSpec.paperRankRealJetSequence_error_hasPolynomialUpperBound
    {ι κ : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (hu : ∀ n i, u0 < u i n)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i, Tendsto
      (fun n ↦ u i n / Real.log (R n)) atTop atTop)
    (i : κ) (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    HasPolynomialUpperBound atTop R
      (fun n ↦ (H.paperRankRealJetSequence D representative offset S hB
        block u hu w hoffset n i).error r) :=
  superpolynomialDecay_hasPolynomialUpperBound
    (H.paperRankRealJetSequence_error_superpolynomialDecay
      D representative offset S hB block u hu w hoffset R hR
      hseparated i r)

/-- Every source-jet coordinate is polynomially bounded whenever its
pre-log representative `E u` is bounded by the comparison scale.  This is
the coefficient bound supplied by the common Hermite family, with no new
analytic estimate. -/
theorem FullHermiteLemmaSpec.paperRankRealJetSequence_sourceJet_hasPolynomialUpperBound
    {ι κ : Type*} {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (hu : ∀ n i, u0 < u i n)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hEu : ∀ᶠ n in atTop, ∀ i, E (u i n) ≤ R n)
    (i : κ) (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    HasPolynomialUpperBound atTop R
      (fun n ↦ (H.paperRankRealJetSequence D representative offset S hB
        block u hu w hoffset n i).sourceJet r) := by
  refine ⟨2 * K0, mul_pos (by norm_num) H.family.coefficientConstant_pos,
    1, ?_⟩
  filter_upwards [hR, hEu] with n hnR hnEu
  let nodes : Option (Fin S.card) → ℂ := fun node ↦
    (paperRankHermiteNodes D representative offset S (block i) (w n) node : ℂ)
  have hnodes : nodes ∈ hermiteNodeNeighborhood B :=
    paperRankHermiteNodes_mem_hermiteNodeNeighborhood D representative offset S
      H.family hB (w n) (hoffset n) (block i)
  have hcenter : X0 < E (u i n) :=
    H.threshold_compatible.trans (E_strictMono (hu n i))
  have hr : r.val + 1 < totalMultiplicity
      (paperRankHermiteNodeMultiplicity S) := by
    change r.val + 1 < paperRankHermiteCoefficientCount S
    rw [← paperRankHermitePositiveDerivativeCount_add_one S]
    exact r.succ.isLt
  have hcoeff := H.family.coefficient_bound (E (u i n)) hcenter nodes hnodes
    (r.val + 1) hr
  have hsource := H.coe_paperRankRealJetSequence_sourceJet D representative
    offset S hB block u hu w hoffset n i r
  rw [← hsource] at hcoeff
  simp only [Complex.norm_real, Real.norm_eq_abs] at hcoeff
  exact hcoeff.trans <| calc
    K0 * (1 + E (u i n)) ≤ K0 * (2 * R n) := by
      apply mul_le_mul_of_nonneg_left _ H.family.coefficientConstant_pos.le
      linarith [hnEu i]
    _ = (2 * K0) * R n ^ (1 : ℕ) := by ring

/-! ## Removing the finite central threshold -/

/-- Finitely many divergent center sequences are uniformly beyond any
fixed threshold after discarding one finite prefix. -/
theorem exists_uniform_nat_tail_gt
    {κ : Type*} [Fintype κ] (u : κ → ℕ → ℝ)
    (huTop : ∀ i, Tendsto (u i) atTop atTop) (C : ℝ) :
    ∃ N : ℕ, ∀ n i, C < u i (n + N) := by
  have hall : ∀ᶠ n in atTop, ∀ i, C < u i n :=
    Filter.eventually_all.mpr fun i ↦
      (huTop i).eventually (eventually_gt_atTop C)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hall)
  refine ⟨N, fun n i ↦ hN (n + N) ?_ i⟩
  omega

/-- A fixed uniform tail index for a finite family of divergent centers. -/
noncomputable def uniformRealJetTail
    {κ : Type*} [Fintype κ] (u : κ → ℕ → ℝ)
    (huTop : ∀ i, Tendsto (u i) atTop atTop) (C : ℝ) : ℕ :=
  Classical.choose (exists_uniform_nat_tail_gt u huTop C)

theorem uniformRealJetTail_spec
    {κ : Type*} [Fintype κ] (u : κ → ℕ → ℝ)
    (huTop : ∀ i, Tendsto (u i) atTop atTop) (C : ℝ)
    (n : ℕ) (i : κ) :
    C < u i (n + uniformRealJetTail u huTop C) :=
  (Classical.choose_spec (exists_uniform_nat_tail_gt u huTop C)) n i

/-- The canonical block-indexed real jets after the automatically chosen
uniform threshold tail. -/
def FullHermiteLemmaSpec.paperRankRealJetTailSequence
    {ι κ : Type*} [Fintype κ] {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (huTop : ∀ i, Tendsto (u i) atTop atTop)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B) :
    ∀ n i, RealCentralJetSubstitutionData A
      (u i (n + uniformRealJetTail u huTop u0))
      (paperRankHermitePositiveDerivativeCount S) :=
  H.paperRankRealJetSequence D representative offset S hB block
    (fun i n ↦ u i (n + uniformRealJetTail u huTop u0))
    (fun n i ↦ uniformRealJetTail_spec u huTop u0 n i)
    (fun n ↦ w (n + uniformRealJetTail u huTop u0))
    (fun n j ↦ hoffset (n + uniformRealJetTail u huTop u0) j)

/-- Exact source-jet lookup for the automatically tailed sequence. -/
theorem FullHermiteLemmaSpec.coe_paperRankRealJetTailSequence_sourceJet
    {ι κ : Type*} [Fintype κ] {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (huTop : ∀ i, Tendsto (u i) atTop atTop)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (n : ℕ) (i : κ)
    (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    ((((H.paperRankRealJetTailSequence D representative offset S hB block u
      huTop w hoffset n i).sourceJet r : ℝ) : ℂ)) =
      abelHermiteCoeff (fun _ ↦ F) B (paperRankHermiteNodeMultiplicity S)
        (E (u i (n + uniformRealJetTail u huTop u0)))
        (fun node ↦ (paperRankHermiteNodes D representative offset S (block i)
          (w (n + uniformRealJetTail u huTop u0)) node : ℂ))
        (r.val + 1) := by
  exact H.coe_paperRankRealJetSequence_sourceJet D representative offset S hB
    block (fun i n ↦ u i (n + uniformRealJetTail u huTop u0))
    (fun n i ↦ uniformRealJetTail_spec u huTop u0 n i)
    (fun n ↦ w (n + uniformRealJetTail u huTop u0))
    (fun n j ↦ hoffset (n + uniformRealJetTail u huTop u0) j) n i r

/-- Superpolynomial Hermite error decay is preserved by the automatically
chosen threshold tail. -/
theorem FullHermiteLemmaSpec.paperRankRealJetTailSequence_error_superpolynomialDecay
    {ι κ : Type*} [Fintype κ] {m p : ℕ}
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    {A : ℝ → ℝ} {B X0 K K0 u0 ε Kr : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (block : κ → Fin m) (u : κ → ℕ → ℝ)
    (huTop : ∀ i, Tendsto (u i) atTop atTop)
    (w : ℕ → RestrictedBoxSpace p)
    (hoffset : ∀ n (j : Fin S.card),
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) (w n)| ≤ B)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i, Tendsto
      (fun n ↦ u i n / Real.log (R n)) atTop atTop)
    (i : κ) (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    Asymptotics.SuperpolynomialDecay atTop
      (fun n ↦ R (n + uniformRealJetTail u huTop u0))
      (fun n ↦ (H.paperRankRealJetTailSequence D representative offset S hB
        block u huTop w hoffset n i).error r) := by
  let N := uniformRealJetTail u huTop u0
  have hshift : Tendsto (fun n : ℕ ↦ n + N) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N
  apply H.paperRankRealJetSequence_error_superpolynomialDecay
    D representative offset S hB block
    (fun i n ↦ u i (n + N))
    (fun n i ↦ uniformRealJetTail_spec u huTop u0 n i)
    (fun n ↦ w (n + N)) (fun n j ↦ hoffset (n + N) j)
  · exact hshift.eventually hR
  · intro k
    exact (hseparated k).comp hshift

/-! ## The concrete selected boundary and its cluster-prefix parameters -/

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

/-- The original sequence index selected by both the representative-cluster
subsequence and the fixed balancing subsequence. -/
def selectedIndex (n : ℕ) : ℕ :=
  data.subsequence (boundary.preprocessed.balancingSubsequence n)

/-- The actual paper-rank parameter at the selected boundary, with its
bounded coordinate translated to the origin as in the rank package. -/
def selectedTranslatedParameter (n : ℕ) : PaperRankParameterSpace m p :=
  (restrictedSourceTranslateToZero w₀ (x (boundary.selectedIndex D
    representative offset radius Fsys x w₀ hw₀ data n))).1

@[simp]
theorem selectedTranslatedParameter_representative
    (n : ℕ) (i : Fin m) :
    (boundary.selectedTranslatedParameter D representative offset radius Fsys
      x w₀ hw₀ data n).1 i =
      (x (boundary.selectedIndex D representative offset radius Fsys
        x w₀ hw₀ data n)).1.1 i :=
  rfl

@[simp]
theorem selectedTranslatedParameter_box
    (n : ℕ) :
    (boundary.selectedTranslatedParameter D representative offset radius Fsys
      x w₀ hw₀ data n).2 =
      (x (boundary.selectedIndex D representative offset radius Fsys
        x w₀ hw₀ data n)).1.2 - w₀ :=
  rfl

/-- The translated bounded parameter remains in the translated closed box. -/
theorem selectedTranslatedParameter_box_mem
    (n : ℕ) :
    (boundary.selectedTranslatedParameter D representative offset radius Fsys
      x w₀ hw₀ data n).2 ∈ (D.translateToZero w₀).closedBox := by
  rw [D.mem_closedBox_translateToZero_iff]
  have hw := D.openBox_subset_closedBox (boundary.selected_regularZero n).1.2
  simpa [selectedTranslatedParameter, selectedIndex,
    restrictedSourceTranslateToZero, RestrictedBox.translateFromZero] using hw

/-- The original offset bound therefore gives the node-radius bound at every
selected translated parameter. -/
theorem selectedTranslatedOffset_bound
    (n : ℕ) (j : Fin boundary.S.card) :
    |(restrictedOffsetTranslateToZero w₀ offset
        (restrictedJetEnumeration boundary.S j).1 :
      RestrictedBoxSpace p → ℝ)
        (boundary.selectedTranslatedParameter D representative offset radius
          Fsys x w₀ hw₀ data n).2| ≤ boundary.B := by
  have hw := D.openBox_subset_closedBox (boundary.selected_regularZero n).1.2
  have h := boundary.offset_bound
    (x (boundary.selectedIndex D representative offset radius Fsys
      x w₀ hw₀ data n)).1.2 hw j
  simpa [selectedTranslatedParameter, selectedIndex,
    restrictedSourceTranslateToZero, restrictedOffsetTranslateToZero,
    RestrictedBox.translateCoefficientToZero,
    RestrictedBox.translateFromZero] using h

/-- The concrete full top-prefix assignment along the selected translated
boundary. -/
def selectedTopPrefixSequenceValue :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1)
          data.orderedClusterCount) → ℕ → ℝ :=
  fun z n ↦ RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
    (D.translateToZero w₀)
    representative (restrictedOffsetTranslateToZero w₀ offset) boundary.S
    boundary.B boundary.Fbranch
    (boundary.selectedTranslatedParameter D representative offset radius Fsys
      x w₀ hw₀ data n) data.orderedClusterCount z

/-- The common analytic extension in the boundary upgraded to the central
remainder data required by real-jet substitution. -/
structure CommonRealHermiteData where
  u0 : ℝ
  ε : ℝ
  Kr : ℝ
  fullHermite : FullHermiteLemmaSpec A boundary.B
    (paperRankHermiteNodeMultiplicity boundary.S)
    (boundary.Xstrip + boundary.B + 3) boundary.K boundary.K0 u0 ε Kr
    (fun _ ↦ boundary.Fbranch) boundary.Fbranch

/-- The central real-Hermite data exists for the same branch already stored
in the corrected top-prefix boundary. -/
theorem nonempty_commonRealHermiteData (hA : IsAbel A) :
    Nonempty (boundary.CommonRealHermiteData D representative offset radius
      Fsys x w₀ hw₀ data) := by
  obtain ⟨u0, ε, Kr, H⟩ :=
    hA.exists_fullHermiteLemmaSpec_of_commonStripFamily boundary.B_pos
      boundary.Xstrip_gt_one boundary.branch_analytic boundary.branch_real
      boundary.hermiteFamily
  exact ⟨⟨u0, ε, Kr, H⟩⟩

/-- A fixed choice of the common central real-Hermite data. -/
noncomputable def commonRealHermiteData (hA : IsAbel A) :
    boundary.CommonRealHermiteData D representative offset radius Fsys x w₀
      hw₀ data :=
  Classical.choice (boundary.nonempty_commonRealHermiteData D representative
    offset radius Fsys x w₀ hw₀ data hA)

/-- Abel times of one ordered cluster along the fixed balancing subsequence. -/
def selectedClusterRawTime
    (c : Fin data.orderedClusterCount) :
    ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ :=
  fun n ↦ data.orderedClusterRawTime
    (boundary.preprocessed.balancingSubsequence n) c

/-- Convert a literal member of an ordered cluster back to its balancing
coordinate. -/
def balancingIndexOfMem
    (c : Fin data.orderedClusterCount) (block : Fin m)
    (hblock : block ∈ data.orderedCluster c) :
    Fin (data.orderedClusterTailSize c + 1) :=
  (data.orderedClusterBalancingToActiveEquiv c).symm
    ((data.orderedCluster c).equivFin ⟨block, hblock⟩)

omit [Nonempty (Fin m)] in
@[simp]
theorem balancingIndexOfMem_enumeration
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    balancingIndexOfMem x data c (data.orderedClusterEnumeration c i)
        (data.orderedClusterEnumeration_mem c i) = i := by
  unfold balancingIndexOfMem
  apply (data.orderedClusterBalancingToActiveEquiv c).injective
  simp [RepresentativeClusterSubsequence.orderedClusterEnumeration,
    RepresentativeClusterSubsequence.orderedClusterBalancingToActiveEquiv]

/-- The concrete paper-rank parameter after the first `r` individual
decrements in cluster `c`.  Active-cluster centers are the exact inverse-Abel
boundary values; all smaller-cluster centers and the bounded coordinate are
copied from the selected top-prefix parameter. -/
def clusterPrefixParameter
    (c : Fin data.orderedClusterCount) (r n : ℕ) :
    PaperRankParameterSpace m p :=
  (fun block ↦ if hblock : block ∈ data.orderedCluster c then
      inverse A (clusterShiftedTimes
        (boundary.selectedClusterRawTime D representative offset radius Fsys
          x w₀ hw₀ data c n)
        ((boundary.preprocessed.fixedSteps c).take r)
        (balancingIndexOfMem x data c block hblock))
    else
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data n).1 block,
    (boundary.selectedTranslatedParameter D representative offset radius
      Fsys x w₀ hw₀ data n).2)

/-- Exact active-block lookup in the cluster-prefix parameter. -/
@[simp]
theorem clusterPrefixParameter_enumeration
    (c : Fin data.orderedClusterCount) (r n : ℕ)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    (boundary.clusterPrefixParameter D representative offset radius Fsys x
      w₀ hw₀ data c r n).1 (data.orderedClusterEnumeration c i) =
      inverse A (clusterShiftedTimes
        (boundary.selectedClusterRawTime D representative offset radius Fsys
          x w₀ hw₀ data c n)
        ((boundary.preprocessed.fixedSteps c).take r) i) := by
  simp [clusterPrefixParameter, data.orderedClusterEnumeration_mem c i]

@[simp]
theorem clusterPrefixParameter_box
    (c : Fin data.orderedClusterCount) (r n : ℕ) :
    (boundary.clusterPrefixParameter D representative offset radius Fsys x
      w₀ hw₀ data c r n).2 =
      (boundary.selectedTranslatedParameter D representative offset radius
      Fsys x w₀ hw₀ data n).2 :=
  rfl

/-! ## Fixed individual decrement jets -/

/-- The exact paper-rank parameter immediately before fixed individual
decrement `j`. -/
def individualPreLogParameter
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (n : ℕ) :
    PaperRankParameterSpace m p :=
  boundary.clusterPrefixParameter D representative offset radius Fsys x w₀
    hw₀ data c j.castSucc n

/-- The full concrete prefix assignment immediately before fixed individual
decrement `j`. -/
def individualPreLogPrefixSequenceValue
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) →
      ℕ → ℝ :=
  data.paperRankHermiteOrderedClusterPrefixSequenceValue
    c (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
    boundary.Fbranch
    (boundary.individualPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c j)

/-- The original representative block selected at individual step `j`. -/
def individualSelectedBlock
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) : Fin 1 → Fin m :=
  fun _ ↦ (data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j).1

/-- The post-log center used by the individual real-jet substitution. -/
def individualPostLogScale
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) : Fin 1 → ℕ → ℝ :=
  data.orderedClusterIndividualPostLogScale c A
    (boundary.selectedClusterRawTime D representative offset radius Fsys x w₀
      hw₀ data c) (boundary.preprocessed.fixedSteps c) j

/-- The selected pre-log center is exactly `E` of the corresponding
post-log center. -/
theorem individualPreLogParameter_selected_center
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (i : Fin 1) (n : ℕ) :
    (boundary.individualPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c j n).1
        (boundary.individualSelectedBlock D representative offset radius Fsys
          x w₀ hw₀ data c j i) =
      E (boundary.individualPostLogScale D representative offset radius Fsys
        x w₀ hw₀ data c j i n) := by
  change
    (boundary.clusterPrefixParameter D representative offset radius Fsys x
      w₀ hw₀ data c j.castSucc n).1
      (data.orderedClusterIndividualSelectedBlock c
        (boundary.preprocessed.fixedSteps c) j).1 = _
  rw [data.orderedClusterIndividualSelectedBlock_eq]
  simp only [data.orderedClusterBalancingPrefixBlock_val]
  rw [boundary.clusterPrefixParameter_enumeration D representative offset
    radius Fsys x w₀ hw₀ data]
  unfold individualPostLogScale
  rw [data.orderedClusterIndividualPostLogScale_apply]
  let t := clusterShiftedTimes
      (boundary.selectedClusterRawTime D representative offset radius Fsys x
        w₀ hw₀ data c n)
      ((boundary.preprocessed.fixedSteps c).take j.castSucc)
      ((boundary.preprocessed.fixedSteps c).get j)
  have hrec := hA.inverse_add_one (t - 1)
  have ht : t - 1 + 1 = t := by ring
  rw [ht] at hrec
  exact hrec

@[simp]
theorem individualPreLogParameter_box
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (n : ℕ) :
    (boundary.individualPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c j n).2 =
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data n).2 :=
  rfl

/-- Canonical real-Hermite substitution data for one fixed individual
decrement.  Passing to a tail is the only reason for the explicit threshold
hypothesis; all nodes and branches come directly from `boundary`. -/
def individualRealJetSequence
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j i n)
      (paperRankHermitePositiveDerivativeCount boundary.S) :=
  (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
    hw₀ data hA).fullHermite.paperRankRealJetSequence
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
      (boundary.individualSelectedBlock D representative offset radius Fsys x
        w₀ hw₀ data c j)
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j) hu
      (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
        radius Fsys x w₀ hw₀ data n).2)
      (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative
        offset radius Fsys x w₀ hw₀ data n k)

/-- Exact compatibility of every individual source-jet coordinate with the
concrete Hermite coefficient at its actual pre-log cluster boundary. -/
theorem individualRealJetSequence_sourceJet_eq_coefficientValue
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n)
    (n : ℕ) (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    (boundary.individualRealJetSequence D representative offset radius Fsys x
      w₀ hw₀ data hA c j hu n i).sourceJet r =
      paperRankHermiteCoefficientValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        boundary.B (fun _ ↦ boundary.Fbranch)
        (boundary.individualPreLogParameter D representative offset radius Fsys
          x w₀ hw₀ data c j n)
        (Sum.inr (boundary.individualSelectedBlock D representative offset
          radius Fsys x w₀ hw₀ data c j i))
        (paperRankHermitePositiveCoefficientIndex boundary.S
          (Sum.inr (boundary.individualSelectedBlock D representative offset
            radius Fsys x w₀ hw₀ data c j i)) r) := by
  unfold individualRealJetSequence
  apply FullHermiteLemmaSpec.paperRankRealJetSequence_sourceJet_eq_coefficientValue
  · intro q k
    exact boundary.individualPreLogParameter_selected_center D representative
      offset radius Fsys x w₀ hw₀ data hA c j k q
  · intro q
    exact boundary.individualPreLogParameter_box D representative offset radius
      Fsys x w₀ hw₀ data c j q

/-- The individual Hermite error decays faster than every power of the
chosen post-boundary cluster scale. -/
theorem individualRealJetSequence_error_superpolynomialDecay
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i : Fin 1, Tendsto
      (fun n ↦ boundary.individualPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c j i n / Real.log (R n)) atTop atTop)
    (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.individualRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j hu n i).error r) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  exact H.paperRankRealJetSequence_error_superpolynomialDecay
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
    (boundary.individualSelectedBlock D representative offset radius Fsys x
      w₀ hw₀ data c j)
    (boundary.individualPostLogScale D representative offset radius Fsys x
      w₀ hw₀ data c j) hu
    (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data n).2)
    (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative
      offset radius Fsys x w₀ hw₀ data n k)
    R hR hseparated i r

/-- The same individual error coordinate has a polynomial upper bound. -/
theorem individualRealJetSequence_error_hasPolynomialUpperBound
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i : Fin 1, Tendsto
      (fun n ↦ boundary.individualPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c j i n / Real.log (R n)) atTop atTop)
    (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    HasPolynomialUpperBound atTop R
      (fun n ↦ (boundary.individualRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j hu n i).error r) :=
  superpolynomialDecay_hasPolynomialUpperBound
    (boundary.individualRealJetSequence_error_superpolynomialDecay D
      representative offset radius Fsys x w₀ hw₀ data hA c j hu R hR
      hseparated i r)

/-- The standard balanced hierarchy supplies the separation hypotheses for
the individual Hermite error automatically. -/
theorem individualRealJetSequence_error_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n)
    (R : ℕ → ℝ)
    (hierarchy : BalancedRealJetTransferHierarchy 0
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j) R)
    (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.individualRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j hu n i).error r) := by
  apply boundary.individualRealJetSequence_error_superpolynomialDecay D
    representative offset radius Fsys x w₀ hw₀ data hA c j hu R
    hierarchy.scale_ge_two
  intro k
  exact tendsto_scaleCoordinate_div_log_atTop_of_strictAnti
    (boundary.individualPostLogScale D representative offset radius Fsys x w₀
      hw₀ data c j) R hierarchy.order hierarchy.scale_ge_two
      hierarchy.smallest_div_log_scale k

/-- Every normalized coordinate error of the individual transfer decays
superpolynomially; representative and time coordinates are exactly zero. -/
theorem individualTransferCoordinateError_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n)
    (R : ℕ → ℝ)
    (hierarchy : BalancedRealJetTransferHierarchy 0
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j) R)
    (z : Fin 1 ⊕ CentralPolynomialIndex (Fin 1)
      (fun _ ↦ paperRankHermitePositiveDerivativeCount boundary.S) (Fin 1)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ realCentralTransferCoordinateError
        (boundary.individualRealJetSequence D representative offset radius Fsys
          x w₀ hw₀ data hA c j hu n) z) := by
  apply realCentralTransferCoordinateError_superpolynomialDecay_of_errors
  intro i r
  exact boundary.individualRealJetSequence_error_superpolynomialDecay_of_hierarchy
    D representative offset radius Fsys x w₀ hw₀ data hA c j hu R hierarchy
      i r

/-- The pre-boundary domination record gives a polynomial upper bound for
every individual source-jet coordinate. -/
theorem individualRealJetSequence_sourceJet_hasPolynomialUpperBound_of_domination
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j i n)
    (R X : ℕ → ℝ)
    (domination : CrossClusterTransferScaleDomination 0
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j) R X)
    (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    HasPolynomialUpperBound atTop X
      (fun n ↦ (boundary.individualRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j hu n i).sourceJet r) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  apply H.paperRankRealJetSequence_sourceJet_hasPolynomialUpperBound
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
    (boundary.individualSelectedBlock D representative offset radius Fsys x w₀
      hw₀ data c j)
    (boundary.individualPostLogScale D representative offset radius Fsys x w₀
      hw₀ data c j) hu
    (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data n).2)
    (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative offset
      radius Fsys x w₀ hw₀ data n k) X
  · exact domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  · exact domination.exponential_le

/-! ## Fixed simultaneous decrement jets -/

/-- The original representative block occupying final active position `i`.
This is the block order used by the simultaneous algebraic certificate. -/
def simultaneousSelectedBlock
    (c : Fin data.orderedClusterCount) :
    Fin (data.orderedCluster c).card → Fin m :=
  fun i ↦ data.orderedClusterEnumeration c
    (boundary.preprocessed.fixedOrder c
      ((data.orderedClusterBalancingToActiveEquiv c).symm i))

/-- The actual paper-rank parameter immediately before simultaneous
operation `r`.  Each active block has undergone all individual decrements
and exactly `r` simultaneous decrements. -/
def simultaneousPreLogParameter
    (c : Fin data.orderedClusterCount) (r n : ℕ) :
    PaperRankParameterSpace m p :=
  (fun block ↦ if hblock : block ∈ data.orderedCluster c then
      inverse A
        (clusterShiftedTimes
          (boundary.selectedClusterRawTime D representative offset radius Fsys
            x w₀ hw₀ data c n)
          (boundary.preprocessed.fixedSteps c)
          (balancingIndexOfMem x data c block hblock) - (r : ℝ))
    else
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data n).1 block,
    (boundary.selectedTranslatedParameter D representative offset radius
      Fsys x w₀ hw₀ data n).2)

/-- The smaller-prefix assignment shared by the coefficient ring throughout
simultaneous operation `r`. -/
def simultaneousSmallerPrefixSequenceValue
    (c : Fin data.orderedClusterCount) (r : ℕ) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock c.val)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) c.val) → ℕ → ℝ :=
  RepresentativeClusterSubsequence.paperRankHermiteOrderedClusterSmallerPrefixSequenceValue data
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
    boundary.Fbranch
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r) c

/-- The corresponding fully concrete smaller-prefix coefficient hom over
real coefficients. -/
def simultaneousSmallerPrefixEvaluationHom
    (c : Fin data.orderedClusterCount) (r : ℕ) :
    data.OrderedClusterPrefixRing ℝ (paperRankHermiteHigherCount boundary.S)
      c.val →+* (ℕ → ℝ) :=
  RepresentativeClusterSubsequence.paperRankHermiteOrderedClusterSmallerPrefixEvaluationHom data
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
    boundary.Fbranch
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r) c

/-- The post-log centers of simultaneous operation `r`, in final active
order. -/
def simultaneousPostLogScale
    (c : Fin data.orderedClusterCount) (r : ℕ) :
    Fin (data.orderedCluster c).card → ℕ → ℝ :=
  data.orderedClusterSimultaneousPostLogScale c A
    (boundary.selectedClusterRawTime D representative offset radius Fsys x w₀
      hw₀ data c) (boundary.preprocessed.fixedSteps c)
    (boundary.preprocessed.fixedOrder c) r

/-- Exact lookup of an active final-position block in the simultaneous
pre-log parameter. -/
@[simp]
theorem simultaneousPreLogParameter_active
    (c : Fin data.orderedClusterCount) (r n : ℕ)
    (i : Fin (data.orderedCluster c).card) :
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r n).1
        (boundary.simultaneousSelectedBlock D representative offset radius Fsys
          x w₀ hw₀ data c i) =
      inverse A
        (data.orderedClusterPostBalancingFinalOrderTime c
          (boundary.selectedClusterRawTime D representative offset radius Fsys
            x w₀ hw₀ data c)
          (boundary.preprocessed.fixedSteps c)
          (boundary.preprocessed.fixedOrder c) i n - (r : ℝ)) := by
  unfold simultaneousSelectedBlock
  simp only [simultaneousPreLogParameter,
    data.orderedClusterEnumeration_mem, dite_true]
  rw [balancingIndexOfMem_enumeration]
  rfl

/-- Every simultaneous pre-log center is `E` of its post-log center. -/
theorem simultaneousPreLogParameter_center
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (r : ℕ)
    (n : ℕ) (i : Fin (data.orderedCluster c).card) :
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r n).1
        (boundary.simultaneousSelectedBlock D representative offset radius Fsys
          x w₀ hw₀ data c i) =
      E (boundary.simultaneousPostLogScale D representative offset radius Fsys
        x w₀ hw₀ data c r i n) := by
  rw [boundary.simultaneousPreLogParameter_active D representative offset
    radius Fsys x w₀ hw₀ data]
  unfold simultaneousPostLogScale
  change inverse A
      (data.orderedClusterPostBalancingFinalOrderTime c
        (boundary.selectedClusterRawTime D representative offset radius Fsys x
          w₀ hw₀ data c)
        (boundary.preprocessed.fixedSteps c)
        (boundary.preprocessed.fixedOrder c) i n - (r : ℝ)) =
    E (inverse A
      (data.orderedClusterPostBalancingFinalOrderTime c
        (boundary.selectedClusterRawTime D representative offset radius Fsys x
          w₀ hw₀ data c)
        (boundary.preprocessed.fixedSteps c)
        (boundary.preprocessed.fixedOrder c) i n - ((r + 1 : ℕ) : ℝ)))
  let t := data.orderedClusterPostBalancingFinalOrderTime c
      (boundary.selectedClusterRawTime D representative offset radius Fsys x
        w₀ hw₀ data c)
      (boundary.preprocessed.fixedSteps c)
      (boundary.preprocessed.fixedOrder c) i n - (r : ℝ)
  have harg :
      data.orderedClusterPostBalancingFinalOrderTime c
      (boundary.selectedClusterRawTime D representative offset radius Fsys x
        w₀ hw₀ data c)
      (boundary.preprocessed.fixedSteps c)
      (boundary.preprocessed.fixedOrder c) i n - ((r + 1 : ℕ) : ℝ) = t - 1 := by
    dsimp only [t]
    push_cast
    ring
  rw [harg]
  change inverse A t = E (inverse A (t - 1))
  have hrec := hA.inverse_add_one (t - 1)
  have ht : t - 1 + 1 = t := by ring
  rw [ht] at hrec
  exact hrec

@[simp]
theorem simultaneousPreLogParameter_box
    (c : Fin data.orderedClusterCount) (r n : ℕ) :
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r n).2 =
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data n).2 :=
  rfl

/-- Canonical real-Hermite substitution data for every active block of
simultaneous operation `r`. -/
def simultaneousRealJetSequence
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c r i n) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c r i n)
      (paperRankHermitePositiveDerivativeCount boundary.S) :=
  (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
    hw₀ data hA).fullHermite.paperRankRealJetSequence
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
      (boundary.simultaneousSelectedBlock D representative offset radius Fsys x
        w₀ hw₀ data c)
      (boundary.simultaneousPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c r) hu
      (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
        radius Fsys x w₀ hw₀ data n).2)
      (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative
        offset radius Fsys x w₀ hw₀ data n k)

/-- Exact compatibility of every simultaneous source jet with the concrete
Hermite coefficient at that operation's actual pre-log boundary. -/
theorem simultaneousRealJetSequence_sourceJet_eq_coefficientValue
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (op : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c op i n)
    (n : ℕ) (i : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    (boundary.simultaneousRealJetSequence D representative offset radius Fsys x
      w₀ hw₀ data hA c op hu n i).sourceJet r =
      paperRankHermiteCoefficientValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        boundary.B (fun _ ↦ boundary.Fbranch)
        (boundary.simultaneousPreLogParameter D representative offset radius
          Fsys x w₀ hw₀ data c op n)
        (Sum.inr (boundary.simultaneousSelectedBlock D representative offset
          radius Fsys x w₀ hw₀ data c i))
        (paperRankHermitePositiveCoefficientIndex boundary.S
          (Sum.inr (boundary.simultaneousSelectedBlock D representative offset
            radius Fsys x w₀ hw₀ data c i)) r) := by
  unfold simultaneousRealJetSequence
  apply FullHermiteLemmaSpec.paperRankRealJetSequence_sourceJet_eq_coefficientValue
  · intro q k
    exact boundary.simultaneousPreLogParameter_center D representative offset
      radius Fsys x w₀ hw₀ data hA c op q k
  · intro q
    exact boundary.simultaneousPreLogParameter_box D representative offset
      radius Fsys x w₀ hw₀ data c op q

/-- Coordinatewise simultaneous Hermite errors have superpolynomial decay
under the scale separation delivered by the cluster hierarchy. -/
theorem simultaneousRealJetSequence_error_superpolynomialDecay
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (op : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c op i n)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i, Tendsto
      (fun n ↦ boundary.simultaneousPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c op i n / Real.log (R n)) atTop atTop)
    (i : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.simultaneousRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c op hu n i).error r) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  exact H.paperRankRealJetSequence_error_superpolynomialDecay
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
    (boundary.simultaneousSelectedBlock D representative offset radius Fsys x
      w₀ hw₀ data c)
    (boundary.simultaneousPostLogScale D representative offset radius Fsys x
      w₀ hw₀ data c op) hu
    (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data n).2)
    (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative
      offset radius Fsys x w₀ hw₀ data n k)
    R hR hseparated i r

/-- The same simultaneous error coordinate has a polynomial upper bound. -/
theorem simultaneousRealJetSequence_error_hasPolynomialUpperBound
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (op : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c op i n)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hseparated : ∀ i, Tendsto
      (fun n ↦ boundary.simultaneousPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c op i n / Real.log (R n)) atTop atTop)
    (i : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    HasPolynomialUpperBound atTop R
      (fun n ↦ (boundary.simultaneousRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c op hu n i).error r) :=
  superpolynomialDecay_hasPolynomialUpperBound
    (boundary.simultaneousRealJetSequence_error_superpolynomialDecay D
      representative offset radius Fsys x w₀ hw₀ data hA c op hu R hR
      hseparated i r)

/-- A successor-cardinality balanced hierarchy supplies all simultaneous
coordinate separation hypotheses after transport to the literal cluster
cardinality. -/
theorem simultaneousRealJetSequence_error_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (op : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c op i n)
    (R : ℕ → ℝ) {tail : ℕ}
    (card_eq : tail + 1 = (data.orderedCluster c).card)
    (hierarchy : BalancedRealJetTransferHierarchy tail
      (fun i n ↦ boundary.simultaneousPostLogScale D representative offset
        radius Fsys x w₀ hw₀ data c op (finCongr card_eq i) n) R)
    (i : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.simultaneousRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c op hu n i).error r) := by
  apply boundary.simultaneousRealJetSequence_error_superpolynomialDecay D
    representative offset radius Fsys x w₀ hw₀ data hA c op hu R
    hierarchy.scale_ge_two
  intro k
  let k' : Fin (tail + 1) := (finCongr card_eq).symm k
  have hk := tendsto_scaleCoordinate_div_log_atTop_of_strictAnti
    (fun q n ↦ boundary.simultaneousPostLogScale D representative offset radius
      Fsys x w₀ hw₀ data c op (finCongr card_eq q) n)
    R hierarchy.order hierarchy.scale_ge_two
      hierarchy.smallest_div_log_scale k'
  simpa only [k', Equiv.apply_symm_apply] using hk

/-- Every normalized coordinate error of the simultaneous transfer decays
superpolynomially after transporting the successor-cardinality hierarchy. -/
theorem simultaneousTransferCoordinateError_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (op : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c op i n)
    (R : ℕ → ℝ) {tail : ℕ}
    (card_eq : tail + 1 = (data.orderedCluster c).card)
    (hierarchy : BalancedRealJetTransferHierarchy tail
      (fun i n ↦ boundary.simultaneousPostLogScale D representative offset
        radius Fsys x w₀ hw₀ data c op (finCongr card_eq i) n) R)
    (z : Fin (data.orderedCluster c).card ⊕
      CentralPolynomialIndex (Fin (data.orderedCluster c).card)
        (fun _ ↦ paperRankHermitePositiveDerivativeCount boundary.S)
        (Fin (data.orderedCluster c).card)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ realCentralTransferCoordinateError
        (boundary.simultaneousRealJetSequence D representative offset radius
          Fsys x w₀ hw₀ data hA c op hu n) z) := by
  apply realCentralTransferCoordinateError_superpolynomialDecay_of_errors
  intro i r
  exact boundary.simultaneousRealJetSequence_error_superpolynomialDecay_of_hierarchy
    D representative offset radius Fsys x w₀ hw₀ data hA c op hu R card_eq
      hierarchy i r

/-- The transported simultaneous domination hierarchy gives a polynomial
upper bound for every source-jet coordinate at the pre-operation scale. -/
theorem simultaneousRealJetSequence_sourceJet_hasPolynomialUpperBound_of_domination
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (op : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c op i n)
    (R X : ℕ → ℝ) {tail : ℕ}
    (card_eq : tail + 1 = (data.orderedCluster c).card)
    (domination : CrossClusterTransferScaleDomination tail
      (fun i n ↦ boundary.simultaneousPostLogScale D representative offset
        radius Fsys x w₀ hw₀ data c op (finCongr card_eq i) n) R X)
    (i : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    HasPolynomialUpperBound atTop X
      (fun n ↦ (boundary.simultaneousRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c op hu n i).sourceJet r) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  apply H.paperRankRealJetSequence_sourceJet_hasPolynomialUpperBound
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
    (boundary.simultaneousSelectedBlock D representative offset radius Fsys x
      w₀ hw₀ data c)
    (boundary.simultaneousPostLogScale D representative offset radius Fsys x
      w₀ hw₀ data c op) hu
    (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data n).2)
    (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative offset
      radius Fsys x w₀ hw₀ data n k) X
  · exact domination.target_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  · filter_upwards [domination.exponential_le] with n hn
    intro k
    let k' : Fin (tail + 1) := (finCongr card_eq).symm k
    simpa only [k', Equiv.apply_symm_apply] using hn k'

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

end AbelFormalization
