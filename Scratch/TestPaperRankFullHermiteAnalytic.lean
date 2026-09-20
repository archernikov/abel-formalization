import AbelFormalization.PaperRankFullHermiteValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open _root_.Set
open scoped Topology

variable {ι : Type*}

theorem test_analyticAt_fullHermiteCoefficientBlockValue
    {A : ℝ → ℝ} {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X K K0 : ℝ} {F : ℂ → ℂ}
    (hB : 0 < B)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)))
    (sw : PaperRankParameterSpace m p)
    (hs : ∀ i, X + B + 3 < sw.1 i)
    (hw : sw.2 ∈ D.closedBox)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) sw.2| ≤ B)
    (z : ClusterOperationSymbol (Fin m)
      (fun _ => paperRankHermitePositiveDerivativeCount S)) :
    AnalyticAt ℝ
      (fun sw => paperRankHermiteCoefficientBlockValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m) B (fun _ => F) sw z)
      sw := by
  rcases z with block | (⟨block, r⟩ | block)
  · -- time variable (the outer block summand)
    let center : PaperRankParameterSpace m p → ℝ := fun sw => sw.1 block
    let nodes : PaperRankParameterSpace m p → Option (Fin S.card) → ℝ :=
      fun sw => paperRankHermiteNodes D representative offset S block sw.2
    have hcenter : AnalyticAt ℝ center sw := by
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) block).analyticAt
        sw.1).comp analyticAt_fst
    have hnodes : AnalyticAt ℝ nodes sw := by
      apply AnalyticAt.pi
      intro i
      rcases i with _ | j
      · exact analyticAt_const
      · by_cases h : representative (restrictedJetEnumeration S j).1 = block
        · simp [nodes, paperRankHermiteNodes, h]
          exact ((D.analyticNearClosedBox_iff.mp
            (offset (restrictedJetEnumeration S j).1).property sw.2 hw).comp
            analyticAt_snd)
        · simp [nodes, paperRankHermiteNodes, h]
          exact analyticAt_const
    have hxcenter : (center sw : ℂ) ∈ rightHalfStrip (X + B + 1) 1 := by
      dsimp [center]
      change X + B + 1 < sw.1 block ∧ |(0 : ℝ)| < 1
      constructor
      · linarith [hs block]
      · norm_num
    have hxnodes : (fun i => (nodes sw i : ℂ)) ∈ hermiteNodeNeighborhood B := by
      apply closed_nodes_subset_hermiteNodeNeighborhood B
      intro i
      rcases i with _ | j
      · simpa [nodes, paperRankHermiteNodes] using hB.le
      · by_cases h : representative (restrictedJetEnumeration S j).1 = block
        · simp only [nodes, paperRankHermiteNodes, Complex.norm_real,
            Real.norm_eq_abs]
          rw [if_pos h]
          exact hoffset j
        · simp [nodes, paperRankHermiteNodes, h, hB.le]
    have hcoeff := normalizedHermiteCoeff_re_analyticAt_commonStrip_real
      (E := PaperRankParameterSpace m p)
      (ι := Option (Fin S.card)) hB hF
      (paperRankHermiteNodeMultiplicity S) (r := 0)
      (by exact paperRankHermiteCoefficientCount_pos S)
      center nodes (x := sw) hcenter hnodes hxcenter hxnodes
    change AnalyticAt ℝ (fun sw => sw.1 block) sw
    exact hcenter
  · -- positive derivative coordinate
    let center : PaperRankParameterSpace m p → ℝ := fun sw => sw.1 block
    let nodes : PaperRankParameterSpace m p → Option (Fin S.card) → ℝ :=
      fun sw => paperRankHermiteNodes D representative offset S block sw.2
    have hcenter : AnalyticAt ℝ center sw := by
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) block).analyticAt
        sw.1).comp analyticAt_fst
    have hnodes : AnalyticAt ℝ nodes sw := by
      apply AnalyticAt.pi
      intro i
      rcases i with _ | j
      · exact analyticAt_const
      · by_cases h : representative (restrictedJetEnumeration S j).1 = block
        · simp [nodes, paperRankHermiteNodes, h]
          exact ((D.analyticNearClosedBox_iff.mp
            (offset (restrictedJetEnumeration S j).1).property sw.2 hw).comp
            analyticAt_snd)
        · simp [nodes, paperRankHermiteNodes, h]
          exact analyticAt_const
    have hxcenter : (center sw : ℂ) ∈ rightHalfStrip (X + B + 1) 1 := by
      dsimp [center]
      change X + B + 1 < sw.1 block ∧ |(0 : ℝ)| < 1
      constructor
      · linarith [hs block]
      · norm_num
    have hxnodes : (fun i => (nodes sw i : ℂ)) ∈ hermiteNodeNeighborhood B := by
      apply closed_nodes_subset_hermiteNodeNeighborhood B
      intro i
      rcases i with _ | j
      · simpa [nodes, paperRankHermiteNodes] using hB.le
      · by_cases h : representative (restrictedJetEnumeration S j).1 = block
        · simp only [nodes, paperRankHermiteNodes, Complex.norm_real,
            Real.norm_eq_abs]
          rw [if_pos h]
          exact hoffset j
        · simp [nodes, paperRankHermiteNodes, h, hB.le]
    have hcoeff := normalizedHermiteCoeff_re_analyticAt_commonStrip_real
      (E := PaperRankParameterSpace m p)
      (ι := Option (Fin S.card)) hB hF
      (paperRankHermiteNodeMultiplicity S) (r := r.val + 1)
      (by
        change r.val + 1 < paperRankHermiteCoefficientCount S
        rw [← paperRankHermitePositiveDerivativeCount_add_one]
        exact Nat.succ_lt_succ r.isLt)
      center nodes (x := sw) hcenter hnodes hxcenter hxnodes
    change AnalyticAt ℝ (fun y =>
      (normalizedCoeff
        (hermiteContourPolynomial
          (fun z => F ((center y : ℂ) + z))
          (nodePolynomial (fun i => (nodes y i : ℂ))
            (paperRankHermiteNodeMultiplicity S)) (B + 1))
        (r.val + 1)).re) sw
    exact hcoeff
  · -- zeroth Hermite coefficient coordinate
    let center : PaperRankParameterSpace m p → ℝ := fun sw => sw.1 block
    let nodes : PaperRankParameterSpace m p → Option (Fin S.card) → ℝ :=
      fun sw => paperRankHermiteNodes D representative offset S block sw.2
    have hcenter : AnalyticAt ℝ center sw := by
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) block).analyticAt
        sw.1).comp analyticAt_fst
    have hnodes : AnalyticAt ℝ nodes sw := by
      apply AnalyticAt.pi
      intro i
      rcases i with _ | j
      · exact analyticAt_const
      · by_cases h : representative (restrictedJetEnumeration S j).1 = block
        · simp [nodes, paperRankHermiteNodes, h]
          exact ((D.analyticNearClosedBox_iff.mp
            (offset (restrictedJetEnumeration S j).1).property sw.2 hw).comp
            analyticAt_snd)
        · simp [nodes, paperRankHermiteNodes, h]
          exact analyticAt_const
    have hxcenter : (center sw : ℂ) ∈ rightHalfStrip (X + B + 1) 1 := by
      dsimp [center]
      change X + B + 1 < sw.1 block ∧ |(0 : ℝ)| < 1
      constructor
      · linarith [hs block]
      · norm_num
    have hxnodes : (fun i => (nodes sw i : ℂ)) ∈ hermiteNodeNeighborhood B := by
      apply closed_nodes_subset_hermiteNodeNeighborhood B
      intro i
      rcases i with _ | j
      · simpa [nodes, paperRankHermiteNodes] using hB.le
      · by_cases h : representative (restrictedJetEnumeration S j).1 = block
        · simp only [nodes, paperRankHermiteNodes, Complex.norm_real,
            Real.norm_eq_abs]
          rw [if_pos h]
          exact hoffset j
        · simp [nodes, paperRankHermiteNodes, h, hB.le]
    have hcoeff := normalizedHermiteCoeff_re_analyticAt_commonStrip_real
      (E := PaperRankParameterSpace m p)
      (ι := Option (Fin S.card)) hB hF
      (paperRankHermiteNodeMultiplicity S) (r := 0)
      (by exact paperRankHermiteCoefficientCount_pos S)
      center nodes (x := sw) hcenter hnodes hxcenter hxnodes
    change AnalyticAt ℝ (fun y =>
      (normalizedCoeff
        (hermiteContourPolynomial
          (fun z => F ((center y : ℂ) + z))
          (nodePolynomial (fun i => (nodes y i : ℂ))
            (paperRankHermiteNodeMultiplicity S)) (B + 1)) 0).re) sw
    exact hcoeff

end AbelFormalization
