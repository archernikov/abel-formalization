import AbelFormalization.HermiteBeforeRankPolynomialSubstitution
import AbelFormalization.CommonStripHermiteRealAnalytic
import AbelFormalization.RestrictedHermiteJetBlockification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open Set
open scoped Topology ContDiff

variable {ι : Type*}

/-- The retained `s` and complete Hermite coefficient assignment in the flat
coordinate order used by rank elimination. -/
def paperRankFullHermiteRetainedValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) :
    PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → ℝ :=
  fun z =>
    paperRankHermiteCoefficientBlockValue D representative offset S
      (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
      B (fun _ => F) sw
      (paperRankRetainedFlatHermiteEquiv m
        (paperRankHermitePositiveDerivativeCount S) z)

/-- The smooth-coordinate part of the complete Hermite assignment. -/
def paperRankFullHermiteSmoothValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ) :
    PaperRankParameterSpace m p →
      PaperRankRealSpace
        (m * (paperRankHermitePositiveDerivativeCount S + 1)) :=
  fun sw j => paperRankFullHermiteRetainedValue D representative offset S B F sw
    (Sum.inr j)

@[simp] theorem paperRankFullHermiteRetainedValue_free
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (i : Fin m) :
    paperRankFullHermiteRetainedValue D representative offset S B F sw
      (Sum.inl i) = sw.1 i := by
  rfl

@[simp] theorem paperRankRetainedArgument_fullHermiteSmoothValue
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (B : ℝ) (F : ℂ → ℂ)
    (x : PaperRankSource m p a) :
    paperRankRetainedArgument
      (paperRankFullHermiteSmoothValue D representative offset S B F) x =
      paperRankFullHermiteRetainedValue D representative offset S B F x.1 := by
  funext z
  rcases z with i | j <;> rfl

private theorem eval₂Hom_isEmptyAlgEquiv
    {R T σ : Type*} [CommSemiring R] [CommSemiring T] [IsEmpty σ]
    (c : R →+* T) (value : σ → T) (P : MvPolynomial σ R) :
    c (MvPolynomial.isEmptyAlgEquiv R σ P) =
      MvPolynomial.eval₂Hom c value P := by
  let lhs : MvPolynomial σ R →+* T :=
    c.comp (MvPolynomial.isEmptyAlgEquiv R σ).toRingHom
  let rhs : MvPolynomial σ R →+* T := MvPolynomial.eval₂Hom c value
  change lhs P = rhs P
  apply DFunLike.congr_fun _ P
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs]
  · intro z
    exact isEmptyElim z

/-- The retained Hermite-before-rank substitution evaluates to the original
selected Abel jets. -/
theorem eval₂Hom_hermiteBeforeRankRetainedHom_fullHermiteValue
    {A : ℝ → ℝ} {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X K K0 : ℝ} {F : ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X K K0 (fun _ => F))
    (hB : 0 < B) (sw : PaperRankParameterSpace m p)
    (hs : ∀ i, X < sw.1 i)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) sw.2| ≤ B)
    (P : MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra sw.2)
        (paperRankFullHermiteRetainedValue D representative offset S B F sw)
        (hermiteBeforeRankRetainedHom
          D.analyticNearClosedBoxSubalgebra
          (paperRankHermiteJetPolynomial D representative offset S
            (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)) P) =
      MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra sw.2)
        (Sum.elim sw.1
          (restrictedSelectedAbelJets A representative offset
            (restrictedJetEnumeration S) sw)) P := by
  let c := subalgebraPointEval D.analyticNearClosedBoxSubalgebra sw.2
  let coeffValue := paperRankHermiteCoefficientBlockValue D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m) B (fun _ => F) sw
  have hold := eval₂Hom_paperRankHermiteClusterCurryHom
    D representative offset S (Fin 0) (Fin m)
    (paperRankAllCoefficientBlockEquiv m) H hB sw hs hoffset P
  let activeValue := paperRankHermiteActiveValue D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m) B (fun _ => F) sw
  let jetPolynomial := paperRankHermiteJetPolynomial D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
  let curried := paperRankClusterCurryHom
    D.analyticNearClosedBoxSubalgebra (Fin 0) (Fin m)
    (paperRankHermiteBlockDerivativeCount S (Fin 0))
    (paperRankHermiteBlockDerivativeCount S (Fin m))
    (paperRankAllCoefficientBlockEquiv m) jetPolynomial P
  have hvalue :
      (paperRankFullHermiteRetainedValue D representative offset S B F sw) ∘
        (paperRankRetainedFlatHermiteEquiv m
          (paperRankHermitePositiveDerivativeCount S)).symm = coeffValue := by
    funext z
    dsimp [paperRankFullHermiteRetainedValue, coeffValue, Function.comp_def]
    rw [Equiv.apply_symm_apply]
  calc
    MvPolynomial.eval₂Hom c
        (paperRankFullHermiteRetainedValue D representative offset S B F sw)
        (hermiteBeforeRankRetainedHom
          D.analyticNearClosedBoxSubalgebra jetPolynomial P) =
      MvPolynomial.eval₂Hom c coeffValue
        (paperRankAllCoefficientCurryHom
          D.analyticNearClosedBoxSubalgebra jetPolynomial P) := by
            rw [show hermiteBeforeRankRetainedHom
                D.analyticNearClosedBoxSubalgebra jetPolynomial P =
              (paperRankRetainedFlatHermiteAlgEquiv
                D.analyticNearClosedBoxSubalgebra m
                (paperRankHermitePositiveDerivativeCount S)).symm
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P) by rfl]
            rw [show (paperRankRetainedFlatHermiteAlgEquiv
                D.analyticNearClosedBoxSubalgebra m
                (paperRankHermitePositiveDerivativeCount S)).symm
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P) =
              MvPolynomial.rename
                (paperRankRetainedFlatHermiteEquiv m
                  (paperRankHermitePositiveDerivativeCount S)).symm
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P) by rfl]
            change MvPolynomial.eval₂ c
                (paperRankFullHermiteRetainedValue
                  D representative offset S B F sw)
                (MvPolynomial.rename
                  (paperRankRetainedFlatHermiteEquiv m
                    (paperRankHermitePositiveDerivativeCount S)).symm
                  (paperRankAllCoefficientCurryHom
                    D.analyticNearClosedBoxSubalgebra jetPolynomial P)) =
              MvPolynomial.eval₂ c coeffValue
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P)
            rw [MvPolynomial.eval₂_rename]
            rw [hvalue]
    _ = MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom c coeffValue) activeValue curried := by
          exact eval₂Hom_isEmptyAlgEquiv
            (MvPolynomial.eval₂Hom c coeffValue) activeValue curried
    _ = _ := by
      simpa [c, coeffValue, activeValue, jetPolynomial, curried] using hold.symm

/-! ## Analyticity of the complete Hermite assignment -/

theorem analyticAt_paperRankFullHermiteCoefficientBlockValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X : ℝ} {F : ℂ → ℂ}
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
  · let center : PaperRankParameterSpace m p → ℝ := fun sw => sw.1 block
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
  · let center : PaperRankParameterSpace m p → ℝ := fun sw => sw.1 block
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
  · let center : PaperRankParameterSpace m p → ℝ := fun sw => sw.1 block
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

theorem paperRankFullHermiteSmoothValue_contDiffOn
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X : ℝ} {F : ℂ → ℂ}
    (hB : 0 < B)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)))
    (hoffset : ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B)
    (Ω : Set (PaperRankSource m p a))
    (hΩ : IsOpen Ω)
    (hΩbox : ∀ x ∈ Ω, x.1.2 ∈ D.closedBox)
    (hΩcenter : ∀ x ∈ Ω, ∀ i, X + B + 3 < x.1.1 i) :
    ContDiffOn ℝ ∞
      (paperRankFullHermiteSmoothValue D representative offset S B F)
      (Prod.fst '' Ω) := by
  rw [contDiffOn_pi]
  intro j
  have hanalytic : AnalyticOnNhd ℝ
      (fun sw => paperRankFullHermiteSmoothValue D representative offset S B F sw j)
      (Prod.fst '' Ω) := by
    rintro _ ⟨x, hx, rfl⟩
    have hswbox : x.1.2 ∈ D.closedBox := hΩbox x hx
    have hswcenter : ∀ i, X + B + 3 < x.1.1 i := hΩcenter x hx
    have hret := analyticAt_paperRankFullHermiteCoefficientBlockValue
      D representative offset S hB hF x.1 hswcenter hswbox
      (fun k => hoffset x.1.2 hswbox k)
      (paperRankRetainedFlatHermiteEquiv m
        (paperRankHermitePositiveDerivativeCount S) (Sum.inr j))
    change AnalyticAt ℝ
      (fun sw => paperRankFullHermiteRetainedValue D representative offset S B F sw
        (Sum.inr j)) x.1
    exact hret
  exact hanalytic.contDiffOn_of_completeSpace

end AbelFormalization
