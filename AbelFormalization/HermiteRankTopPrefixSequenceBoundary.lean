import AbelFormalization.HermiteBeforeRankSequenceTranslation
import AbelFormalization.HermiteRankTopPrefixEvaluation
import AbelFormalization.SeparatedFiniteRealJetTrace

/-!
# Full-Hermite sequence boundary and ordered-cluster descent

This module joins the arbitrary-limit Hermite-before-rank theorem to the
full ordered-cluster prefix.  Starting only from a finite restricted-base
system over an Abel function and an all-unbounded regular-zero sequence, it
chooses the finite polynomial compression, the common Hermite family, the
rank ideal and its analytic representatives.  It then transports those same
generators and evaluations through the top-prefix variable equivalence and
continues the mapped ideal to the bottom-cluster time-polynomial extraction.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Set
open scoped Topology Polynomial

namespace AbelFormalization

variable {ι : Type*}

namespace RepresentativeClusterSubsequence

/-- Add a leading zero to the mapped full-Hermite top-prefix generators.
The resulting family is indexed by the nonempty type `Fin (c + 1)`. -/
def paperRankHermiteTopPrefixPaddedGenerator
    {m p c : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (g : Fin c → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)) :
    Fin (c + 1) →
      data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount S) data.orderedClusterCount :=
  Fin.cons 0 (fun j =>
    data.paperRankHermiteTopPrefixAlgEquiv (RealAnalyticGerm p) S (g j))

/-- Add a leading zero to the corresponding pointwise top-prefix polynomial
representatives. -/
def paperRankHermiteTopPrefixPaddedRepresentative
    {m p c : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (G : Fin c → RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ) :
    Fin (c + 1) → RestrictedBoxSpace p →
      data.OrderedClusterPrefixRing ℝ
        (paperRankHermiteHigherCount S) data.orderedClusterCount :=
  Fin.cons (fun _ => 0) (fun j =>
    paperRankHermiteTopPrefixRepresentative data S (G j))

/-- Padding the mapped top-prefix family preserves its mapped span, its
analytic-germ representatives, and its eventual vanishing under transported
assignments. -/
theorem paperRankHermiteTopPrefixPaddedFamily_spec
    {m p c : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)))
    (g : Fin c → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))
    (G : Fin c → RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ)
    (v : ℕ → PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → ℝ)
    (w : ℕ → RestrictedBoxSpace p)
    (hspan : Ideal.span (Set.range g) = I)
    (hG : ∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
      (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial
          (PaperRankRetainedSymbols m
            (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ)))
    (hvanish : ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval (v n) (G j (w n)) = 0) :
    Ideal.span (Set.range
        (paperRankHermiteTopPrefixPaddedGenerator data S g)) =
      data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I ∧
    (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (paperRankHermiteTopPrefixPaddedGenerator data S g j) =
      (paperRankHermiteTopPrefixPaddedRepresentative data S G j :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (data.OrderedClusterPrefixRing ℝ
            (paperRankHermiteHigherCount S) data.orderedClusterCount))) ∧
    ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval
        (paperRankHermiteTopPrefixAssignment data S (v n))
        (paperRankHermiteTopPrefixPaddedRepresentative data S G j (w n)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [paperRankHermiteTopPrefixPaddedGenerator,
      Ideal.span_range_finCons_zero]
    calc
      Ideal.span (Set.range (fun j =>
          data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) S (g j))) =
          data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S
            (Ideal.span (Set.range g)) :=
        span_paperRankHermiteTopPrefixAlgEquiv_range
          (RealAnalyticGerm p) data S g
      _ = data.paperRankHermiteTopPrefixIdeal
          (RealAnalyticGerm p) S I := by rw [hspan]
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact analyticPolynomialGermHom_paperRankHermiteTopPrefixAlgEquiv_of
        data S (g k) (G k) (hG k)
  · filter_upwards [hvanish] with n hn
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [paperRankHermiteTopPrefixPaddedRepresentative]
    · change MvPolynomial.eval
          (paperRankHermiteTopPrefixAssignment data S (v n))
          (paperRankHermiteTopPrefixRepresentative data S (G k) (w n)) = 0
      rw [paperRankHermiteTopPrefixRepresentative_apply,
        eval_paperRankHermiteTopPrefixAlgEquiv]
      exact hn k

end RepresentativeClusterSubsequence

/-- A finite restricted-base system along an all-unbounded regular-zero
sequence has one common full-Hermite rank package compatible with the entire
ordered-cluster descent.  The bounded coordinates are normalized at their
arbitrary limit `w₀`.  The original rank representatives and their renamed
top-prefix representatives have exactly the same evaluations, so eventual
vanishing is retained after reindexing.  Nonemptiness of `Fin m` supplies the
bottom cluster internally. -/
theorem IsAbel.exists_restrictedBaseHermiteRankTopPrefixSequenceBoundary
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} [Nonempty (Fin m)]
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (R : ℝ)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hxrepresentative : ∀ i,
      Tendsto (fun n => (x n).1.1 i) atTop atTop)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n => (x n).1.2) atTop (𝓝 w₀))
    (data : RepresentativeClusterSubsequence
      (fun n i => A ((x n).1.1 i))) :
    let D₀ : RestrictedBox p := D.translateToZero w₀
    let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
      D.zero_mem_closedBox_translateToZero hw₀
    let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
      restrictedOffsetTranslateToZero w₀ offset
    let x₀ : ℕ → RestrictedSource m p a :=
      fun n => restrictedSourceTranslateToZero w₀ (x n)
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          D.analyticNearClosedBoxSubalgebra,
    ∃ B Xstrip K K0 : ℝ,
    ∃ Fbranch : ℂ → ℂ,
    ∃ I : Ideal (MvPolynomial
        (PaperRankRetainedSymbols m
          (m * (paperRankHermitePositiveDerivativeCount S + 1)))
        (RealAnalyticGerm p)),
    ∃ c : ℕ,
    ∃ g : Fin c → MvPolynomial
        (PaperRankRetainedSymbols m
          (m * (paperRankHermitePositiveDerivativeCount S + 1)))
        (RealAnalyticGerm p),
    ∃ G : Fin c → RestrictedBoxSpace p → MvPolynomial
        (PaperRankRetainedSymbols m
          (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ,
    ∃ W : Set (RestrictedBoxSpace p),
    ∃ nextIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 1),
    ∃ _tail : RepresentativeClusterSubsequence.OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data (paperRankHermiteHigherCount S)
        (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
        1 data.orderedClusterCount_pos_of_nonempty nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 0)
        (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
        (fun _ => paperRankHermiteHigherCount S)
        (data.orderedClusterPrefixCurriedIdeal
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩ nextIdeal),
    ∃ i : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
    ∃ P : ℝ[X],
      (∀ r, restrictedPaperPolynomialValue A D representative offset
        (restrictedJetEnumeration S) (Q r) = F r) ∧
      0 < B ∧
      1 < Xstrip ∧
      AnalyticOnNhd ℂ Fbranch (rightHalfStrip Xstrip (B + 2)) ∧
      (∀ t : ℝ, Xstrip < t → Fbranch (t : ℂ) = (A t : ℂ)) ∧
      AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
        (Xstrip + B + 3) K K0 (fun _ => Fbranch) ∧
      (∀ w ∈ D.closedBox, ∀ j : Fin S.card,
        |(offset (restrictedJetEnumeration S j).1 :
          RestrictedBoxSpace p → ℝ) w| ≤ B) ∧
      I = jacobianEliminationIdeal a
        (fun r => restrictedPaperGermPolynomial D₀ h0D₀
          (hermiteBeforeRankPolynomialFamily D₀ representative offset₀ S
            (fun q => restrictedPaperPolynomialTranslateToZero D w₀ (Q q)) r))
        (analyticGermFormalDerivations p) ∧
      ((m + p : ℕ) : ENat) ≤ I.height ∧
      Ideal.span (Set.range g) = I ∧
      IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
      (∀ j w, (G j w).support ⊆ (g j).support) ∧
      (∀ j d, AnalyticOnNhd ℝ (fun w => (G j w).coeff d) W) ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
        (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (PaperRankRetainedSymbols m
              (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ))) ∧
      (∀ᶠ n in atTop, ∀ j,
        MvPolynomial.eval
          (paperRankRetainedArgument
            (paperRankFullHermiteSmoothValue
              D₀ representative offset₀ S B Fbranch) (x₀ n))
          (G j (x₀ n).1.2) = 0) ∧
      (data.paperRankHermiteTopPrefixIdeal
        (RealAnalyticGerm p) S I).height = I.height ∧
      Ideal.span (Set.range (fun j =>
        data.paperRankHermiteTopPrefixAlgEquiv
          (RealAnalyticGerm p) S (g j))) =
        data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) S (g j)) =
        (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
          data S (G j) : Germ (𝓝 (0 : RestrictedBoxSpace p))
            (data.OrderedClusterPrefixRing ℝ
              (paperRankHermiteHigherCount S) data.orderedClusterCount))) ∧
      (∀ j w (v : PaperRankRetainedSymbols m
          (m * (paperRankHermitePositiveDerivativeCount S + 1)) → ℝ),
        MvPolynomial.eval
          (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixAssignment
            data S v)
          (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
            data S (G j) w) =
          MvPolynomial.eval v (G j w)) ∧
      (∀ᶠ n in atTop, ∀ j,
        MvPolynomial.eval
          (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixAssignment
            data S
            (paperRankRetainedArgument
              (paperRankFullHermiteSmoothValue
                D₀ representative offset₀ S B Fbranch) (x₀ n)))
          (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
            data S (G j) (x₀ n).1.2) = 0) ∧
      P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount S) 0) i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount S) 0) i P ∈
        certificate.terminalized.timeIdeal := by
  dsimp only
  classical
  obtain ⟨S, Q, _C, _hC, hQ⟩ :=
    exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
      A D representative offset F hF
  obtain ⟨B, hB, hbound⟩ :=
    exists_paperRankHermiteOffsetBound D offset S
  obtain ⟨Xstrip, K, K0, Fbranch, hXstrip, hFbranch, hreal, H⟩ :=
    hA.exists_commonStrip_abelHermiteFamily
      (ι := Option (Fin S.card)) hB
      (paperRankHermiteNodeMultiplicity S)
      (paperRankHermiteCoefficientCount_pos S)
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_hermiteBeforeRankElimination_at_limit
      D representative offset S R Xstrip (Xstrip + B + 3) B K K0
      Fbranch hFbranch hB H hbound Q F hQ x hx hxrepresentative
      w₀ hw₀ hxlim
  have hbottom : ((p + m : ℕ) : ENat) ≤ I.height := by
    simpa only [Nat.add_comm] using hheight
  obtain ⟨nextIdeal, tail, certificate, i, P, hP, hPembedded, hPmem⟩ :=
    data.exists_paperRankHermiteBottomTimePolynomial S I
      data.orderedClusterCount_pos_of_nonempty hbottom
  have htopSpan :
      Ideal.span (Set.range (fun j =>
        data.paperRankHermiteTopPrefixAlgEquiv
          (RealAnalyticGerm p) S (g j))) =
        data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I := by
    calc
      Ideal.span (Set.range (fun j =>
          data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) S (g j))) =
          data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S
            (Ideal.span (Set.range g)) :=
        RepresentativeClusterSubsequence.span_paperRankHermiteTopPrefixAlgEquiv_range
          (RealAnalyticGerm p) data S g
      _ = data.paperRankHermiteTopPrefixIdeal
          (RealAnalyticGerm p) S I := by rw [hspan]
  have htopGerm : ∀ j,
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (data.paperRankHermiteTopPrefixAlgEquiv
            (RealAnalyticGerm p) S (g j)) =
        (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
          data S (G j) : Germ (𝓝 (0 : RestrictedBoxSpace p))
            (data.OrderedClusterPrefixRing ℝ
              (paperRankHermiteHigherCount S) data.orderedClusterCount)) := by
    intro j
    exact
      RepresentativeClusterSubsequence.analyticPolynomialGermHom_paperRankHermiteTopPrefixAlgEquiv_of
        data S (g j) (G j) (hG j)
  have htopEval : ∀ j w (v : PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → ℝ),
      MvPolynomial.eval
        (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixAssignment
          data S v)
        (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
          data S (G j) w) =
        MvPolynomial.eval v (G j w) := by
    intro j w v
    rw [RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative_apply]
    exact RepresentativeClusterSubsequence.eval_paperRankHermiteTopPrefixAlgEquiv
      ℝ data S v (G j w)
  have htopVanish : ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval
        (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixAssignment
          data S
          (paperRankRetainedArgument
            (paperRankFullHermiteSmoothValue
              (D.translateToZero w₀) representative
              (restrictedOffsetTranslateToZero w₀ offset) S B Fbranch)
            (restrictedSourceTranslateToZero w₀ (x n))))
        (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
          data S (G j)
            (restrictedSourceTranslateToZero w₀ (x n)).1.2) = 0 := by
    filter_upwards [hvanish] with n hn
    intro j
    rw [htopEval j]
    exact hn j
  exact ⟨S, Q, B, Xstrip, K, K0, Fbranch, I, c, g, G, W,
    nextIdeal, tail, certificate, i, P, hQ, hB, hXstrip, hFbranch,
    hreal, H, hbound, hI, hheight, hspan, hWopen, h0W, hsupport,
    hanalytic, hG, hvanish,
    data.paperRankHermiteTopPrefixIdeal_height (RealAnalyticGerm p) S I,
    htopSpan, htopGerm, htopEval, htopVanish,
    hP, hPembedded, hPmem⟩

end AbelFormalization
