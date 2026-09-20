import AbelFormalization.RestrictedBasePaperRankElimination
import AbelFormalization.SeparatedFiniteRealJetTrace

/-!
# The restricted rank-elimination output at the separated-trace boundary

The quantitative-transfer interface needs a nonempty finite family.  The
rank-elimination theorem legitimately returns an empty family when its ideal
is zero.  This module pads the actual family and its actual analytic
representatives by a leading zero, and transports every property supplied by
rank elimination.  In particular, this is not an abstract data assumption:
the witnesses are obtained directly from
`IsAbel.exists_restrictedBasePaperRankElimination_at_limit`.
-/

noncomputable section
set_option autoImplicit false

open Filter Set

namespace AbelFormalization

open scoped Polynomial Topology

variable {ι : Type*}

universe u v w

/-- Add a leading zero to a central-transfer certificate.  All four
generated ideals are unchanged, while the source family becomes
definitionally nonempty. -/
def CentralQuantitativeTransferCertificate.padZero
    {R : Type u} [CommRing R]
    {Block : Type v} {Time : Type w} {d : Block → ℕ} {h : ℕ}
    {omega : CentralPolynomialIndex Block d Time → Fin h → ℤ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R)}
    (certificate : CentralQuantitativeTransferCertificate
      R Block Time d h omega I) :
    CentralQuantitativeTransferCertificate R Block Time d h omega I := by
  let sourcePlus : Fin (certificate.count + 1) →
      MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R :=
    fun a ↦ Fin.cases 0 certificate.source a
  refine {
    count := certificate.count + 1
    source := sourcePlus
    source_mem := ?_
    initial_span := ?_
    normalized_span := ?_
    central_span := ?_ }
  ·
    intro a
    refine Fin.cases ?_ (fun j ↦ ?_) a
    · exact (I.map
        (polynomialCoordinateTranslation
          (Sum.elim (fun _ : Fin h ↦ (-1 : R))
            (fun _ : CentralPolynomialIndex Block d Time ↦ 0))).toRingHom).zero_mem
    · simpa [sourcePlus] using certificate.source_mem j
  ·
    have hfamily :
        (fun a : Fin (certificate.count + 1) ↦
          lexicographicInitialForm (centralLaurentWeight omega)
            (sourcePlus a)) =
        (@Fin.cons certificate.count (fun _ ↦
          MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)
          0 (fun a ↦
          lexicographicInitialForm (centralLaurentWeight omega)
            (certificate.source a))) := by
      funext a
      refine Fin.cases ?_ (fun j ↦ ?_) a
      · simp [sourcePlus]
      · simp [sourcePlus]
    rw [hfamily, Ideal.span_range_finCons_zero]
    exact certificate.initial_span
  ·
    have hfamily :
        (fun a : Fin (certificate.count + 1) ↦
          centralNormalizedInitialPolynomial omega
            (sourcePlus a)) =
        (@Fin.cons certificate.count (fun _ ↦
          MvPolynomial (CentralPolynomialIndex Block d Time) R)
          0 (fun a ↦
          centralNormalizedInitialPolynomial omega
            (certificate.source a))) := by
      funext a
      refine Fin.cases ?_ (fun j ↦ ?_) a
      · simp [sourcePlus, centralNormalizedInitialPolynomial]
      · simp [sourcePlus, centralNormalizedInitialPolynomial]
    rw [hfamily, Ideal.span_range_finCons_zero]
    exact certificate.normalized_span
  ·
    have hfamily :
        (fun a : Fin (certificate.count + 1) ↦
          centralPolynomialPhi R Block d Time
            (centralNormalizedInitialPolynomial omega
              (sourcePlus a))) =
        (@Fin.cons certificate.count (fun _ ↦
          CentralPolynomial R Block d Time)
          0 (fun a ↦
          centralPolynomialPhi R Block d Time
            (centralNormalizedInitialPolynomial omega
              (certificate.source a)))) := by
      funext a
      refine Fin.cases ?_ (fun j ↦ ?_) a
      · simp [sourcePlus, centralNormalizedInitialPolynomial]
      · simp [sourcePlus]
    rw [hfamily, Ideal.span_range_finCons_zero]
    exact certificate.central_span

/-- Noetherianity therefore always supplies a central-transfer certificate
whose finite source family is nonempty, including for the zero ideal. -/
theorem exists_nonempty_centralQuantitativeTransferCertificate
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Block : Type v} {Time : Type w} [Finite Block] [Finite Time]
    {d : Block → ℕ} {h : ℕ}
    (omega : CentralPolynomialIndex Block d Time → Fin h → ℤ)
    (I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) :
    ∃ certificate : CentralQuantitativeTransferCertificate
        R Block Time d h omega I,
      Nonempty (Fin certificate.count) := by
  obtain ⟨certificate⟩ :=
    exists_centralQuantitativeTransferCertificate omega I
  refine ⟨certificate.padZero, ?_⟩
  change Nonempty (Fin (certificate.count + 1))
  exact ⟨⟨0, Nat.succ_pos _⟩⟩

/-- A uniform zero derivative-order family used only to place every retained
paper-rank symbol in the independent-variable block of a real-jet transfer
ring.  A later cluster-specific relabeling can replace this canonical
embedding. -/
def paperRankZeroDerivativeOrder (m b : ℕ) : Fin (m + b + 1) → ℕ :=
  fun _ ↦ 0

/-- Canonical injective algebraic placement of the retained paper-rank
variables in a sufficiently large `RealJetTransferIndex`. -/
def paperRankRetainedToRealJetTransferIndex (m b : ℕ) :
    PaperRankRetainedSymbols m b →
      RealJetTransferIndex (m + b) (paperRankZeroDerivativeOrder m b) :=
  fun i ↦ Sum.inl (Fin.castSucc (finSumFinEquiv i))

theorem paperRankRetainedToRealJetTransferIndex_injective (m b : ℕ) :
    Function.Injective (paperRankRetainedToRealJetTransferIndex m b) := by
  intro i j hij
  apply finSumFinEquiv.injective
  apply Fin.castSucc_injective (m + b)
  exact Sum.inl.inj hij

/-- Renaming a displayed generating family commutes exactly with taking its
spanned ideal. -/
theorem span_rename_range_eq_map_span
    {R : Type u} [CommRing R] {σ τ : Type*}
    {c : ℕ} (r : σ → τ) (g : Fin c → MvPolynomial σ R) :
    Ideal.span (Set.range (fun j ↦ MvPolynomial.rename r (g j))) =
      Ideal.map (MvPolynomial.rename r) (Ideal.span (Set.range g)) := by
  rw [Ideal.map_span]
  congr 1
  change Set.range ((MvPolynomial.rename r) ∘ g) =
    (MvPolynomial.rename r) '' Set.range g
  exact Set.range_comp _ _

/-- Every real-jet ideal over analytic germs admits, simultaneously, a
nonempty transfer certificate and actual polynomial-valued analytic
representatives for all of that certificate's source polynomials. -/
theorem exists_nonempty_realJetTransferCertificate_with_representatives
    {p q : ℕ} (d : Fin (q + 1) → ℕ)
    (I : Ideal (MvPolynomial (RealJetTransferIndex q d)
      (RealAnalyticGerm p))) :
    ∃ certificate : CentralQuantitativeTransferCertificate
        (RealAnalyticGerm p) (Fin (q + 1)) (Fin (q + 1)) d (q + 1)
          (centralTransferShear d) I,
    ∃ sourceRepresentative : Fin certificate.count →
        RestrictedBoxSpace p →
          MvPolynomial (RealJetTransferIndex q d) ℝ,
    ∃ U : Set (RestrictedBoxSpace p),
      Nonempty (Fin certificate.count) ∧
      IsOpen U ∧ (0 : RestrictedBoxSpace p) ∈ U ∧
      (∀ a w, (sourceRepresentative a w).support ⊆
        (certificate.source a).support) ∧
      (∀ a e, AnalyticOnNhd ℝ
        (fun w ↦ (sourceRepresentative a w).coeff e) U) ∧
      ∀ a, analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (certificate.source a) =
        (sourceRepresentative a : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (RealJetTransferIndex q d) ℝ)) := by
  obtain ⟨certificate, hcount⟩ :=
    exists_nonempty_centralQuantitativeTransferCertificate
      (centralTransferShear d) I
  obtain ⟨sourceRepresentative, U, hUopen, h0U, hsupport,
      hanalytic, hrepresent⟩ :=
    exists_analyticPolynomialRepresentatives
      (0 : RestrictedBoxSpace p) certificate.source
  exact ⟨certificate, sourceRepresentative, U, hcount, hUopen, h0U,
    hsupport, hanalytic, hrepresent⟩

/-- A concrete nonzero terminal polynomial supplies the terminal seed for
an already assembled finite separated-cluster trace.  Only the value of the
distinguished padded generator `0` is needed; all other terminal generators
may be arbitrary. -/
theorem SeparatedClustersBackwardTrace.initial_of_nonzeroPolynomial_terminal
    {X : Type*} {l : Filter X} {clusterCount : ℕ}
    {generatorCount : ℕ → ℕ} {scale : ℕ → X → ℝ}
    {value : (j : ℕ) → Fin (generatorCount j + 1) → X → ℝ}
    (trace : SeparatedClustersBackwardTrace l clusterCount
      generatorCount scale value)
    (P : ℝ[X]) (hP : P ≠ 0) (u : X → ℝ)
    (hu : Tendsto u l atTop)
    (hterminal : ∀ᶠ x in l,
      value clusterCount 0 x = P.eval (u x)) :
    HasInversePowerLowerBound l (scale 0) (value 0) := by
  obtain ⟨c, hc, hPbound⟩ :=
    nonzeroPolynomial_exists_pos_eventually_le_abs_eval_comp P hP hu
  have hlower : HasInversePowerLowerBound l (scale clusterCount)
      (value clusterCount) := by
    refine ⟨c, hc, 0, ?_⟩
    filter_upwards [hPbound, hterminal] with x hx hvalue
    simp only [pow_zero, div_one]
    calc
      c ≤ |P.eval (u x)| := hx
      _ = |value clusterCount 0 x| := congrArg abs hvalue.symm
      _ ≤ finiteFamilyMaxAbs (value clusterCount) x :=
        abs_le_finiteFamilyMaxAbs (value clusterCount) x 0
  exact trace.initial_of_terminal hlower

/-- The rank-elimination family at an arbitrary bounded-coordinate limit can
be made nonempty without changing its span, analytic-germ identities, or
eventual vanishing along the normalized regular-zero sequence. -/
theorem IsAbel.exists_restrictedBasePaperRankElimination_at_limit_padded
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (𝓝 w₀)) :
    let D₀ : RestrictedBox p := D.translateToZero w₀
    let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
      restrictedOffsetTranslateToZero w₀ offset
    let F₀ : Fin (m + p + a) → RestrictedSource m p a → ℝ :=
      restrictedEquationFamilyTranslateToZero w₀ F
    let x₀ : ℕ → RestrictedSource m p a :=
      fun n ↦ restrictedSourceNormalizeAt w₀ (x n)
    let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
      D.zero_mem_closedBox_translateToZero hw₀
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          D₀.analyticNearClosedBoxSubalgebra,
    ∃ C : Finset D₀.analyticNearClosedBoxSubalgebra,
    ∃ I : Ideal
        (MvPolynomial (PaperRankRetainedSymbols m S.card)
          (RealAnalyticGerm p)),
    ∃ c : ℕ,
    ∃ g : Fin (c + 1) →
        MvPolynomial (PaperRankRetainedSymbols m S.card)
          (RealAnalyticGerm p),
    ∃ G : Fin (c + 1) → RestrictedBoxSpace p →
        MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ,
    ∃ W : Set (RestrictedBoxSpace p),
      (∀ i d, d ∈ (Q i).support → (Q i).coeff d ∈ C) ∧
      (∀ i, restrictedPaperPolynomialValue A D₀ representative offset₀
        (restrictedJetEnumeration S) (Q i) = F₀ i) ∧
      I = jacobianEliminationIdeal a
        (fun i ↦ restrictedPaperGermPolynomial D₀ h0D₀ (Q i))
        (analyticGermFormalDerivations p) ∧
      ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
      Ideal.span (Set.range g) = I ∧
      IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
      (∀ j w, (G j w).support ⊆ (g j).support) ∧
      (∀ j d, AnalyticOnNhd ℝ (fun w ↦ (G j w).coeff d) W) ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
        (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) ∧
      ∀ᶠ n in atTop, ∀ j,
        MvPolynomial.eval
          (paperRankRetainedArgument
            (restrictedSelectedAbelJets A representative offset₀
              (restrictedJetEnumeration S)) (x₀ n))
          (G j (x₀ n).1.2) = 0 := by
  dsimp only
  obtain ⟨S, Q, C, I, c, g, G, W, hC, hQ, hI, hheight, hspan,
      hWopen, h0W, hsupport, hanalytic, hG, hvanish⟩ :=
    hA.exists_restrictedBasePaperRankElimination_at_limit
      D representative offset R hDomain F hF x hx w₀ hw₀ hxlim
  let gPlus : Fin (c + 1) →
      MvPolynomial (PaperRankRetainedSymbols m S.card)
        (RealAnalyticGerm p) :=
    Fin.cons 0 g
  let GPlus : Fin (c + 1) → RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ :=
    Fin.cons (fun _ ↦ 0) G
  refine ⟨S, Q, C, I, c, gPlus, GPlus, W, hC, hQ, hI, hheight, ?_,
    hWopen, h0W, ?_, ?_, ?_, ?_⟩
  · simpa only [gPlus, Ideal.span_range_finCons_zero] using hspan
  · intro j w
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [GPlus, gPlus]
    · simpa only [GPlus, gPlus, Fin.cons_succ] using hsupport k w
  · intro j d
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change AnalyticOnNhd ℝ
        (fun _ : RestrictedBoxSpace p ↦ (0 : ℝ)) W
      exact analyticOnNhd_const
    · simpa only [GPlus, Fin.cons_succ] using hanalytic k d
  · intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change (0 : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)) =
          ((fun _ : RestrictedBoxSpace p ↦
            (0 : MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)) :
              Germ (𝓝 (0 : RestrictedBoxSpace p))
                (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))
      rfl
    · simpa only [GPlus, gPlus, Fin.cons_succ] using hG k
  · filter_upwards [hvanish] with n hn
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [GPlus]
    · simpa only [GPlus, Fin.cons_succ] using hn k

/-- After `Λ` and `N` have been fixed, the actual rank-elimination ideal can
be placed in a concrete real-jet transfer ring.  The theorem chooses a
nonempty quantitative-transfer certificate and simultaneous analytic
representatives for all of its source coefficients.  It also retains the
actual padded rank generators and their vanishing on the separated
restriction.

The canonical placement puts all rank variables in the independent `q`
block.  Identifying the manuscript's individual time/derivative clusters is
the remaining cluster-specific relabeling step. -/
theorem IsAbel.exists_restrictedRank_realJetTransferBoundary
    {A : ℝ → ℝ} (hA : IsAbel A)
    (Γ : ℕ → Set ℕ) (Λ : Set ℕ) (N : ℕ)
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (𝓝 w₀)) :
    let D₀ : RestrictedBox p := D.translateToZero w₀
    let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
      restrictedOffsetTranslateToZero w₀ offset
    let F₀ : Fin (m + p + a) → RestrictedSource m p a → ℝ :=
      restrictedEquationFamilyTranslateToZero w₀ F
    let x₀ : ℕ → RestrictedSource m p a :=
      fun n ↦ restrictedSourceNormalizeAt w₀ (x n)
    let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
      D.zero_mem_closedBox_translateToZero hw₀
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          D₀.analyticNearClosedBoxSubalgebra,
    ∃ I : Ideal (MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RealAnalyticGerm p)),
    ∃ c : ℕ,
    ∃ g : Fin (c + 1) →
      MvPolynomial (PaperRankRetainedSymbols m S.card)
        (RealAnalyticGerm p),
    ∃ G : Fin (c + 1) → RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ,
    ∃ W : Set (RestrictedBoxSpace p),
    ∃ J : Ideal (MvPolynomial
      (RealJetTransferIndex (m + S.card)
        (paperRankZeroDerivativeOrder m S.card))
      (RealAnalyticGerm p)),
    ∃ certificate : CentralQuantitativeTransferCertificate
      (RealAnalyticGerm p) (Fin (m + S.card + 1))
      (Fin (m + S.card + 1))
      (paperRankZeroDerivativeOrder m S.card) (m + S.card + 1)
      (centralTransferShear (paperRankZeroDerivativeOrder m S.card)) J,
    ∃ sourceRepresentative : Fin certificate.count →
      RestrictedBoxSpace p →
        MvPolynomial
          (RealJetTransferIndex (m + S.card)
            (paperRankZeroDerivativeOrder m S.card)) ℝ,
    ∃ U : Set (RestrictedBoxSpace p),
      (∀ i, restrictedPaperPolynomialValue A D₀ representative offset₀
        (restrictedJetEnumeration S) (Q i) = F₀ i) ∧
      I = jacobianEliminationIdeal a
        (fun i ↦ restrictedPaperGermPolynomial D₀ h0D₀ (Q i))
        (analyticGermFormalDerivations p) ∧
      ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
      Ideal.span (Set.range g) = I ∧
      J = Ideal.map
        (MvPolynomial.rename
          (paperRankRetainedToRealJetTransferIndex m S.card)) I ∧
      Ideal.span (Set.range (fun j ↦
        MvPolynomial.rename
          (paperRankRetainedToRealJetTransferIndex m S.card) (g j))) = J ∧
      Nonempty (Fin certificate.count) ∧
      IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
      (∀ j w, (G j w).support ⊆ (g j).support) ∧
      (∀ j d, AnalyticOnNhd ℝ (fun w ↦ (G j w).coeff d) W) ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
        (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) ∧
      IsOpen U ∧ (0 : RestrictedBoxSpace p) ∈ U ∧
      (∀ j w, (sourceRepresentative j w).support ⊆
        (certificate.source j).support) ∧
      (∀ j d, AnalyticOnNhd ℝ
        (fun w ↦ (sourceRepresentative j w).coeff d) U) ∧
      (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
          (certificate.source j) =
        (sourceRepresentative j : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (RealJetTransferIndex (m + S.card)
              (paperRankZeroDerivativeOrder m S.card)) ℝ))) ∧
      ∀ᶠ n in separatedRestriction Λ Γ N, ∀ j,
        MvPolynomial.eval
          (paperRankRetainedArgument
            (restrictedSelectedAbelJets A representative offset₀
              (restrictedJetEnumeration S)) (x₀ n))
          (G j (x₀ n).1.2) = 0 := by
  dsimp only
  obtain ⟨S, Q, C, I, c, g, G, W, hC, hQ, hI, hheight, hspan,
      hWopen, h0W, hsupport, hanalytic, hG, hvanish⟩ :=
    hA.exists_restrictedBasePaperRankElimination_at_limit_padded
      D representative offset R hDomain F hF x hx w₀ hw₀ hxlim
  let r := paperRankRetainedToRealJetTransferIndex m S.card
  let J : Ideal (MvPolynomial
      (RealJetTransferIndex (m + S.card)
        (paperRankZeroDerivativeOrder m S.card))
      (RealAnalyticGerm p)) :=
    Ideal.map (MvPolynomial.rename r) I
  obtain ⟨certificate, sourceRepresentative, U, hcount, hUopen, h0U,
      hsourceSupport, hsourceAnalytic, hsourceGerm⟩ :=
    exists_nonempty_realJetTransferCertificate_with_representatives
      (paperRankZeroDerivativeOrder m S.card) J
  have hrenamedSpan : Ideal.span (Set.range (fun j ↦
      MvPolynomial.rename r (g j))) = J := by
    calc
      Ideal.span (Set.range (fun j ↦ MvPolynomial.rename r (g j))) =
          Ideal.map (MvPolynomial.rename r)
            (Ideal.span (Set.range g)) :=
        span_rename_range_eq_map_span r g
      _ = J := by rw [hspan]
  have hvanishRestricted :
      ∀ᶠ n in separatedRestriction Λ Γ N, ∀ j,
        MvPolynomial.eval
          (paperRankRetainedArgument
            (restrictedSelectedAbelJets A representative
              (restrictedOffsetTranslateToZero w₀ offset)
              (restrictedJetEnumeration S))
            (restrictedSourceNormalizeAt w₀ (x n)))
          (G j (restrictedSourceNormalizeAt w₀ (x n)).1.2) = 0 := by
    rw [eventually_separatedRestriction_iff]
    filter_upwards [hvanish] with n hn
    exact fun _ ↦ hn
  refine ⟨S, Q, I, c, g, G, W, J, certificate,
    sourceRepresentative, U, hQ, hI, hheight, hspan, rfl,
    hrenamedSpan, hcount, hWopen, h0W, hsupport, hanalytic, hG,
    hUopen, h0U, hsourceSupport, hsourceAnalytic, hsourceGerm,
    hvanishRestricted⟩

end AbelFormalization
