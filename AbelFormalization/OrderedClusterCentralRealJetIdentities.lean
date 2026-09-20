import AbelFormalization.HermiteRankTopPrefixClusterValues
import AbelFormalization.OrderedClusterAlgebraicDescentTraceData
import AbelFormalization.TerminalizedClusterIterationTraceData
import AbelFormalization.SeparatedRingHomRealJetStep

/-!
# Evaluated identities for an ordered-cluster central step

The algebraic descent records central-transfer inputs and outputs as ideals,
while quantitative transfer is stated for finite evaluated generator
families.  This file supplies the intervening finite change-of-generators
data.  It also records the two evaluation homomorphisms used by the real-jet
step and proves the exact central and source identities in the
coefficientwise form expected by
`TerminalGeneratorBackwardIdentity.terminal_lower_of_realJet_transfer_coefficientwise`.

The final construction applies to every retained step of an actual ordered
cluster.  Its input generators are extended along `Sum.inr`; thus the fresh
representative variables are present in the transfer input but absent from
the displayed generators, exactly as required by
`unusedRepresentativeExtension`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v w

/-- Extending every member of a finite family along the right summand
extends the ideal which that family spans. -/
theorem span_rename_inr_range_eq_unusedPolynomialExtension
    {R X Q κ : Type*} [CommRing R]
    (g : κ → MvPolynomial X R) :
    Ideal.span (Set.range (fun k ↦
        MvPolynomial.rename (Sum.inr : X → Q ⊕ X) (g k))) =
      unusedPolynomialExtension Q (Ideal.span (Set.range g)) := by
  unfold unusedPolynomialExtension
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨g i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-! ## Finite algebraic identities for one central transfer -/

/-- Literal change-of-generators identities on the two sides of one central
quantitative-transfer certificate.  The source family is allowed to be any
finite family spanning an ideal containing the certificate sources, and the
central family any finite family contained in the ideal spanned by the
canonical central generators. -/
structure CentralTransferDisplayedIdentities
    {R : Type u} [CommRing R]
    {Block : Type v} {Time : Type w} [Fintype Block] [Fintype Time]
    {d : Block → ℕ} {h : ℕ}
    {omega : CentralPolynomialIndex Block d Time → Fin h → ℤ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R)}
    (certificate : CentralQuantitativeTransferCertificate
      R Block Time d h omega I)
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    (sourceGenerator : Source →
      MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)
    (centralGenerator : Central → CentralPolynomial R Block d Time) where
  sourceCoefficient : Fin certificate.count → Source →
    MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R
  centralCoefficient : Central → Fin certificate.count →
    CentralPolynomial R Block d Time
  source_identity : ∀ a,
    certificate.source a =
      ∑ k, sourceCoefficient a k * sourceGenerator k
  central_identity : ∀ b,
    centralGenerator b =
      ∑ a, centralCoefficient b a *
        centralPolynomialPhi R Block d Time
          (centralNormalizedInitialPolynomial omega
            (certificate.source a))

/-- Ideal membership on the two displayed sides chooses all finite
change-of-generators coefficients at once. -/
theorem nonempty_centralTransferDisplayedIdentities
    {R : Type u} [CommRing R]
    {Block : Type v} {Time : Type w} [Fintype Block] [Fintype Time]
    {d : Block → ℕ} {h : ℕ}
    {omega : CentralPolynomialIndex Block d Time → Fin h → ℤ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex Block d Time) R)}
    (certificate : CentralQuantitativeTransferCertificate
      R Block Time d h omega I)
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    (sourceGenerator : Source →
      MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)
    (centralGenerator : Central → CentralPolynomial R Block d Time)
    (hsource : ∀ a, certificate.source a ∈
      Ideal.span (Set.range sourceGenerator))
    (hcentral : ∀ b, centralGenerator b ∈
      Ideal.span (Set.range (fun a ↦
        centralPolynomialPhi R Block d Time
          (centralNormalizedInitialPolynomial omega
            (certificate.source a))))) :
    Nonempty (CentralTransferDisplayedIdentities certificate
      sourceGenerator centralGenerator) := by
  classical
  choose sourceCoefficient hsourceCoefficient using fun a ↦
    Ideal.mem_span_range_iff_exists_fun.mp (hsource a)
  choose centralCoefficient hcentralCoefficient using fun b ↦
    Ideal.mem_span_range_iff_exists_fun.mp (hcentral b)
  exact ⟨{
    sourceCoefficient := sourceCoefficient
    centralCoefficient := centralCoefficient
    source_identity := fun a ↦ (hsourceCoefficient a).symm
    central_identity := fun b ↦ (hcentralCoefficient b).symm
  }⟩

/-! ## The two real-jet evaluation homomorphisms -/

/-- Ring-homomorphic evaluation of the literal, unnormalized real-jet source
coordinates at one sequence index. -/
def realJetSourceEvaluationHom
    {R : Type u} [CommRing R] {m : ℕ} {A : ℝ → ℝ}
    (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (d : Fin (m + 1) → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (n : ℕ) :
    MvPolynomial (RealJetTransferIndex m d) R →+* ℝ :=
  MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
    (fun x ↦ realJetActualAssignment u d jets x n)

/-- Ring-homomorphic evaluation of the canonical central coordinates at one
sequence index. -/
def realJetCentralEvaluationHom
    {R : Type u} [CommRing R] {m : ℕ}
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (d : Fin (m + 1) → ℕ) (n : ℕ) :
    CentralPolynomial R (Fin (m + 1)) d (Fin (m + 1)) →+* ℝ :=
  MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
    (realCentralTransferCentralValue A (fun i ↦ u i n) d)

/-- Coefficient values obtained from a genuine sequence-valued coefficient
ring homomorphism.  This is a valid specialization of the more flexible
coefficientwise transfer interface. -/
def CentralQuantitativeTransferCertificate.ringHomCoefficientValue
    {R : Type u} [CommRing R] {m : ℕ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    (certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    (c : R →+* (ℕ → ℝ))
    (a : Fin certificate.count)
    (e : RealJetTransferIndex m d →₀ ℕ) (n : ℕ) : ℝ :=
  c ((certificate.source a).coeff e) n

theorem realJetCoefficientwiseSourceEvaluation_ringHomCoefficientValue
    {R : Type u} [CommRing R] {m : ℕ} {A : ℝ → ℝ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    (certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (a : Fin certificate.count) (n : ℕ) :
    realJetCoefficientwiseSourceEvaluation d
        (certificate.ringHomCoefficientValue c a) u jets
        (certificate.source a) n =
      realJetSourceEvaluationHom c u d jets n
        (certificate.source a) := by
  change finiteSupportPolynomialEvaluation (certificate.source a)
      (fun e ↦ coefficientEvaluationAt c n
        ((certificate.source a).coeff e))
      (fun x ↦ realJetActualAssignment u d jets x n) =
    MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
      (fun x ↦ realJetActualAssignment u d jets x n)
      (certificate.source a)
  exact finiteSupportPolynomialEvaluation_eq_eval₂Hom
    (coefficientEvaluationAt c n) (certificate.source a)
      (fun x ↦ realJetActualAssignment u d jets x n)

theorem realJetCoefficientwiseCentralEvaluation_ringHomCoefficientValue
    {R : Type u} [CommRing R] {m : ℕ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    (certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I)
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (a : Fin certificate.count) (n : ℕ) :
    realJetCoefficientwiseCentralEvaluation A d
        (certificate.ringHomCoefficientValue c a) u
        (certificate.source a) n =
      realJetCentralEvaluationHom A c u d n
        (centralPolynomialPhi R (Fin (m + 1)) d (Fin (m + 1))
          (centralNormalizedInitialPolynomial
            (centralTransferShear d) (certificate.source a))) := by
  change finiteSupportInitialEvaluation
      (centralLaurentWeight (centralTransferShear d))
      (certificate.source a)
      (fun e ↦ coefficientEvaluationAt c n
        ((certificate.source a).coeff e))
      (realCentralTransferMainValue A (fun i ↦ u i n) d) = _
  exact finiteSupportInitialEvaluation_realCentralMain_eq_centralGenerator
    (coefficientEvaluationAt c n) A (fun i ↦ u i n) d
      (certificate.source a)

/-! ## Evaluating the algebraic identities -/

namespace CentralTransferDisplayedIdentities

/-- Evaluation of the fixed central coefficient matrix. -/
def evaluatedCentralCoefficient
    {R : Type u} [CommRing R] {m : ℕ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    {certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I}
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    {sourceGenerator : Source → MvPolynomial (RealJetTransferIndex m d) R}
    {centralGenerator : Central →
      CentralPolynomial R (Fin (m + 1)) d (Fin (m + 1))}
    (identities : CentralTransferDisplayedIdentities certificate
      sourceGenerator centralGenerator)
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (b : Central) (a : Fin certificate.count) (n : ℕ) : ℝ :=
  realJetCentralEvaluationHom A c u d n
    (identities.centralCoefficient b a)

/-- Evaluation of the fixed source coefficient matrix. -/
def evaluatedSourceCoefficient
    {R : Type u} [CommRing R] {m : ℕ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    {certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I}
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    {sourceGenerator : Source → MvPolynomial (RealJetTransferIndex m d) R}
    {centralGenerator : Central →
      CentralPolynomial R (Fin (m + 1)) d (Fin (m + 1))}
    (identities : CentralTransferDisplayedIdentities certificate
      sourceGenerator centralGenerator)
    {A : ℝ → ℝ} (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (a : Fin certificate.count) (k : Source) (n : ℕ) : ℝ :=
  realJetSourceEvaluationHom c u d jets n
    (identities.sourceCoefficient a k)

/-- The literal central change-of-generators identity, in exactly the
coefficientwise real-jet form required by quantitative transfer. -/
theorem evaluated_central_identity
    {R : Type u} [CommRing R] {m : ℕ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    {certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I}
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    {sourceGenerator : Source → MvPolynomial (RealJetTransferIndex m d) R}
    {centralGenerator : Central →
      CentralPolynomial R (Fin (m + 1)) d (Fin (m + 1))}
    (identities : CentralTransferDisplayedIdentities certificate
      sourceGenerator centralGenerator)
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (b : Central) (n : ℕ) :
    realJetCentralEvaluationHom A c u d n (centralGenerator b) =
      ∑ a, identities.evaluatedCentralCoefficient A c u b a n *
        realJetCoefficientwiseCentralEvaluation A d
          (certificate.ringHomCoefficientValue c a) u
          (certificate.source a) n := by
  have hid := congrArg (realJetCentralEvaluationHom A c u d n)
    (identities.central_identity b)
  rw [map_sum] at hid
  simpa only [map_mul, evaluatedCentralCoefficient,
    realJetCoefficientwiseCentralEvaluation_ringHomCoefficientValue] using hid

/-- The literal source change-of-generators identity, in exactly the
coefficientwise real-jet form required by quantitative transfer. -/
theorem evaluated_source_identity
    {R : Type u} [CommRing R] {m : ℕ} {A : ℝ → ℝ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    {certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I}
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    {sourceGenerator : Source → MvPolynomial (RealJetTransferIndex m d) R}
    {centralGenerator : Central →
      CentralPolynomial R (Fin (m + 1)) d (Fin (m + 1))}
    (identities : CentralTransferDisplayedIdentities certificate
      sourceGenerator centralGenerator)
    (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (a : Fin certificate.count) (n : ℕ) :
    realJetCoefficientwiseSourceEvaluation d
        (certificate.ringHomCoefficientValue c a) u jets
        (certificate.source a) n =
      ∑ k, identities.evaluatedSourceCoefficient c u jets a k n *
        realJetSourceEvaluationHom c u d jets n (sourceGenerator k) := by
  rw [realJetCoefficientwiseSourceEvaluation_ringHomCoefficientValue]
  have hid := congrArg (realJetSourceEvaluationHom c u d jets n)
    (identities.source_identity a)
  rw [map_sum] at hid
  simpa only [map_mul, evaluatedSourceCoefficient] using hid

/-- Both pointwise identities packaged as eventual identities on `atTop`.
These are the two algebraic hypotheses consumed by the coefficientwise
one-cluster transfer theorem; all remaining premises of that theorem are
quantitative bounds. -/
theorem eventually_evaluated_identities
    {R : Type u} [CommRing R] {m : ℕ} {A : ℝ → ℝ}
    {d : Fin (m + 1) → ℕ}
    {I : Ideal (MvPolynomial (RealJetTransferIndex m d) R)}
    {certificate : CentralQuantitativeTransferCertificate R
      (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
      (centralTransferShear d) I}
    {Source Central : Type*} [Fintype Source] [Fintype Central]
    {sourceGenerator : Source → MvPolynomial (RealJetTransferIndex m d) R}
    {centralGenerator : Central →
      CentralPolynomial R (Fin (m + 1)) d (Fin (m + 1))}
    (identities : CentralTransferDisplayedIdentities certificate
      sourceGenerator centralGenerator)
    (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    (∀ᶠ n in atTop, ∀ b,
      realJetCentralEvaluationHom A c u d n (centralGenerator b) =
        ∑ a, identities.evaluatedCentralCoefficient A c u b a n *
          realJetCoefficientwiseCentralEvaluation A d
            (certificate.ringHomCoefficientValue c a) u
            (certificate.source a) n) ∧
    (∀ᶠ n in atTop, ∀ a,
      realJetCoefficientwiseSourceEvaluation d
          (certificate.ringHomCoefficientValue c a) u jets
          (certificate.source a) n =
        ∑ k, identities.evaluatedSourceCoefficient c u jets a k n *
          realJetSourceEvaluationHom c u d jets n (sourceGenerator k)) := by
  constructor
  · exact Filter.Eventually.of_forall fun n b ↦
      identities.evaluated_central_identity A c u b n
  · exact Filter.Eventually.of_forall fun n a ↦
      identities.evaluated_source_identity c u jets a n

end CentralTransferDisplayedIdentities

/-! ## An actual retained step, with unused representatives adjoined -/

namespace TerminalizedClusterCertificate

/-- Displayed generators and exact transfer identities for retained central
iteration `j`.  The source generators are the `Sum.inr` extensions of a
family spanning the current retained ideal; the output family spans the
literal next ideal in the stored iteration. -/
structure RetainedCentralStepDisplayedData
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate R h higher Q}
    (transferData : certificate.CentralIterationTransferData)
    (j : Fin certificate.extraSteps) where
  input : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))
    (certificate.centralIterationIdeal j)
  output : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))
    (certificate.centralIterationIdeal (j + 1))
  identities : CentralTransferDisplayedIdentities
    (transferData.transferCertificate j)
    (fun k ↦ MvPolynomial.rename Sum.inr (input.generator k))
    output.generator

/-- Noetherianity chooses displayed generators and both exact coefficient
matrices for every retained central step. -/
theorem nonempty_retainedCentralStepDisplayedData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate R h higher Q}
    (transferData : certificate.CentralIterationTransferData)
    (j : Fin certificate.extraSteps) :
    Nonempty (RetainedCentralStepDisplayedData transferData j) := by
  classical
  let input := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      _ (certificate.centralIterationIdeal j))
  let output := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      _ (certificate.centralIterationIdeal (j + 1)))
  let sourceGenerator : Fin (input.count + 1) →
      MvPolynomial
        (Fin h ⊕ CentralPolynomialIndex (Fin h)
          (terminalTotalDerivativeCount higher) (Fin h)) R :=
    fun k ↦ MvPolynomial.rename Sum.inr (input.generator k)
  let canonicalCentralGenerator :
      Fin (transferData.transferCertificate j).count →
        CentralPolynomial R (Fin h)
          (terminalTotalDerivativeCount higher) (Fin h) :=
    fun a ↦ centralPolynomialPhi R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h)
      (centralNormalizedInitialPolynomial
        (centralTransferShear (terminalTotalDerivativeCount higher))
        ((transferData.transferCertificate j).source a))
  have hsourceSpan : Ideal.span (Set.range sourceGenerator) =
      (certificate.centralIterationTransferInput j).map
        (polynomialCoordinateTranslation
          (Sum.elim (fun _ : Fin h ↦ (-1 : R))
            (fun _ : CentralPolynomialIndex (Fin h)
              (terminalTotalDerivativeCount higher) (Fin h) ↦ 0))).toRingHom := by
    calc
      Ideal.span (Set.range sourceGenerator) =
          unusedPolynomialExtension (Fin h)
            (Ideal.span (Set.range input.generator)) :=
        span_rename_inr_range_eq_unusedPolynomialExtension input.generator
      _ = unusedRepresentativeExtension R
          (terminalTotalDerivativeCount higher) (Fin h)
          (certificate.centralIterationIdeal j) := by
        rw [input.span_eq]
        rfl
      _ = (certificate.centralIterationTransferInput j).map
          (polynomialCoordinateTranslation
            (Sum.elim (fun _ : Fin h ↦ (-1 : R))
              (fun _ : CentralPolynomialIndex (Fin h)
                (terminalTotalDerivativeCount higher) (Fin h) ↦ 0))).toRingHom := by
        change unusedRepresentativeExtension R
            (terminalTotalDerivativeCount higher) (Fin h)
              (certificate.centralIterationIdeal j) =
          (unusedRepresentativeExtension R
            (terminalTotalDerivativeCount higher) (Fin h)
              (certificate.centralIterationIdeal j)).map
            (polynomialCoordinateTranslation
              (Sum.elim (fun _ : Fin h ↦ (-1 : R))
                (fun _ : CentralPolynomialIndex (Fin h)
                  (terminalTotalDerivativeCount higher) (Fin h) ↦ 0))).toRingHom
        exact (polynomialCoordinateTranslation_unusedExtension R
          (terminalTotalDerivativeCount higher) (Fin h)
          (certificate.centralIterationIdeal j)).symm
  have hsource : ∀ a, (transferData.transferCertificate j).source a ∈
      Ideal.span (Set.range sourceGenerator) := by
    intro a
    rw [hsourceSpan]
    exact (transferData.transferCertificate j).source_mem a
  have hcanonicalSpan : Ideal.span (Set.range canonicalCentralGenerator) =
      certificate.centralIterationIdeal (j + 1) := by
    exact transferData.central_span_eq_next j
  have hcentral : ∀ b, output.generator b ∈
      Ideal.span (Set.range canonicalCentralGenerator) := by
    intro b
    have hb : output.generator b ∈
        certificate.centralIterationIdeal (j + 1) :=
      output.span_eq.le Ideal.mem_span_range_self
    exact hcanonicalSpan.ge hb
  let identities := Classical.choice
    (nonempty_centralTransferDisplayedIdentities
      (transferData.transferCertificate j)
      sourceGenerator
      output.generator hsource hcentral)
  refine ⟨{ input := input, output := output, identities := ?_ }⟩
  simpa only [sourceGenerator] using identities

end TerminalizedClusterCertificate

namespace ClusterAlgebraicReductionCertificate

/-- The index of the first, non-retained central operation in the full
central trace of a cluster. -/
def firstCentralStepIndex
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I) :
    Fin (certificate.terminalized.extraSteps + 1) :=
  ⟨0, Nat.succ_pos _⟩

/-- Arbitrary padded presentations of the translated input and central
output of one operation in the full cluster trace, equipped with literal
change-of-generators identities.  At index zero the input is the actual
curried ordered-prefix ideal; successor indices are the retained
unused-representative inputs. -/
structure FullCentralStepDisplayedData
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    (transferData : certificate.FullCentralTransferData)
    (j : Fin (certificate.terminalized.extraSteps + 1)) where
  source : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)
    ((certificate.centralTransferInput j).map
      (polynomialCoordinateTranslation
        (Sum.elim (fun _ : Fin h ↦ (-1 : R))
          (fun _ : CentralPolynomialIndex (Fin h)
            (terminalTotalDerivativeCount higher) (Fin h) ↦ 0))).toRingHom)
  central : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))
    (certificate.centralTransferOutput j)
  identities : CentralTransferDisplayedIdentities
    (transferData.transferCertificate j) source.generator central.generator

/-- Noetherianity supplies the finite presentations and both exact
coefficient matrices at every operation in the full cluster trace. -/
theorem nonempty_fullCentralStepDisplayedData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    (transferData : certificate.FullCentralTransferData)
    (j : Fin (certificate.terminalized.extraSteps + 1)) :
    Nonempty (FullCentralStepDisplayedData transferData j) := by
  classical
  let source := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      _ ((certificate.centralTransferInput j).map
        (polynomialCoordinateTranslation
          (Sum.elim (fun _ : Fin h ↦ (-1 : R))
            (fun _ : CentralPolynomialIndex (Fin h)
              (terminalTotalDerivativeCount higher) (Fin h) ↦ 0))).toRingHom))
  let central := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      _ (certificate.centralTransferOutput j))
  let canonicalCentralGenerator :
      Fin (transferData.transferCertificate j).count →
        CentralPolynomial R (Fin h)
          (terminalTotalDerivativeCount higher) (Fin h) :=
    fun a ↦ centralPolynomialPhi R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h)
      (centralNormalizedInitialPolynomial
        (centralTransferShear (terminalTotalDerivativeCount higher))
        ((transferData.transferCertificate j).source a))
  have hsource : ∀ a, (transferData.transferCertificate j).source a ∈
      Ideal.span (Set.range source.generator) := by
    intro a
    exact source.span_eq.ge
      ((transferData.transferCertificate j).source_mem a)
  have hcanonicalSpan : Ideal.span (Set.range canonicalCentralGenerator) =
      certificate.centralTransferOutput j := by
    exact transferData.central_span_eq_output j
  have hcentral : ∀ b, central.generator b ∈
      Ideal.span (Set.range canonicalCentralGenerator) := by
    intro b
    have hb : central.generator b ∈
        certificate.centralTransferOutput j :=
      central.span_eq.le Ideal.mem_span_range_self
    exact hcanonicalSpan.ge hb
  let identities := Classical.choice
    (nonempty_centralTransferDisplayedIdentities
      (transferData.transferCertificate j) source.generator
      central.generator hsource hcentral)
  exact ⟨{ source := source, central := central, identities := identities }⟩

/-- At the distinguished first index, the displayed source family spans the
translated actual input ideal of the cluster. -/
theorem FullCentralStepDisplayedData.first_source_span
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    (data : FullCentralStepDisplayedData transferData
      certificate.firstCentralStepIndex) :
    Ideal.span (Set.range data.source.generator) =
      I.map (polynomialCoordinateTranslation
        (Sum.elim (fun _ : Fin h ↦ (-1 : R))
          (fun _ : CentralPolynomialIndex (Fin h)
            (terminalTotalDerivativeCount higher) (Fin h) ↦ 0))).toRingHom := by
  simpa [firstCentralStepIndex, centralTransferInput] using data.source.span_eq

/-- At the distinguished first index, the displayed central family spans
the first central ideal of the actual curried cluster input. -/
theorem FullCentralStepDisplayedData.first_central_span
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    (data : FullCentralStepDisplayedData transferData
      certificate.firstCentralStepIndex) :
    Ideal.span (Set.range data.central.generator) =
      clusterFirstCentralIdeal R higher I := by
  simpa [firstCentralStepIndex, centralTransferOutput] using
    data.central.span_eq

end ClusterAlgebraicReductionCertificate

/-! ## Specialization to one ordered-cluster stage -/

namespace RepresentativeClusterSubsequence

/-- Sequence-valued evaluation of the smaller ordered prefix which remains
in the coefficient ring at algebraic stage `j`. -/
def OrderedClusterPrefixAlgebraicStage.coefficientSequenceHom
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ) :
    stage.CoefficientRing →+* (ℕ → ℝ) :=
  MvPolynomial.eval₂Hom base prefixValue

/-- Every retained central iteration inside an actual ordered-cluster stage
has a nonempty displayed real-jet bridge.  This is the stage-indexed form
used when assembling the dependent separated trace. -/
theorem OrderedClusterPrefixAlgebraicStage.nonempty_retainedCentralStepDisplayedData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj)
    (transferData :
      stage.certificate.terminalized.CentralIterationTransferData)
    (k : Fin stage.certificate.terminalized.extraSteps) :
    Nonempty
      (TerminalizedClusterCertificate.RetainedCentralStepDisplayedData
        transferData k) := by
  exact TerminalizedClusterCertificate.nonempty_retainedCentralStepDisplayedData
    transferData k

/-- The first simultaneous central operation of an ordered-prefix stage,
starting from that stage's actual curried `nextIdeal`, has finite displayed
source/central families and exact evaluated identities. -/
theorem OrderedClusterPrefixAlgebraicStage.nonempty_firstCentralStepDisplayedData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj)
    (transferData : stage.certificate.FullCentralTransferData) :
    Nonempty
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
        transferData stage.certificate.firstCentralStepIndex) := by
  exact
    ClusterAlgebraicReductionCertificate.nonempty_fullCentralStepDisplayedData
      transferData stage.certificate.firstCentralStepIndex

end RepresentativeClusterSubsequence

end AbelFormalization
