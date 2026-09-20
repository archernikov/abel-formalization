import AbelFormalization.OrderedClusterPreprocessedTransferTraceData
import AbelFormalization.OrderedClusterIndividualRealJetEvaluation
import AbelFormalization.HermiteRankTopPrefixClusterValues

/-!
# Real-jet evaluation of the simultaneous part of an ordered-cluster stage

After the individual balancing list has been performed, the active cluster is
curried over the smaller ordered prefix and relabeled by the fixed final
order.  This file gives that active cluster its literal final Abel-time
vector.  At simultaneous operation `r`, its post-log coordinate is the
inverse Abel value after `r + 1` further unit decrements.

The algebraic trace stores every simultaneous input only after the source
translation `q \mapsto q - 1`.  We therefore undo that translation on each
displayed source generator and re-adjoin the unused representatives to each
displayed central generator.  The resulting families span the exact stored
input and output boundaries, and their evaluations are exactly the source
and central real-jet evaluations.  All simultaneous operations use one
sequence-valued evaluation of the smaller-prefix coefficient ring.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

universe u

/-! ## Real-jet evaluation for an arbitrary finite nonempty block set -/

/-- Source-side real-jet evaluation with `Fin h` kept literal.  The existing
quantitative API writes a nonempty block set as `Fin (m + 1)`; this form is
definitionally compatible with it and avoids transporting an ordered
cluster's dependent certificate across its cardinality proof. -/
def finiteRealJetSourceEvaluationHom
    {R : Type u} [CommRing R] {h : ℕ} {A : ℝ → ℝ}
    (c : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (n : ℕ) :
    MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) d (Fin h)) R →+* ℝ :=
  MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
    (fun x ↦ realCentralTransferActualValue A (fun i ↦ u i n) d
      (jets n) x)

/-- Central-side real-jet evaluation with the ordered cluster cardinality
left in its native `Fin h` form. -/
def finiteRealJetCentralEvaluationHom
    {R : Type u} [CommRing R] {h : ℕ}
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ) (n : ℕ) :
    CentralPolynomial R (Fin h) d (Fin h) →+* ℝ :=
  MvPolynomial.eval₂Hom (coefficientEvaluationAt c n)
    (realCentralTransferCentralValue A (fun i ↦ u i n) d)

/-- On a successor-sized block set, the literal-cardinality source hom is
the source hom already used by quantitative transfer. -/
theorem finiteRealJetSourceEvaluationHom_eq_realJetSourceEvaluationHom
    {R : Type u} [CommRing R] {m : ℕ} {A : ℝ → ℝ}
    (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ) (d : Fin (m + 1) → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (n : ℕ) :
    finiteRealJetSourceEvaluationHom c u d jets n =
      realJetSourceEvaluationHom c u d jets n :=
  rfl

/-- On a successor-sized block set, the literal-cardinality central hom is
the central hom already used by quantitative transfer. -/
theorem finiteRealJetCentralEvaluationHom_eq_realJetCentralEvaluationHom
    {R : Type u} [CommRing R] {m : ℕ}
    (A : ℝ → ℝ) (c : R →+* (ℕ → ℝ))
    (u : Fin (m + 1) → ℕ → ℝ) (d : Fin (m + 1) → ℕ)
    (n : ℕ) :
    finiteRealJetCentralEvaluationHom A c u d n =
      realJetCentralEvaluationHom A c u d n :=
  rfl

/-- Active values immediately before one simultaneous logarithmic step.
The independent representative is `E u`; translating the displayed source
back by `q \mapsto q + 1` consequently evaluates it at `exp u`. -/
def simultaneousCentralPreLogActiveAssignment
    {h : ℕ} {A : ℝ → ℝ}
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    ClusterOperationSymbol (Fin h) d → ℕ → ℝ
  | Sum.inl i, n => E (u i n)
  | Sum.inr x, n =>
      realCentralTransferActualValue A (fun i ↦ u i n) d (jets n)
        (Sum.inr x)

/-- Active values immediately after one simultaneous logarithmic step. -/
def simultaneousCentralPostLogActiveAssignment
    {h : ℕ} (A : ℝ → ℝ)
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ) :
    ClusterOperationSymbol (Fin h) d → ℕ → ℝ
  | Sum.inl i, n => u i n
  | Sum.inr x, n =>
      realCentralTransferCentralValue A (fun i ↦ u i n) d x

@[simp]
theorem simultaneousCentralPreLogActiveAssignment_q
    {h : ℕ} {A : ℝ → ℝ}
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (i : Fin h) (n : ℕ) :
    simultaneousCentralPreLogActiveAssignment u d jets (Sum.inl i) n =
      E (u i n) :=
  rfl

@[simp]
theorem simultaneousCentralPreLogActiveAssignment_central
    {h : ℕ} {A : ℝ → ℝ}
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (x : CentralPolynomialIndex (Fin h) d (Fin h)) (n : ℕ) :
    simultaneousCentralPreLogActiveAssignment u d jets (Sum.inr x) n =
      realCentralTransferActualValue A (fun i ↦ u i n) d (jets n)
        (Sum.inr x) :=
  rfl

@[simp]
theorem simultaneousCentralPostLogActiveAssignment_q
    {h : ℕ} (A : ℝ → ℝ)
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (i : Fin h) (n : ℕ) :
    simultaneousCentralPostLogActiveAssignment A u d (Sum.inl i) n =
      u i n :=
  rfl

@[simp]
theorem simultaneousCentralPostLogActiveAssignment_central
    {h : ℕ} (A : ℝ → ℝ)
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (x : CentralPolynomialIndex (Fin h) d (Fin h)) (n : ℕ) :
    simultaneousCentralPostLogActiveAssignment A u d (Sum.inr x) n =
      realCentralTransferCentralValue A (fun i ↦ u i n) d x :=
  rfl

/-- The multi-block pre-log assignment restricts to the existing individual
assignment when the active cluster has one block. -/
theorem simultaneousCentralPreLogActiveAssignment_fin_one
    {A : ℝ → ℝ} (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i)) :
    simultaneousCentralPreLogActiveAssignment u d jets =
      individualCentralPreLogActiveAssignment u d jets :=
  by
    funext z n
    rcases z with i | x <;> rfl

/-- The multi-block post-log assignment similarly extends the existing
individual assignment. -/
theorem simultaneousCentralPostLogActiveAssignment_fin_one
    (A : ℝ → ℝ) (u : Fin 1 → ℕ → ℝ) (d : Fin 1 → ℕ) :
    simultaneousCentralPostLogActiveAssignment A u d =
      individualCentralPostLogActiveAssignment A u d :=
  by
    funext z n
    rcases z with i | x <;> rfl

/-- The source translation used by every full central step. -/
def simultaneousCentralSourceTranslation
    (R : Type u) [CommRing R] {h : ℕ} (d : Fin h → ℕ) :
    MvPolynomial (ClusterOperationSymbol (Fin h) d) R ≃ₐ[R]
      MvPolynomial (ClusterOperationSymbol (Fin h) d) R :=
  polynomialCoordinateTranslation
    (Sum.elim (fun _ : Fin h ↦ (-1 : R))
      (fun _ : CentralPolynomialIndex (Fin h) d (Fin h) ↦ 0))

/-- Undoing source translation at `E u` gives the literal source values at
`exp u`. -/
theorem eval₂Hom_simultaneousCentralSourceTranslation_symm_preLog
    (R : Type u) [CommRing R] {h : ℕ} {A : ℝ → ℝ}
    (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A (u i n) (d i))
    (P : MvPolynomial (ClusterOperationSymbol (Fin h) d) R) (n : ℕ) :
    MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
        (fun z ↦ simultaneousCentralPreLogActiveAssignment u d jets z n)
        ((simultaneousCentralSourceTranslation R d).symm P) =
      finiteRealJetSourceEvaluationHom coefficientEval u d jets n P := by
  let pre := simultaneousCentralPreLogActiveAssignment u d jets
  let lhs : MvPolynomial (ClusterOperationSymbol (Fin h) d) R →+* ℝ :=
    (MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
      (fun z ↦ pre z n)).comp
        (simultaneousCentralSourceTranslation R d).symm.toRingHom
  let rhs := finiteRealJetSourceEvaluationHom coefficientEval u d jets n
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, simultaneousCentralSourceTranslation,
        polynomialCoordinateTranslation]
      dsimp only [rhs, finiteRealJetSourceEvaluationHom]
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    · intro z
      rcases z with i | x
      · simp [lhs, rhs, pre, simultaneousCentralSourceTranslation,
          polynomialCoordinateTranslation, finiteRealJetSourceEvaluationHom,
          realCentralTransferActualValue, E]
      · simp [lhs, rhs, pre, simultaneousCentralSourceTranslation,
          polynomialCoordinateTranslation, finiteRealJetSourceEvaluationHom,
          realCentralTransferActualValue]
  exact RingHom.congr_fun hhom P

/-- Re-adjoining representatives and using post-log active values is exactly
the finite-cardinality central evaluation. -/
theorem eval₂Hom_rename_inr_simultaneousCentralPostLog
    (R : Type u) [CommRing R] {h : ℕ}
    (A : ℝ → ℝ) (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (P : CentralPolynomial R (Fin h) d (Fin h)) (n : ℕ) :
    MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientEval n)
        (fun z ↦ simultaneousCentralPostLogActiveAssignment A u d z n)
        (MvPolynomial.rename Sum.inr P) =
      finiteRealJetCentralEvaluationHom A coefficientEval u d n P := by
  rw [MvPolynomial.eval₂Hom_rename]
  rfl

/-! ## Displayed generators at every full central step -/

namespace ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

/-- Undo the displayed source translation.  This generator belongs to the
literal stored input of the named full central step. -/
def beforeGenerator
    (R : Type u) [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r)
    (k : Fin (data.source.count + 1)) :
    MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R :=
  (simultaneousCentralSourceTranslation R
    (terminalTotalDerivativeCount higher)).symm (data.source.generator k)

/-- Re-adjoin the unused representatives to a displayed central generator. -/
def afterGenerator
    (R : Type u) [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r)
    (k : Fin (data.central.count + 1)) :
    MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R :=
  MvPolynomial.rename Sum.inr (data.central.generator k)

/-- The un-translated displayed source family spans the exact stored input,
for the first operation and every extra retained operation alike. -/
theorem before_span
    (R : Type u) [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r) :
    Ideal.span (Set.range (beforeGenerator R data)) =
      certificate.centralTransferInput r := by
  let translate := simultaneousCentralSourceTranslation R
    (terminalTotalDerivativeCount higher)
  change Ideal.span (Set.range (fun k ↦
    translate.symm.toRingHom (data.source.generator k))) = _
  calc
    Ideal.span (Set.range (fun k ↦
        translate.symm.toRingHom (data.source.generator k))) =
        (Ideal.span (Set.range data.source.generator)).map
          translate.symm.toRingHom := span_range_map_eq _ _
    _ = ((certificate.centralTransferInput r).map translate.toRingHom).map
          translate.symm.toRingHom := by
      simpa [translate, simultaneousCentralSourceTranslation] using
        congrArg (fun J ↦ J.map translate.symm.toRingHom)
          data.source.span_eq
    _ = certificate.centralTransferInput r :=
      Ideal.map_of_equiv translate.toRingEquiv

/-- The re-extended central family spans the exact central output with fresh
unused representatives adjoined. -/
theorem after_span
    (R : Type u) [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r) :
    Ideal.span (Set.range (afterGenerator R data)) =
      unusedPolynomialExtension (Fin h)
        (certificate.centralTransferOutput r) := by
  calc
    Ideal.span (Set.range (afterGenerator R data)) =
        unusedPolynomialExtension (Fin h)
          (Ideal.span (Set.range data.central.generator)) :=
      span_rename_inr_range_eq_unusedPolynomialExtension data.central.generator
    _ = unusedPolynomialExtension (Fin h)
          (certificate.centralTransferOutput r) := by rw [data.central.span_eq]

/-- Exact before/source evaluation for any displayed full central step. -/
theorem eval_beforeGenerator_preLog
    (R : Type u) [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r)
    {A : ℝ → ℝ} (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (u i n) (terminalTotalDerivativeCount higher i))
    (k : Fin (data.source.count + 1)) (n : ℕ) :
    MvPolynomial.eval₂Hom coefficientEval
        (simultaneousCentralPreLogActiveAssignment u
          (terminalTotalDerivativeCount higher) jets)
        (beforeGenerator R data k) n =
      finiteRealJetSourceEvaluationHom coefficientEval u
        (terminalTotalDerivativeCount higher) jets n
        (data.source.generator k) := by
  rw [mvPolynomial_eval₂Hom_pi_apply]
  exact eval₂Hom_simultaneousCentralSourceTranslation_symm_preLog
    R coefficientEval u (terminalTotalDerivativeCount higher) jets
      (data.source.generator k) n

/-- Exact after/central evaluation for any displayed full central step. -/
theorem eval_afterGenerator_postLog
    (R : Type u) [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (ClusterOperationSymbol (Fin h) (terminalTotalDerivativeCount higher)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    {transferData : certificate.FullCentralTransferData}
    {r : Fin (certificate.terminalized.extraSteps + 1)}
    (data : FullCentralStepDisplayedData transferData r)
    (A : ℝ → ℝ) (coefficientEval : R →+* (ℕ → ℝ))
    (u : Fin h → ℕ → ℝ)
    (k : Fin (data.central.count + 1)) (n : ℕ) :
    MvPolynomial.eval₂Hom coefficientEval
        (simultaneousCentralPostLogActiveAssignment A u
          (terminalTotalDerivativeCount higher))
        (afterGenerator R data k) n =
      finiteRealJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount higher) n
        (data.central.generator k) := by
  rw [mvPolynomial_eval₂Hom_pi_apply]
  exact eval₂Hom_rename_inr_simultaneousCentralPostLog
    R A coefficientEval u (terminalTotalDerivativeCount higher)
      (data.central.generator k) n

end ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData

/-! ## Actual ordered-cluster values -/

namespace RepresentativeClusterSubsequence

/-- The balanced Abel time in final active-coordinate order.  Final position
`i` contains the original balancing coordinate `finalOrder i`, in agreement
with `orderedClusterFinalOrderAlgEquiv_X_q`. -/
def orderedClusterPostBalancingFinalOrderTime
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1))) :
    Fin (data.orderedCluster c).card → ℕ → ℝ :=
  fun i n ↦ clusterShiftedTimes (rawTime n) fixedSteps
    (finalOrder ((data.orderedClusterBalancingToActiveEquiv c).symm i))

@[simp]
theorem orderedClusterPostBalancingFinalOrderTime_apply
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedClusterTailSize c + 1)) (n : ℕ) :
    data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
        finalOrder (data.orderedClusterBalancingToActiveEquiv c i) n =
      clusterShiftedTimes (rawTime n) fixedSteps (finalOrder i) := by
  simp [orderedClusterPostBalancingFinalOrderTime]

/-- The post-log active value for simultaneous operation `r`.  Operation
zero starts one unit below the balanced individual output; every extra
retained operation lowers all active Abel times by one further unit. -/
def orderedClusterSimultaneousPostLogScale
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (r : ℕ) : Fin (data.orderedCluster c).card → ℕ → ℝ :=
  fun i n ↦ inverse A
    (data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
      finalOrder i n - ((r + 1 : ℕ) : ℝ))

@[simp]
theorem orderedClusterSimultaneousPostLogScale_apply
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (r : ℕ) (i : Fin (data.orderedClusterTailSize c + 1)) (n : ℕ) :
    data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
        finalOrder r (data.orderedClusterBalancingToActiveEquiv c i) n =
      inverse A (clusterShiftedTimes (rawTime n) fixedSteps (finalOrder i) -
        ((r + 1 : ℕ) : ℝ)) := by
  simp [orderedClusterSimultaneousPostLogScale]

/-- The first simultaneous operation starts one Abel-time unit below the
final individually balanced vector. -/
@[simp]
theorem orderedClusterSimultaneousPostLogScale_zero
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
        finalOrder 0 i n =
      inverse A
        (data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
          finalOrder i n - 1) := by
  simp [orderedClusterSimultaneousPostLogScale]

/-- Extra retained operation `r` starts `r + 2` Abel-time units below the
final individually balanced vector. -/
theorem orderedClusterSimultaneousPostLogScale_succ
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (A : ℝ → ℝ)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (r : ℕ) (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
        finalOrder (r + 1) i n =
      inverse A
        (data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
          finalOrder i n - ((r + 2 : ℕ) : ℝ)) := by
  simp only [orderedClusterSimultaneousPostLogScale]

/-- Before simultaneous operation `r`, the representative coordinate is the
inverse Abel value after exactly `r` simultaneous decrements. -/
theorem simultaneousCentralPreLogActiveAssignment_q_eq_boundary
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (higher : ℕ)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (r : ℕ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
        finalOrder r i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦ higher) i))
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    simultaneousCentralPreLogActiveAssignment
        (data.orderedClusterSimultaneousPostLogScale c A rawTime fixedSteps
          finalOrder r)
        (terminalTotalDerivativeCount
          (fun _ : Fin (data.orderedCluster c).card ↦ higher)) jets
        (Sum.inl i) n =
      inverse A
        (data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
          finalOrder i n - (r : ℝ)) := by
  rw [simultaneousCentralPreLogActiveAssignment_q]
  unfold orderedClusterSimultaneousPostLogScale
  calc
    E (inverse A
        (data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
          finalOrder i n - ((r + 1 : ℕ) : ℝ))) =
        inverse A
          ((data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
            finalOrder i n - ((r + 1 : ℕ) : ℝ)) + 1) :=
      (hA.inverse_add_one _).symm
    _ = inverse A
        (data.orderedClusterPostBalancingFinalOrderTime c rawTime fixedSteps
          finalOrder i n - (r : ℝ)) := by
      congr 1
      push_cast
      ring

/-! ## The common smaller-prefix coefficient evaluation -/

/-- Sequence-valued evaluation of the smaller prefix which is the
coefficient ring throughout all simultaneous operations of a preprocessed
stage. -/
def OrderedClusterPreprocessedAlgebraicStage.coefficientSequenceHom
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj)
    (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ) :
    data.OrderedClusterPrefixRing R higher j →+* (ℕ → ℝ) :=
  MvPolynomial.eval₂Hom base prefixValue

/-- The concrete Hermite assignment on the smaller prefix, now viewed as a
sequence-valued assignment. -/
def paperRankHermiteOrderedClusterSmallerPrefixSequenceValue
    {ι : Type*} {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : ℕ → PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock c.val)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) c.val) →
      ℕ → ℝ :=
  fun z n ↦ paperRankHermitePrefixValue data D representative offset S B F
    (sw n) c.val z

/-- The shared smaller-prefix coefficient hom specialized to the concrete
Hermite values.  The base-coefficient hom is explicit so the construction
also applies after a further subsequence or coefficient specialization. -/
def paperRankHermiteOrderedClusterSmallerPrefixCoefficientSequenceHom
    {ι : Type*} {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : ℕ → PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (base : ℝ →+* (ℕ → ℝ)) :
    data.OrderedClusterPrefixRing ℝ (paperRankHermiteHigherCount S) c.val
        →+* (ℕ → ℝ) :=
  MvPolynomial.eval₂Hom base
    (paperRankHermiteOrderedClusterSmallerPrefixSequenceValue data D
      representative offset S B F sw c)

/-- The canonical inclusion of real constants as constant real sequences. -/
def constantRealSequenceRingHom : ℝ →+* (ℕ → ℝ) :=
  RingHom.pi (fun _ : ℕ ↦ RingHom.id ℝ)

@[simp]
theorem constantRealSequenceRingHom_apply (x : ℝ) (n : ℕ) :
    constantRealSequenceRingHom x n = x :=
  rfl

/-- Fully concrete Hermite coefficient evaluation with constant real base
coefficients. -/
def paperRankHermiteOrderedClusterSmallerPrefixEvaluationHom
    {ι : Type*} {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : ℕ → PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount) :
    data.OrderedClusterPrefixRing ℝ (paperRankHermiteHigherCount S) c.val
        →+* (ℕ → ℝ) :=
  paperRankHermiteOrderedClusterSmallerPrefixCoefficientSequenceHom data D
    representative offset S B F sw c constantRealSequenceRingHom

/-! ## Evaluation at one preprocessed ordered-cluster stage -/

namespace OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData

variable {R : Type u} [CommRing R]
variable {m : ℕ} {time : ℕ → Fin m → ℝ}
variable {data : RepresentativeClusterSubsequence time}
variable {higher : ℕ}
variable {fixedSteps : data.OrderedClusterIndividualStepPlan}
variable {fixedOrder : data.OrderedClusterFinalOrderPlan}
variable {initialIdeal : Ideal
  (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
variable {j : ℕ} {hj : j < data.orderedClusterCount}
variable {stage : OrderedClusterPreprocessedAlgebraicStage R data higher
  fixedSteps fixedOrder initialIdeal j hj}

/-- Pull an un-translated simultaneous source generator back through the
final-order relabeling and ordered-prefix curry.  At the first simultaneous
index these are literal generators in the flat individual-output ring. -/
def flatBeforeGenerator
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    (k : Fin ((trace.simultaneousDisplayed r).source.count + 1)) :
    data.OrderedClusterPrefixRing R higher (j + 1) :=
  (data.orderedClusterPrefixCurryAlgEquiv R ⟨j, hj⟩ (higher + 1)).symm
    ((data.orderedClusterFinalOrderAlgEquiv
      (data.OrderedClusterPrefixRing R higher j) higher ⟨j, hj⟩
      (fixedOrder ⟨j, hj⟩)).symm
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
        (data.OrderedClusterPrefixRing R higher j)
        (trace.simultaneousDisplayed r) k))

/-- The pulled-back family at an arbitrary simultaneous index spans the
stored input transported back to the flat `(j+1)`-prefix ring. -/
theorem flatBefore_span
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1)) :
    Ideal.span (Set.range (trace.flatBeforeGenerator r)) =
      ((stage.certificate.centralTransferInput r).map
        (data.orderedClusterFinalOrderAlgEquiv
          (data.OrderedClusterPrefixRing R higher j) higher ⟨j, hj⟩
          (fixedOrder ⟨j, hj⟩)).symm.toRingHom).map
        (data.orderedClusterPrefixCurryAlgEquiv R ⟨j, hj⟩
          (higher + 1)).symm.toRingHom := by
  let reorder := data.orderedClusterFinalOrderAlgEquiv
    (data.OrderedClusterPrefixRing R higher j) higher ⟨j, hj⟩
      (fixedOrder ⟨j, hj⟩)
  let curry := data.orderedClusterPrefixCurryAlgEquiv R ⟨j, hj⟩
    (higher + 1)
  change Ideal.span (Set.range (fun k ↦ curry.symm.toRingHom
    (reorder.symm.toRingHom
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
        (data.OrderedClusterPrefixRing R higher j)
        (trace.simultaneousDisplayed r) k)))) = _
  calc
    _ = (Ideal.span (Set.range (fun k ↦ reorder.symm.toRingHom
          (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
            (data.OrderedClusterPrefixRing R higher j)
            (trace.simultaneousDisplayed r) k)))).map
          curry.symm.toRingHom := span_range_map_eq _ _
    _ = ((Ideal.span (Set.range
          (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
            (data.OrderedClusterPrefixRing R higher j)
            (trace.simultaneousDisplayed r)))).map
          reorder.symm.toRingHom).map curry.symm.toRingHom := by
      rw [span_range_map_eq]
    _ = _ := by
      rw [(trace.simultaneousDisplayed r).before_span
        (data.OrderedClusterPrefixRing R higher j)]

/-- Pulling back the first displayed source family cancels translation,
final-order relabeling, and currying, leaving exactly the terminal boundary
of the individual preprocessing trace. -/
theorem firstFlatBefore_span
    (trace : stage.FullTransferTraceData) :
    Ideal.span (Set.range (trace.flatBeforeGenerator
      stage.certificate.firstCentralStepIndex)) =
      stage.preprocessingOutput := by
  let reorder := data.orderedClusterFinalOrderAlgEquiv
    (data.OrderedClusterPrefixRing R higher j) higher ⟨j, hj⟩
      (fixedOrder ⟨j, hj⟩)
  let curry := data.orderedClusterPrefixCurryAlgEquiv R ⟨j, hj⟩
    (higher + 1)
  rw [trace.flatBefore_span]
  change ((stage.reductionInput.map reorder.symm.toRingHom).map
    curry.symm.toRingHom) = stage.preprocessingOutput
  change (((((stage.preprocessingOutput).map curry.toRingHom).map
    reorder.toRingHom).map reorder.symm.toRingHom).map
      curry.symm.toRingHom) = stage.preprocessingOutput
  have hreorder :
      (((stage.preprocessingOutput).map curry.toRingHom).map
        reorder.toRingHom).map reorder.symm.toRingHom =
      (stage.preprocessingOutput).map curry.toRingHom :=
    Ideal.map_of_equiv reorder.toRingEquiv
  rw [hreorder]
  exact Ideal.map_of_equiv curry.toRingEquiv

/-- The un-translated source family at any simultaneous index spans that
index's exact stored input. -/
theorem simultaneousBefore_span
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1)) :
    Ideal.span (Set.range
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
        (data.OrderedClusterPrefixRing R higher j)
        (trace.simultaneousDisplayed r))) =
      stage.certificate.centralTransferInput r :=
  (trace.simultaneousDisplayed r).before_span
    (data.OrderedClusterPrefixRing R higher j)

/-- At index zero the un-translated source family starts at the actual
curried, final-order-relabeled output of individual preprocessing. -/
theorem firstSimultaneousBefore_span
    (trace : stage.FullTransferTraceData) :
    Ideal.span (Set.range
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
        (data.OrderedClusterPrefixRing R higher j) (trace.simultaneousDisplayed
          stage.certificate.firstCentralStepIndex))) =
      stage.reductionInput :=
  (trace.simultaneousBefore_span
    stage.certificate.firstCentralStepIndex).trans
      trace.simultaneous_first_input

/-- At successor index `i.succ`, the un-translated source family spans the
stored unused-representative input of retained iteration `i`. -/
theorem extraRetainedBefore_span
    (trace : stage.FullTransferTraceData)
    (i : Fin stage.certificate.terminalized.extraSteps) :
    Ideal.span (Set.range
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
        (data.OrderedClusterPrefixRing R higher j)
        (trace.simultaneousDisplayed i.succ))) =
      stage.certificate.terminalized.centralIterationTransferInput i := by
  simpa [ClusterAlgebraicReductionCertificate.centralTransferInput] using
    trace.simultaneousBefore_span i.succ

/-- Exact before/source evaluation at an arbitrary simultaneous operation,
using the one smaller-prefix coefficient hom shared by the whole stage. -/
theorem eval_simultaneousBeforeGenerator_preLog
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    {A : ℝ → ℝ} (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (k : Fin ((trace.simultaneousDisplayed r).source.count + 1)) (n : ℕ) :
    MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPreLogActiveAssignment
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets)
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed r) k) n =
      finiteRealJetSourceEvaluationHom
        (stage.coefficientSequenceHom base prefixValue)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets n
        ((trace.simultaneousDisplayed r).source.generator k) := by
  exact (trace.simultaneousDisplayed r).eval_beforeGenerator_preLog
    (data.OrderedClusterPrefixRing R higher j)
    (stage.coefficientSequenceHom base prefixValue)
    (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
    jets k n

/-- Exact after/central evaluation at an arbitrary simultaneous operation,
with the same smaller-prefix coefficient hom. -/
theorem eval_simultaneousAfterGenerator_postLog
    (trace : stage.FullTransferTraceData)
    (r : Fin (stage.certificate.terminalized.extraSteps + 1))
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (k : Fin ((trace.simultaneousDisplayed r).central.count + 1)) (n : ℕ) :
    MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPostLogActiveAssignment A
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed r) k) n =
      finiteRealJetCentralEvaluationHom A
        (stage.coefficientSequenceHom base prefixValue)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) n
        ((trace.simultaneousDisplayed r).central.generator k) := by
  exact (trace.simultaneousDisplayed r).eval_afterGenerator_postLog
    (data.OrderedClusterPrefixRing R higher j) A
    (stage.coefficientSequenceHom base prefixValue)
    (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) r.val)
    k n

/-- Source-side evaluation for the distinguished first simultaneous
operation.  Its active scale is the final balanced vector shifted by one. -/
theorem eval_firstSimultaneousBeforeGenerator_preLog
    (trace : stage.FullTransferTraceData)
    {A : ℝ → ℝ} (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0 i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) i))
    (k : Fin ((trace.simultaneousDisplayed
      stage.certificate.firstCentralStepIndex).source.count + 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPreLogActiveAssignment
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets)
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed
            stage.certificate.firstCentralStepIndex) k) n =
      finiteRealJetSourceEvaluationHom
        (stage.coefficientSequenceHom base prefixValue)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets n
        ((trace.simultaneousDisplayed
          stage.certificate.firstCentralStepIndex).source.generator k) := by
  exact trace.eval_simultaneousBeforeGenerator_preLog
    stage.certificate.firstCentralStepIndex base prefixValue rawTime jets k n

/-- Central-side evaluation for the distinguished first simultaneous
operation. -/
theorem eval_firstSimultaneousAfterGenerator_postLog
    (trace : stage.FullTransferTraceData)
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (k : Fin ((trace.simultaneousDisplayed
      stage.certificate.firstCentralStepIndex).central.count + 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPostLogActiveAssignment A
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed
            stage.certificate.firstCentralStepIndex) k) n =
      finiteRealJetCentralEvaluationHom A
        (stage.coefficientSequenceHom base prefixValue)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) 0)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) n
        ((trace.simultaneousDisplayed
          stage.certificate.firstCentralStepIndex).central.generator k) := by
  exact trace.eval_simultaneousAfterGenerator_postLog
    stage.certificate.firstCentralStepIndex A base prefixValue rawTime k n

/-- Source-side evaluation for arbitrary extra retained operation `i`; its
post-log scale is the final balanced vector shifted by `i + 2`. -/
theorem eval_extraRetainedBeforeGenerator_preLog
    (trace : stage.FullTransferTraceData)
    (i : Fin stage.certificate.terminalized.extraSteps)
    {A : ℝ → ℝ} (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (jets : ∀ n a, RealCentralJetSubstitutionData A
      (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
        (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1) a n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher) a))
    (k : Fin ((trace.simultaneousDisplayed i.succ).source.count + 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPreLogActiveAssignment
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets)
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.beforeGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed i.succ) k) n =
      finiteRealJetSourceEvaluationHom
        (stage.coefficientSequenceHom base prefixValue)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) jets n
        ((trace.simultaneousDisplayed i.succ).source.generator k) := by
  exact trace.eval_simultaneousBeforeGenerator_preLog
    i.succ base prefixValue rawTime jets k n

/-- Central-side evaluation for arbitrary extra retained operation `i`. -/
theorem eval_extraRetainedAfterGenerator_postLog
    (trace : stage.FullTransferTraceData)
    (i : Fin stage.certificate.terminalized.extraSteps)
    (A : ℝ → ℝ) (base : R →+* (ℕ → ℝ))
    (prefixValue : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock j)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) j) →
        ℕ → ℝ)
    (rawTime : ℕ →
      Fin (data.orderedClusterTailSize ⟨j, hj⟩ + 1) → ℝ)
    (k : Fin ((trace.simultaneousDisplayed i.succ).central.count + 1))
    (n : ℕ) :
    MvPolynomial.eval₂Hom
        (stage.coefficientSequenceHom base prefixValue)
        (simultaneousCentralPostLogActiveAssignment A
          (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
            (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing R higher j)
          (trace.simultaneousDisplayed i.succ) k) n =
      finiteRealJetCentralEvaluationHom A
        (stage.coefficientSequenceHom base prefixValue)
        (data.orderedClusterSimultaneousPostLogScale ⟨j, hj⟩ A rawTime
          (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) (i.val + 1))
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster ⟨j, hj⟩).card ↦ higher)) n
        ((trace.simultaneousDisplayed i.succ).central.generator k) := by
  exact trace.eval_simultaneousAfterGenerator_postLog
    i.succ A base prefixValue rawTime k n

end OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData

end RepresentativeClusterSubsequence
end AbelFormalization
