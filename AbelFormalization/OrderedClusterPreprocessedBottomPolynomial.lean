import AbelFormalization.OrderedClusterBottomPolynomial
import AbelFormalization.OrderedClusterPreprocessedAlgebraicDescent

/-!
# Bottom polynomial after ordered-cluster individual preprocessing

The preprocessed ordered-cluster descent has the same bottom coefficient ring
as the direct descent.  This file transports the maintained height through the
individual preprocessing and simultaneous reduction at the bottom cluster,
then reuses `extract_under_coefficient_equiv` to obtain the scalar polynomial.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

open scoped Polynomial

universe u

/-- The literal bottom-stage certificate in a completed preprocessed descent
inherits the maintained height in its time ideal.  Stating this directly for
`stageAt 0` keeps later quantitative data definitionally tied to the same
certificate used by the flattened transfer trace. -/
theorem bottom_preprocessed_certificate_height
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (hcount : 0 < data.orderedClusterCount)
    (p : ℕ) (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    ((p + (data.orderedCluster ⟨0, hcount⟩).card : ℕ) : ENat) ≤
      (descent.stageAt 0 hcount).certificate.terminalized.timeIdeal.height := by
  let stage := descent.stageAt 0 hcount
  have hnext := stage.tail.prefixHeight_le p (by
    simpa only [data.orderedClusterPrefixSize_top] using hheight)
  rw [data.orderedClusterPrefixSize_succ hcount,
    data.orderedClusterPrefixSize_zero, zero_add] at hnext
  exact hnext.trans ((data.orderedClusterPreprocessedCurriedIdeal_height_le
    R higher ⟨0, hcount⟩ (fixedSteps ⟨0, hcount⟩)
      (fixedOrder ⟨0, hcount⟩) stage.nextIdeal).trans
        stage.certificate.height_monotone)

/-- At the bottom stage of a preprocessed descent, the incoming prefix height
survives the individual balancing operations and the simultaneous reduction
into the terminal time ideal. -/
theorem exists_bottom_preprocessed_certificate_height
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (hcount : 0 < data.orderedClusterCount)
    (p : ℕ) (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    ∃ nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher 1),
    ∃ tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
        fixedSteps fixedOrder initialIdeal 1 hcount nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher 0)
        (data.orderedCluster ⟨0, hcount⟩).card (fun _ ↦ higher)
        (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨0, hcount⟩
          (fixedSteps ⟨0, hcount⟩) (fixedOrder ⟨0, hcount⟩) nextIdeal),
      (((p + (data.orderedCluster ⟨0, hcount⟩).card : ℕ) : ENat) ≤
        certificate.terminalized.timeIdeal.height) := by
  let stage := descent.stageAt 0 hcount
  exact ⟨stage.nextIdeal, stage.tail, stage.certificate,
    bottom_preprocessed_certificate_height descent hcount p hheight⟩

/-- The nonzero time polynomial can be extracted directly from the literal
bottom certificate of the completed descent. -/
theorem exists_bottom_preprocessed_timePolynomial_at_stage
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher
        data.orderedClusterCount)}
    {finalIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent
      (RealAnalyticGerm p) data higher fixedSteps fixedOrder initialIdeal 0
        (Nat.zero_le _) finalIdeal)
    (hcount : 0 < data.orderedClusterCount)
    (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    ∃ i : Fin (data.orderedCluster ⟨0, hcount⟩).card,
    ∃ P : ℝ[X], P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0) i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0) i P ∈
        (descent.stageAt 0 hcount).certificate.terminalized.timeIdeal := by
  let d := (data.orderedCluster ⟨0, hcount⟩).card
  have hd : 0 < d := Finset.card_pos.mpr
    (data.orderedCluster_nonempty ⟨0, hcount⟩)
  let i : Fin d := ⟨0, hd⟩
  let e0 := data.orderedClusterPrefixRingZeroAlgEquiv
    (RealAnalyticGerm p) higher
  let e0R :
      data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0 ≃ₐ[ℝ]
        RealAnalyticGerm p := e0.restrictScalars ℝ
  obtain ⟨P, hP, hPembedded, hPmem⟩ :=
    extract_under_coefficient_equiv p d e0R
      (descent.stageAt 0 hcount).certificate.terminalized.timeIdeal
      (bottom_preprocessed_certificate_height descent hcount p hheight) i
  exact ⟨i, P, hP, hPembedded, hPmem⟩

/-- At the bottom cluster of a preprocessed descent, the maintained height
produces a nonzero scalar polynomial in a retained time variable before the
final contraction. -/
theorem exists_bottom_preprocessed_timePolynomial
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher
        data.orderedClusterCount)}
    {finalIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent
      (RealAnalyticGerm p) data higher fixedSteps fixedOrder initialIdeal 0
        (Nat.zero_le _) finalIdeal)
    (hcount : 0 < data.orderedClusterCount)
    (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    ∃ nextIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 1),
    ∃ tail : OrderedClusterPreprocessedAlgebraicDescent
        (RealAnalyticGerm p) data higher fixedSteps fixedOrder initialIdeal 1
          hcount nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0)
        (data.orderedCluster ⟨0, hcount⟩).card (fun _ ↦ higher)
        (data.orderedClusterPreprocessedCurriedIdeal
          (RealAnalyticGerm p) higher ⟨0, hcount⟩
            (fixedSteps ⟨0, hcount⟩) (fixedOrder ⟨0, hcount⟩) nextIdeal),
    ∃ i : Fin (data.orderedCluster ⟨0, hcount⟩).card,
    ∃ P : ℝ[X], P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0) i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0) i P ∈
        certificate.terminalized.timeIdeal := by
  let stage := descent.stageAt 0 hcount
  obtain ⟨i, P, hP, hPembedded, hPmem⟩ :=
    exists_bottom_preprocessed_timePolynomial_at_stage descent hcount hheight
  exact ⟨stage.nextIdeal, stage.tail, stage.certificate,
    i, P, hP, hPembedded, hPmem⟩

end RepresentativeClusterSubsequence
end AbelFormalization
