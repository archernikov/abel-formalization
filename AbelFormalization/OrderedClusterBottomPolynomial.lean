import AbelFormalization.OrderedClusterPrefixAnalyticDimension
import AbelFormalization.OrderedClusterPrefixZeroRing
import AbelFormalization.AnalyticGermPolynomialExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

open scoped Polynomial

universe u

theorem extract_under_coefficient_equiv
    {R : Type*} [CommRing R] [Algebra ℝ R]
    (p d : ℕ) (e0 : R ≃ₐ[ℝ] RealAnalyticGerm p)
    (I : Ideal (MvPolynomial (Fin d) R))
    (hI : ((p + d : ℕ) : ENat) ≤ I.height) (i : Fin d) :
    ∃ P : ℝ[X], P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ R i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ R i P ∈ I := by
  let e : MvPolynomial (Fin d) R ≃+*
      MvPolynomial (Fin d) (RealAnalyticGerm p) :=
    MvPolynomial.mapEquiv (Fin d) e0.toRingEquiv
  let J : Ideal (MvPolynomial (Fin d) (RealAnalyticGerm p)) := I.map e
  have hJ : ((p + d : ℕ) : ENat) ≤ J.height := by
    dsimp only [J]
    rw [e.height_map I]
    exact hI
  obtain ⟨P, hP, hPembedded, hPmem⟩ :=
    analyticGerm_height_polynomial_extraction p d J hJ i
  have hpre : e.symm
      (scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i P) ∈ I :=
    (Ideal.symm_apply_mem_of_equiv_iff
      (I := I) (f := e)
      (y := scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i P)).2 hPmem
  have hpull : e.symm
      (scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i P) =
      scalarUnivariateEmbedding ℝ R i P := by
    have hcoeff :
        (e0.symm.toRingHom.comp
          (algebraMap ℝ (RealAnalyticGerm p))) =
          algebraMap ℝ R := by
      ext x
      exact e0.symm.commutes x
    dsimp only [e]
    simp only [scalarUnivariateEmbedding, RingHom.comp_apply,
      MvPolynomial.mapEquiv_symm, MvPolynomial.mapEquiv_apply,
      MvPolynomial.map_map]
    change MvPolynomial.map
        (e0.symm.toRingHom.comp (algebraMap ℝ (RealAnalyticGerm p)))
          ((Polynomial.toMvPolynomial i).toRingHom P) =
      MvPolynomial.map (algebraMap ℝ R)
          ((Polynomial.toMvPolynomial i).toRingHom P)
    rw [hcoeff]
  refine ⟨P, hP, ?_, ?_⟩
  · intro hzero
    apply hPembedded
    apply e.symm.injective
    rw [map_zero, hpull, hzero]
  · rwa [hpull] at hpre

private theorem exists_current_certificate
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal k hk stageIdeal)
    (hlt : k < data.orderedClusterCount) :
    ∃ nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (k + 1)),
    ∃ tail : OrderedClusterPrefixAlgebraicDescent R data higher
        initialIdeal (k + 1) hlt nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher k)
        (data.orderedCluster ⟨k, hlt⟩).card (fun _ ↦ higher)
        (data.orderedClusterPrefixCurriedIdeal R higher ⟨k, hlt⟩
          nextIdeal), True := by
  cases descent with
  | top => exact (Nat.lt_irrefl _ hlt).elim
  | @step k hk nextIdeal tail certificate =>
      exact ⟨nextIdeal, tail, certificate, trivial⟩

theorem exists_bottom_certificate_height
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (hcount : 0 < data.orderedClusterCount)
    (p : ℕ) (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    ∃ nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher 1),
    ∃ tail : OrderedClusterPrefixAlgebraicDescent R data higher
        initialIdeal 1 hcount nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher 0)
        (data.orderedCluster ⟨0, hcount⟩).card (fun _ ↦ higher)
        (data.orderedClusterPrefixCurriedIdeal R higher ⟨0, hcount⟩
          nextIdeal),
      (((p + (data.orderedCluster ⟨0, hcount⟩).card : ℕ) : ENat) ≤
        certificate.terminalized.timeIdeal.height) := by
  obtain ⟨nextIdeal, tail, certificate, _⟩ :=
    exists_current_certificate descent hcount
  refine ⟨nextIdeal, tail, certificate, ?_⟩
  have hnext := tail.prefixHeight_le p (by
    simpa only [data.orderedClusterPrefixSize_top] using hheight)
  rw [data.orderedClusterPrefixSize_succ hcount,
    data.orderedClusterPrefixSize_zero, zero_add] at hnext
  exact hnext.trans (by
    rw [← data.orderedClusterPrefixCurriedIdeal_height
      R higher ⟨0, hcount⟩ nextIdeal]
    exact certificate.height_monotone)

/-- At the bottom cluster, the maintained height produces a nonzero scalar
polynomial in one retained time variable before the final contraction. -/
theorem exists_bottom_timePolynomial
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher
        data.orderedClusterCount)}
    {finalIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent
      (RealAnalyticGerm p) data higher initialIdeal 0
        (Nat.zero_le _) finalIdeal)
    (hcount : 0 < data.orderedClusterCount)
    (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    ∃ nextIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 1),
    ∃ tail : OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data higher initialIdeal 1 hcount nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0)
        (data.orderedCluster ⟨0, hcount⟩).card (fun _ ↦ higher)
        (data.orderedClusterPrefixCurriedIdeal
          (RealAnalyticGerm p) higher ⟨0, hcount⟩ nextIdeal),
    ∃ i : Fin (data.orderedCluster ⟨0, hcount⟩).card,
    ∃ P : ℝ[X], P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0) i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0) i P ∈
        certificate.terminalized.timeIdeal := by
  obtain ⟨nextIdeal, tail, certificate, htime⟩ :=
    exists_bottom_certificate_height descent hcount p hheight
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
      certificate.terminalized.timeIdeal htime i
  exact ⟨nextIdeal, tail, certificate, i, P, hP, hPembedded, hPmem⟩

end RepresentativeClusterSubsequence
end AbelFormalization
