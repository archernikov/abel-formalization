import AbelFormalization.HermiteBeforeRankEquation
import AbelFormalization.PaperRankHermiteCount
import AbelFormalization.OrderedClusterBottomPolynomial

/-!
# From full Hermite rank elimination to ordered-cluster descent

This module identifies the retained polynomial ring produced by the corrected
Hermite-before-rank elimination with the full ordered-cluster prefix ring.  It
then transports the rank ideal across that equivalence, preserving its height,
and starts the existing ordered-cluster algebraic descent.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

open scoped Polynomial

variable {ι : Type*}

/-- The variable equivalence underlying the full-Hermite top-prefix algebra
equivalence. -/
def paperRankHermiteTopPrefixSymbolEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) :
    PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)) ≃
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) data.orderedClusterCount) :=
  (paperRankRetainedFlatHermiteEquiv m
    (paperRankHermitePositiveDerivativeCount S)).trans
    (clusterOperationSymbolEquiv
      data.orderedClusterPrefixTopEquiv
      (fun _ : Fin m ↦ paperRankHermitePositiveDerivativeCount S)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount S + 1) data.orderedClusterCount)
      (fun _ ↦ (paperRankHermiteHigherCount_add_one S).symm))

/-- The full-Hermite retained ring used by paper-rank elimination is the top
ordered-cluster prefix ring.  The count comparison is built into the type of
the equivalence. -/
def paperRankHermiteTopPrefixAlgEquiv
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) :
    MvPolynomial
        (PaperRankRetainedSymbols m
          (m * (paperRankHermitePositiveDerivativeCount S + 1))) R ≃ₐ[R]
      data.OrderedClusterPrefixRing R (paperRankHermiteHigherCount S)
        data.orderedClusterCount :=
  MvPolynomial.renameEquiv R (paperRankHermiteTopPrefixSymbolEquiv data S)

/-- The ordered top-prefix ideal obtained from a retained paper-rank ideal by
the full-Hermite reindexing. -/
def paperRankHermiteTopPrefixIdeal
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R)) :
    Ideal (data.OrderedClusterPrefixRing R
      (paperRankHermiteHigherCount S) data.orderedClusterCount) :=
  I.map (data.paperRankHermiteTopPrefixAlgEquiv R S).toRingHom

/-- Relabeling the full-Hermite retained variables as the ordered top prefix
preserves ideal height exactly. -/
@[simp]
theorem paperRankHermiteTopPrefixIdeal_height
    (R : Type*) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R)) :
    (data.paperRankHermiteTopPrefixIdeal R S I).height = I.height := by
  exact (data.paperRankHermiteTopPrefixAlgEquiv R S).toRingEquiv.height_map I

/-- Membership in the mapped top-prefix ideal is exactly membership in the
original retained paper-rank ideal after applying the reindexing. -/
@[simp]
theorem paperRankHermiteTopPrefixAlgEquiv_apply_mem_iff
    (R : Type*) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R))
    (f : MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R) :
    data.paperRankHermiteTopPrefixAlgEquiv R S f ∈
        data.paperRankHermiteTopPrefixIdeal R S I ↔
      f ∈ I := by
  exact Ideal.apply_mem_of_equiv_iff
    (I := I)
    (f := (data.paperRankHermiteTopPrefixAlgEquiv R S).toRingEquiv)
    (x := f)

/-- Every full-Hermite retained rank ideal over real-analytic germs starts a
coherent algebraic descent through all ordered cluster prefixes. -/
theorem exists_paperRankHermiteTopPrefixAlgebraicDescent
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))) :
    ∃ finalIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 0),
      Nonempty (OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data (paperRankHermiteHigherCount S)
        (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
        0 (Nat.zero_le _) finalIdeal) :=
  data.exists_orderedClusterPrefixAlgebraicDescent_realAnalyticGerm
    (paperRankHermiteHigherCount S)
    (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)

/-- The height surviving after the full ordered-cluster descent can be stated
directly in terms of the original retained paper-rank ideal. -/
theorem exists_paperRankHermiteTopPrefixAlgebraicDescent_height
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)))
    (q : ℕ) (hheight : ((q + m : ℕ) : ENat) ≤ I.height) :
    ∃ finalIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 0),
      Nonempty (OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data (paperRankHermiteHigherCount S)
        (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
        0 (Nat.zero_le _) finalIdeal) ∧
      (q : ENat) ≤ finalIdeal.height := by
  obtain ⟨finalIdeal, ⟨descent⟩⟩ :=
    data.exists_paperRankHermiteTopPrefixAlgebraicDescent S I
  have htop : ((q + m : ℕ) : ENat) ≤
      (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I).height := by
    simpa only [paperRankHermiteTopPrefixIdeal_height] using hheight
  exact ⟨finalIdeal, ⟨descent⟩, descent.finalHeight_le q htop⟩

/-- If there is a bottom cluster, the height output of paper-rank elimination
feeds the terminal extraction theorem and yields a nonzero scalar polynomial
in one retained time variable. -/
theorem exists_paperRankHermiteBottomTimePolynomial
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)))
    (hcount : 0 < data.orderedClusterCount)
    (hheight : ((p + m : ℕ) : ENat) ≤ I.height) :
    ∃ nextIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 1),
    ∃ _tail : OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data (paperRankHermiteHigherCount S)
        (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
        1 hcount nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 0)
        (data.orderedCluster ⟨0, hcount⟩).card
        (fun _ ↦ paperRankHermiteHigherCount S)
        (data.orderedClusterPrefixCurriedIdeal
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
          ⟨0, hcount⟩ nextIdeal),
    ∃ i : Fin (data.orderedCluster ⟨0, hcount⟩).card,
    ∃ P : ℝ[X], P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount S) 0) i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount S) 0) i P ∈
        certificate.terminalized.timeIdeal := by
  obtain ⟨finalIdeal, ⟨descent⟩⟩ :=
    data.exists_paperRankHermiteTopPrefixAlgebraicDescent S I
  have htop : ((p + m : ℕ) : ENat) ≤
      (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I).height := by
    simpa only [paperRankHermiteTopPrefixIdeal_height] using hheight
  exact data.exists_bottom_timePolynomial descent hcount htop

end RepresentativeClusterSubsequence

open scoped Polynomial

/-- A finite restricted expression system over an Abel function reaches the
bottom ordered cluster after the corrected Hermite-before-rank elimination.
The result retains the polynomial compression, the original rank-height
bound, exact height preservation under the top-prefix reindexing, the full
descent tail, and the terminal nonzero scalar time polynomial. -/
theorem IsAbel.exists_restrictedBaseHermiteRankTopPrefixBottomTimePolynomial
    {ι : Type*} {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (hcount : 0 < data.orderedClusterCount) :
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
    ∃ I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)),
      (∀ i, restrictedPaperPolynomialValue A D representative offset
        (restrictedJetEnumeration S) (Q i) = F i) ∧
      ((m + p : ℕ) : ENat) ≤ I.height ∧
      (data.paperRankHermiteTopPrefixIdeal
        (RealAnalyticGerm p) S I).height = I.height ∧
    ∃ nextIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 1),
    ∃ _tail : RepresentativeClusterSubsequence.OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data (paperRankHermiteHigherCount S)
        (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
        1 hcount nextIdeal,
    ∃ certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount S) 0)
        (data.orderedCluster ⟨0, hcount⟩).card
        (fun _ ↦ paperRankHermiteHigherCount S)
        (data.orderedClusterPrefixCurriedIdeal
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S)
          ⟨0, hcount⟩ nextIdeal),
    ∃ i : Fin (data.orderedCluster ⟨0, hcount⟩).card,
    ∃ P : ℝ[X], P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount S) 0) i P ≠ 0 ∧
      scalarUnivariateEmbedding ℝ
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount S) 0) i P ∈
        certificate.terminalized.timeIdeal := by
  obtain ⟨S, Q, I, hQ, hheight⟩ :=
    hA.exists_restrictedBaseHermiteBeforeRankElimination_height
      D h0D representative offset R F hF
  have hbottom : ((p + m : ℕ) : ENat) ≤ I.height := by
    simpa only [Nat.add_comm] using hheight
  obtain ⟨nextIdeal, tail, certificate, i, P, hP, hPembedded, hPmem⟩ :=
    data.exists_paperRankHermiteBottomTimePolynomial
      S I hcount hbottom
  exact ⟨S, Q, I, hQ, hheight,
    data.paperRankHermiteTopPrefixIdeal_height (RealAnalyticGerm p) S I,
    nextIdeal, tail, certificate, i, P, hP, hPembedded, hPmem⟩

end AbelFormalization
