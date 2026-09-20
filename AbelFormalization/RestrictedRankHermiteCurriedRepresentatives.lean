import AbelFormalization.RestrictedRankHermiteClusterRepresentatives

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

universe u v w

def splitClusterCurryCoefficientIndex
    (Active : Type v) (Coeff : Type w)
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (a : ClusterOperationSymbol Active dActive →₀ ℕ)
    (c : ClusterOperationSymbol Coeff dCoeff →₀ ℕ) :
    SplitClusterBlockSymbol Active Coeff dActive dCoeff →₀ ℕ :=
  Finsupp.mapDomain
    (splitClusterBlockSymbolEquiv Active Coeff dActive dCoeff).symm
    ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm (a, c))

theorem splitClusterCurryAlgEquiv_coeff_coeff
    (R : Type u) [CommSemiring R]
    (Active : Type v) (Coeff : Type w)
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (P : MvPolynomial
      (SplitClusterBlockSymbol Active Coeff dActive dCoeff) R)
    (a : ClusterOperationSymbol Active dActive →₀ ℕ)
    (c : ClusterOperationSymbol Coeff dCoeff →₀ ℕ) :
    ((splitClusterCurryAlgEquiv R Active Coeff dActive dCoeff P).coeff a).coeff c =
      P.coeff (splitClusterCurryCoefficientIndex Active Coeff dActive dCoeff a c) := by
  let e := splitClusterBlockSymbolEquiv Active Coeff dActive dCoeff
  let join : (ClusterOperationSymbol Active dActive ⊕
      ClusterOperationSymbol Coeff dCoeff) →₀ ℕ :=
    (Finsupp.sumFinsuppAddEquivProdFinsupp).symm (a, c)
  have hsum := terminalSumAlgEquiv_symm_coeff
    (splitClusterCurryAlgEquiv R Active Coeff dActive dCoeff P) a c
  have hinv :
      (MvPolynomial.sumAlgEquiv R
        (ClusterOperationSymbol Active dActive)
        (ClusterOperationSymbol Coeff dCoeff)).symm
          (splitClusterCurryAlgEquiv R Active Coeff dActive dCoeff P) =
        MvPolynomial.rename e P := by
    simp [splitClusterCurryAlgEquiv, e]
  rw [hinv] at hsum
  have hcoeff := MvPolynomial.coeff_rename_mapDomain e e.injective P
    (Finsupp.mapDomain e.symm join)
  have hmap : Finsupp.mapDomain e
      (Finsupp.mapDomain e.symm join) = join := by
    rw [← Finsupp.mapDomain_comp]
    ext x
    simp
  rw [hmap] at hcoeff
  exact hsum.symm.trans (by
    simpa only [join, e, splitClusterCurryCoefficientIndex] using hcoeff)

/-- Map nested polynomials over analytic germs to germs of nested real
polynomials.  The definition flattens, applies the ordinary analytic
polynomial-germ map, and curries pointwise again. -/
def analyticSplitClusterCurriedPolynomialGermHom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (Active : Type v) (Coeff : Type w)
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ) :
    MvPolynomial (ClusterOperationSymbol Active dActive)
        (MvPolynomial (ClusterOperationSymbol Coeff dCoeff)
          (AnalyticGermAt x)) →+*
      Germ (𝓝 x)
        (MvPolynomial (ClusterOperationSymbol Active dActive)
          (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ)) :=
  (germMapRingHom (𝓝 x)
      (splitClusterCurryAlgEquiv ℝ Active Coeff dActive dCoeff).toRingHom).comp
    ((analyticPolynomialGermHom
      (ι := SplitClusterBlockSymbol Active Coeff dActive dCoeff) x).comp
      (splitClusterCurryAlgEquiv (AnalyticGermAt x)
        Active Coeff dActive dCoeff).symm.toRingHom)

/-- A finite family of flat analytic-germ polynomials has simultaneous
pointwise nested representatives after cluster currying.  Their nested
supports remain inside the corresponding fixed germ supports, and every
scalar coefficient is analytic on one common neighborhood. -/
theorem exists_analyticSplitClusterCurriedRepresentatives
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite κ]
    (x : E) (Active : Type v) (Coeff : Type w)
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (P : κ → MvPolynomial
      (SplitClusterBlockSymbol Active Coeff dActive dCoeff)
        (AnalyticGermAt x)) :
    ∃ F : κ → E →
        MvPolynomial (ClusterOperationSymbol Active dActive)
          (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ),
    ∃ U : Set E,
      IsOpen U ∧ x ∈ U ∧
      (∀ i y a, ((F i y).coeff a).support ⊆
        ((splitClusterCurryAlgEquiv (AnalyticGermAt x)
          Active Coeff dActive dCoeff (P i)).coeff a).support) ∧
      (∀ i a c, AnalyticOnNhd ℝ
        (fun y => ((F i y).coeff a).coeff c) U) ∧
      ∀ i,
        analyticSplitClusterCurriedPolynomialGermHom x
            Active Coeff dActive dCoeff
            (splitClusterCurryAlgEquiv (AnalyticGermAt x)
              Active Coeff dActive dCoeff (P i)) =
          (F i : Germ (𝓝 x)
            (MvPolynomial (ClusterOperationSymbol Active dActive)
              (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ))) := by
  obtain ⟨H, U, hUopen, hxU, hsupport, hanalytic, hH⟩ :=
    exists_analyticPolynomialRepresentatives x P
  let F : κ → E →
      MvPolynomial (ClusterOperationSymbol Active dActive)
        (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ) :=
    fun i y => splitClusterCurryAlgEquiv ℝ Active Coeff dActive dCoeff (H i y)
  refine ⟨F, U, hUopen, hxU, ?_, ?_, ?_⟩
  · intro i y a c hc
    rw [MvPolynomial.mem_support_iff] at hc ⊢
    rw [splitClusterCurryAlgEquiv_coeff_coeff] at hc ⊢
    exact MvPolynomial.mem_support_iff.mp
      (hsupport i y (MvPolynomial.mem_support_iff.mpr hc))
  · intro i a c
    have h := hanalytic i
      (splitClusterCurryCoefficientIndex Active Coeff dActive dCoeff a c)
    simpa only [F, splitClusterCurryAlgEquiv_coeff_coeff] using h
  · intro i
    simp only [analyticSplitClusterCurriedPolynomialGermHom,
      RingHom.comp_apply]
    have hinv :
        (splitClusterCurryAlgEquiv (AnalyticGermAt x)
          Active Coeff dActive dCoeff).symm.toRingHom
            (splitClusterCurryAlgEquiv (AnalyticGermAt x)
              Active Coeff dActive dCoeff (P i)) = P i :=
      (splitClusterCurryAlgEquiv (AnalyticGermAt x)
        Active Coeff dActive dCoeff).symm_apply_apply (P i)
    rw [hinv]
    rw [hH i]
    exact germMapRingHom_coe (𝓝 x)
      (splitClusterCurryAlgEquiv ℝ Active Coeff dActive dCoeff).toRingHom
      (H i)

/-! ## Specialization to the Hermite blockification of rank generators -/

variable {ι : Type*}

/-- Curry the explicit real Hermite blockification of one displayed rank
representative. -/
def paperRankHermiteRealCurriedRepresentative
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (G : RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)
    (z : RestrictedBoxSpace p) :
    MvPolynomial
        (ClusterOperationSymbol Active
          (paperRankHermiteBlockDerivativeCount S Active))
      (MvPolynomial
        (ClusterOperationSymbol Coeff
          (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ) :=
  splitClusterCurryAlgEquiv ℝ Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    (paperRankHermiteRealBlockifiedRepresentative D representative offset S
      Active Coeff blockEquiv G z)

/-- The finite rank-generator representatives supplied by elimination can be
curried through the explicit Hermite blockification on one common analytic
neighborhood.  The chosen curried representatives eventually equal the
literal pointwise transformation of the original displayed representatives,
which is the bridge needed to transport their evaluated vanishing. -/
theorem exists_paperRankHermiteCurriedGeneratorRepresentatives
    {κ : Type*} [Finite κ]
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (g : κ → MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RealAnalyticGerm p))
    (G : κ → RestrictedBoxSpace p →
      MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ)
    (hG : ∀ i,
      analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g i) =
        (G i : Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial (PaperRankRetainedSymbols m S.card) ℝ))) :
    ∃ H : κ → RestrictedBoxSpace p →
        MvPolynomial
          (ClusterOperationSymbol Active
            (paperRankHermiteBlockDerivativeCount S Active))
          (MvPolynomial
            (ClusterOperationSymbol Coeff
              (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ),
    ∃ U : Set (RestrictedBoxSpace p),
      IsOpen U ∧ (0 : RestrictedBoxSpace p) ∈ U ∧
      (∀ i z a, ((H i z).coeff a).support ⊆
        ((paperRankClusterCurryHom (RealAnalyticGerm p) Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff) blockEquiv
          (paperRankHermiteGermJetPolynomial D h0D representative offset S
            Active Coeff blockEquiv) (g i)).coeff a).support) ∧
      (∀ i a c, AnalyticOnNhd ℝ
        (fun z => ((H i z).coeff a).coeff c) U) ∧
      (∀ i,
        analyticSplitClusterCurriedPolynomialGermHom
            (0 : RestrictedBoxSpace p) Active Coeff
            (paperRankHermiteBlockDerivativeCount S Active)
            (paperRankHermiteBlockDerivativeCount S Coeff)
            (paperRankClusterCurryHom (RealAnalyticGerm p) Active Coeff
              (paperRankHermiteBlockDerivativeCount S Active)
              (paperRankHermiteBlockDerivativeCount S Coeff) blockEquiv
              (paperRankHermiteGermJetPolynomial D h0D representative offset S
                Active Coeff blockEquiv) (g i)) =
          (H i : Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial
              (ClusterOperationSymbol Active
                (paperRankHermiteBlockDerivativeCount S Active))
              (MvPolynomial
                (ClusterOperationSymbol Coeff
                  (paperRankHermiteBlockDerivativeCount S Coeff)) ℝ)))) ∧
      (∀ i, H i =ᶠ[𝓝 (0 : RestrictedBoxSpace p)]
        paperRankHermiteRealCurriedRepresentative D representative offset S
          Active Coeff blockEquiv (G i)) := by
  let dActive := paperRankHermiteBlockDerivativeCount S Active
  let dCoeff := paperRankHermiteBlockDerivativeCount S Coeff
  let P : κ → MvPolynomial
      (SplitClusterBlockSymbol Active Coeff dActive dCoeff)
        (RealAnalyticGerm p) :=
    fun i => paperRankClusterBlockificationHom (RealAnalyticGerm p)
      Active Coeff dActive dCoeff blockEquiv
      (paperRankHermiteGermJetPolynomial D h0D representative offset S
        Active Coeff blockEquiv) (g i)
  obtain ⟨H, U, hUopen, h0U, hsupport, hanalytic, hrep⟩ :=
    exists_analyticSplitClusterCurriedRepresentatives
      (0 : RestrictedBoxSpace p) Active Coeff dActive dCoeff P
  refine ⟨H, U, hUopen, h0U, ?_, ?_, ?_, ?_⟩
  · intro i z a
    change ((H i z).coeff a).support ⊆
      ((splitClusterCurryAlgEquiv (RealAnalyticGerm p)
        Active Coeff dActive dCoeff (P i)).coeff a).support
    exact hsupport i z a
  · simpa only [dActive, dCoeff] using hanalytic
  · intro i
    change analyticSplitClusterCurriedPolynomialGermHom
        (0 : RestrictedBoxSpace p) Active Coeff dActive dCoeff
        (splitClusterCurryAlgEquiv (RealAnalyticGerm p)
          Active Coeff dActive dCoeff (P i)) =
      (H i : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial (ClusterOperationSymbol Active dActive)
          (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ)))
    exact hrep i
  · intro i
    have hblock :=
      analyticPolynomialGermHom_paperRankHermiteBlockification_of
        D h0D representative offset S Active Coeff blockEquiv
        (g i) (G i) (hG i)
    have hmapped' :
        analyticSplitClusterCurriedPolynomialGermHom
            (0 : RestrictedBoxSpace p) Active Coeff dActive dCoeff
            (paperRankClusterCurryHom (RealAnalyticGerm p) Active Coeff
              dActive dCoeff blockEquiv
              (paperRankHermiteGermJetPolynomial D h0D representative offset S
                Active Coeff blockEquiv) (g i)) =
          (paperRankHermiteRealCurriedRepresentative D representative offset S
            Active Coeff blockEquiv (G i) :
              Germ (𝓝 (0 : RestrictedBoxSpace p))
                (MvPolynomial (ClusterOperationSymbol Active dActive)
                  (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ))) := by
      let blockGerm :=
        paperRankClusterBlockificationHom (RealAnalyticGerm p)
          Active Coeff dActive dCoeff blockEquiv
          (paperRankHermiteGermJetPolynomial D h0D representative offset S
            Active Coeff blockEquiv) (g i)
      let curryGerm := splitClusterCurryAlgEquiv (RealAnalyticGerm p)
        Active Coeff dActive dCoeff
      let curryReal := splitClusterCurryAlgEquiv ℝ
        Active Coeff dActive dCoeff
      have hcurry :
          paperRankClusterCurryHom (RealAnalyticGerm p) Active Coeff
              dActive dCoeff blockEquiv
              (paperRankHermiteGermJetPolynomial D h0D representative offset S
                Active Coeff blockEquiv) (g i) =
            curryGerm blockGerm := rfl
      rw [hcurry]
      simp only [analyticSplitClusterCurriedPolynomialGermHom,
        RingHom.comp_apply]
      have hinv : curryGerm.symm.toRingHom (curryGerm blockGerm) =
          blockGerm := curryGerm.symm_apply_apply blockGerm
      rw [hinv]
      calc
        (germMapRingHom (𝓝 (0 : RestrictedBoxSpace p))
            curryReal.toRingHom)
            (analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
              blockGerm) =
          (germMapRingHom (𝓝 (0 : RestrictedBoxSpace p))
            curryReal.toRingHom)
            (paperRankHermiteRealBlockifiedRepresentative D representative
              offset S Active Coeff blockEquiv (G i) :
                Germ (𝓝 (0 : RestrictedBoxSpace p))
                  (MvPolynomial
                    (SplitClusterBlockSymbol Active Coeff dActive dCoeff) ℝ)) :=
              congrArg _ hblock
        _ = ((fun z => curryReal
              (paperRankHermiteRealBlockifiedRepresentative D representative
                offset S Active Coeff blockEquiv (G i) z)) :
                Germ (𝓝 (0 : RestrictedBoxSpace p))
                  (MvPolynomial (ClusterOperationSymbol Active dActive)
                    (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ))) :=
              germMapRingHom_coe (𝓝 (0 : RestrictedBoxSpace p))
                curryReal.toRingHom _
        _ = (paperRankHermiteRealCurriedRepresentative D representative offset S
              Active Coeff blockEquiv (G i) :
                Germ (𝓝 (0 : RestrictedBoxSpace p))
                  (MvPolynomial (ClusterOperationSymbol Active dActive)
                    (MvPolynomial (ClusterOperationSymbol Coeff dCoeff) ℝ))) := rfl
    exact Germ.coe_eq.mp ((hrep i).symm.trans hmapped')

end AbelFormalization
