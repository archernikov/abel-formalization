import AbelFormalization.HermiteRankTopPrefix
import AbelFormalization.PolynomialGermSymbolMaps

/-!
# Evaluation across the Hermite rank top-prefix reindexing

The algebra equivalence from the retained paper-rank ring to the full ordered
cluster prefix is only a renaming of independent polynomial variables.  This
module makes that renaming explicit and records its semantic consequences:
evaluation is preserved after transporting an assignment, displayed
generating families still generate the mapped ideal, and polynomial-valued
analytic-germ representatives transport pointwise.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

variable {ι : Type*}

/-- The top-prefix algebra equivalence is transparently the polynomial rename
induced by `paperRankHermiteTopPrefixSymbolEquiv`. -/
theorem paperRankHermiteTopPrefixAlgEquiv_eq_renameEquiv
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) :
    data.paperRankHermiteTopPrefixAlgEquiv R S =
      MvPolynomial.renameEquiv R
        (paperRankHermiteTopPrefixSymbolEquiv data S) := by
  rfl

/-- Transport an assignment on retained paper-rank variables to the ordered
top-prefix variables. -/
def paperRankHermiteTopPrefixAssignment
    {R : Type*}
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (v : PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → R) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) data.orderedClusterCount) → R :=
  v ∘ (paperRankHermiteTopPrefixSymbolEquiv data S).symm

/-- Reindexing a polynomial and transporting its variable assignment preserve
its value. -/
@[simp]
theorem eval_paperRankHermiteTopPrefixAlgEquiv
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (v : PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → R)
    (P : MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R) :
    MvPolynomial.eval (paperRankHermiteTopPrefixAssignment data S v)
        (data.paperRankHermiteTopPrefixAlgEquiv R S P) =
      MvPolynomial.eval v P := by
  rw [paperRankHermiteTopPrefixAlgEquiv_eq_renameEquiv]
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  rw [show paperRankHermiteTopPrefixAssignment data S v ∘
      paperRankHermiteTopPrefixSymbolEquiv data S = v by
    funext i
    change v ((paperRankHermiteTopPrefixSymbolEquiv data S).symm
      (paperRankHermiteTopPrefixSymbolEquiv data S i)) = v i
    rw [(paperRankHermiteTopPrefixSymbolEquiv data S).symm_apply_apply]]

/-- Apply the top-prefix reindexing pointwise to a displayed polynomial
representative. -/
def paperRankHermiteTopPrefixRepresentative
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (G : RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ) :
    RestrictedBoxSpace p →
      data.OrderedClusterPrefixRing ℝ (paperRankHermiteHigherCount S)
        data.orderedClusterCount :=
  fun w ↦ MvPolynomial.rename (paperRankHermiteTopPrefixSymbolEquiv data S)
    (G w)

@[simp]
theorem paperRankHermiteTopPrefixRepresentative_apply
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (G : RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ)
    (w : RestrictedBoxSpace p) :
    paperRankHermiteTopPrefixRepresentative data S G w =
      data.paperRankHermiteTopPrefixAlgEquiv ℝ S (G w) := by
  rw [paperRankHermiteTopPrefixAlgEquiv_eq_renameEquiv,
    MvPolynomial.renameEquiv_apply]
  rfl

/-- A displayed generating family for an ideal remains a displayed generating
family after the top-prefix reindexing. -/
theorem span_paperRankHermiteTopPrefixAlgEquiv_range
    (R : Type*) [CommRing R]
    {κ : Type*}
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (g : κ → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R) :
    Ideal.span
        (Set.range (fun j ↦ data.paperRankHermiteTopPrefixAlgEquiv R S (g j))) =
      data.paperRankHermiteTopPrefixIdeal R S
        (Ideal.span (Set.range g)) := by
  rw [paperRankHermiteTopPrefixIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨g j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

/-- An analytic polynomial-valued representative transports pointwise across
the full-Hermite top-prefix reindexing. -/
theorem analyticPolynomialGermHom_paperRankHermiteTopPrefixAlgEquiv_of
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (g : MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))
    (G : RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ)
    (hG : analyticPolynomialGermHom (0 : RestrictedBoxSpace p) g =
      (G : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial
          (PaperRankRetainedSymbols m
            (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ))) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (data.paperRankHermiteTopPrefixAlgEquiv (RealAnalyticGerm p) S g) =
      (paperRankHermiteTopPrefixRepresentative data S G :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (data.OrderedClusterPrefixRing ℝ
            (paperRankHermiteHigherCount S) data.orderedClusterCount)) := by
  rw [paperRankHermiteTopPrefixAlgEquiv_eq_renameEquiv,
    MvPolynomial.renameEquiv_apply]
  exact
      analyticPolynomialGermHom_rename_of
        (0 : RestrictedBoxSpace p)
        (paperRankHermiteTopPrefixSymbolEquiv data S) hG

end RepresentativeClusterSubsequence
end AbelFormalization
