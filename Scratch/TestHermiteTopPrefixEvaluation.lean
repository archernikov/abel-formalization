import AbelFormalization.HermiteRankTopPrefix
import AbelFormalization.PolynomialGermSymbolMaps

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

variable {ι : Type*}

def testPaperRankHermiteTopPrefixSymbolEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) :
    PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)) ≃
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) data.orderedClusterCount) := by
  let flat := paperRankRetainedFlatHermiteEquiv m
    (paperRankHermiteHigherCount S + 1)
  let top := clusterOperationSymbolEquiv
    data.orderedClusterPrefixTopEquiv
    (fun _ : Fin m ↦ paperRankHermiteHigherCount S + 1)
    (data.orderedClusterPrefixConstantDerivativeCount
      (paperRankHermiteHigherCount S + 1) data.orderedClusterCount)
    (fun _ ↦ rfl)
  simpa only [← paperRankHermiteHigherCount_add_one S, Nat.add_assoc,
    Nat.reduceAdd] using flat.trans top

theorem test_paperRankHermiteTopPrefixAlgEquiv_eq_renameEquiv
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) :
    data.paperRankHermiteTopPrefixAlgEquiv R S =
      MvPolynomial.renameEquiv R
        (testPaperRankHermiteTopPrefixSymbolEquiv data S) := by
  simp only [paperRankHermiteTopPrefixAlgEquiv,
    paperRankRetainedTopPrefixAlgEquiv,
    paperRankRetainedFlatHermiteAlgEquiv,
    clusterOperationRenameAlgEquiv,
    testPaperRankHermiteTopPrefixSymbolEquiv,
    MvPolynomial.renameEquiv_trans]

def testPaperRankHermiteTopPrefixAssignment
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
  v ∘ (testPaperRankHermiteTopPrefixSymbolEquiv data S).symm

theorem test_eval_paperRankHermiteTopPrefixAlgEquiv
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (v : PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → R)
    (P : MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) R) :
    MvPolynomial.eval (testPaperRankHermiteTopPrefixAssignment data S v)
        (data.paperRankHermiteTopPrefixAlgEquiv R S P) =
      MvPolynomial.eval v P := by
  rw [test_paperRankHermiteTopPrefixAlgEquiv_eq_renameEquiv]
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  congr 1
  funext i
  simp [testPaperRankHermiteTopPrefixAssignment]

end RepresentativeClusterSubsequence
end AbelFormalization
