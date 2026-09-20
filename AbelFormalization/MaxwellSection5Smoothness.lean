import AbelFormalization.MaxwellAutomaticFirstOrder
import AbelFormalization.CharbonnelClosureNullityWitnesses
import AbelFormalization.MaxwellClosureNullity

/-!
# Maxwell smoothness from the Charbonnel section 5 induction

The section 5 induction already constructs all of `P'_n`, `P_n`, and `Q_n`.
This file records the resulting Theorems 2.1 and 2.2 together and feeds them
to the automatic Maxwell first-order assembly.  Thus Maxwell's finite-order
almost-everywhere smoothness theorem is no longer a separate input once the
section 5 analytic and finite-decomposition steps are available.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- The complete logical section 5 induction gives both Charbonnel theorems
used by the automatic Maxwell argument. -/
theorem charbonnelTheorems21And22_of_section5Induction
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hbase : CharbonnelPPrime C 1)
    (hanalytic : CharbonnelSection5AnalyticStep C)
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition C n)
    (hwitness : HasCharbonnelClosureNullityWitnesses C) :
    CharbonnelTheorem21 C ∧ CharbonnelTheorem22 C := by
  have hPPrime : ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n :=
    charbonnelPPrime_all_of_one_and_analyticStep
      htrunc hbase hanalytic
  have hQ : ∀ {n : ℕ}, 0 < n → CharbonnelQ C n := by
    intro n hn
    exact charbonnelQ_of_pPrime_and_analyticStep hn htrunc hanalytic
      (hPPrime hn)
  have hP : ∀ {n : ℕ}, 0 < n → CharbonnelP C n := by
    intro n hn
    exact charbonnelP_of_pPrime_Q_and_closureWitness
      hn hmem (hPPrime hn) (hQ hn) hwitness
  have hnull : ∀ {n : ℕ}, 0 < n → CharbonnelInteriorNullity C n := by
    intro n hn
    exact charbonnelInteriorNullity_of_pPrime_and_finiteLocallyClosed
      hn hmem (hdecomp hn) (hPPrime hn)
  let h21 : CharbonnelTheorem21 C :=
    charbonnelTheorem21_of_interiorNullity_and_P hnull hP
  have hclosure : ∀ {d : ℕ}, 0 < d →
      ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
        interior S = ∅ → interior (closure S) = ∅ := by
    intro d hd S hS hSempty
    exact (h21 hd hS).2.1.mp ((h21 hd hS).1.mp hSempty)
  let h22 : CharbonnelTheorem22 C :=
    charbonnelTheorem22_of_Q hmem hclosure hQ
  exact ⟨h21, h22⟩

/-- For a literal-zero Charbonnel closure, the elementary trace, truncation,
one-dimensional, and closure-witness inputs are already theorems.  The
section 5 analytic step and finite locally closed decomposition therefore
imply Maxwell's full finite-output, finite-order smoothness conclusion. -/
theorem literalZeroSet_maxwellAlmostEverywhereSmoothness_of_section5Inputs
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) n) :
    MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let C := charbonnelClosure (literalZeroSetFamily G)
  have hmem : CharbonnelSection5TraceMembership C :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  have htrunc : CharbonnelCompactTruncationMembership C :=
    literalZeroSet_charbonnelClosure_compactTruncationMembership hG hsmooth
  have hbase : CharbonnelPPrime C 1 := hC.charbonnelPPrime_one
  have hwitness : HasCharbonnelClosureNullityWitnesses C :=
    literalZeroSet_charbonnelClosure_hasClosureNullityWitnesses hG hsmooth
  obtain ⟨h21, h22⟩ :=
    charbonnelTheorems21And22_of_section5Induction
      hmem htrunc hbase hanalytic hdecomp hwitness
  exact maxwellAlmostEverywhereSmoothness_of_charbonnel
    hC hmem h21 h22

/-- Uniform fiber finiteness supplies the weak-structure argument needed by
the preceding literal-zero specialization. -/
theorem literalZeroSet_maxwellAlmostEverywhereSmoothness_of_section5
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) n) :
    MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure (literalZeroSetFamily G)) :=
  literalZeroSet_maxwellAlmostEverywhereSmoothness_of_section5Inputs
    hG hsmooth
      (literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
        hG hsmooth hUFF)
      hanalytic hdecomp

/-- The source-shaped Section 5 route replaces finite locally closed
decomposition by Maxwell's meagre finite-selection step.  Together with the
analytic successor step it supplies `P'_n`, closure regularity, Theorem 2.1,
`Q_n`, and hence Theorem 2.2. -/
theorem literalZeroSet_charbonnelTheorems21And22_of_meagreSelection_and_analyticStep
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelTheorem21
        (charbonnelClosure (literalZeroSetFamily G)) ∧
      CharbonnelTheorem22
        (charbonnelClosure (literalZeroSetFamily G)) := by
  let C := charbonnelClosure (literalZeroSetFamily G)
  have hC : PositiveArityOMinimalWeakSetStructure C :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hmem : CharbonnelSection5TraceMembership C :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  have htrunc : CharbonnelCompactTruncationMembership C :=
    literalZeroSet_charbonnelClosure_compactTruncationMembership hG hsmooth
  let hMaxwell : MaxwellClosureNullityDimensionInduction C :=
    maxwellClosureNullityDimensionInduction_of_meagreSelection_and_analyticStep
      hC hselection hanalytic
  have h21 : CharbonnelTheorem21 C := hMaxwell.theorem21 hC hmem
  have hPPrime : ∀ {d : ℕ}, 0 < d → CharbonnelPPrime C d :=
    hMaxwell.pPrime_all hC
  have hQ : ∀ {n : ℕ}, 0 < n → CharbonnelQ C n := by
    intro n hn
    exact charbonnelQ_of_pPrime_and_analyticStep hn htrunc hanalytic
      (hPPrime hn)
  have hclosure : ∀ {d : ℕ}, 0 < d →
      ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
        interior S = ∅ → interior (closure S) = ∅ := by
    intro d hd S hS hSempty
    exact (h21 hd hS).2.1.mp ((h21 hd hS).1.mp hSempty)
  have h22 : CharbonnelTheorem22 C :=
    charbonnelTheorem22_of_Q hmem hclosure hQ
  exact ⟨h21, h22⟩

/-- The preceding source-shaped construction of Theorems 2.1 and 2.2 feeds
the automatic Maxwell theorem. -/
theorem
    literalZeroSet_maxwellAlmostEverywhereSmoothness_of_meagreSelection_and_analyticStep
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G))) :
    MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure (literalZeroSetFamily G)) := by
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  obtain ⟨h21, h22⟩ :=
    literalZeroSet_charbonnelTheorems21And22_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  exact maxwellAlmostEverywhereSmoothness_of_charbonnel
    hC hmem h21 h22

end AbelFormalization
