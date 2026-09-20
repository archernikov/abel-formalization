import AbelFormalization.RestrictedPairMergeDenominatorClearedRegularZero

/-!
# The cleared pair-merge graph as one restricted square system
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- At a quantitative-tail point, the full denominator-cleared augmented
family has a regular zero at the flat graph point exactly when the original
old equations have a regular zero after pair-merge substitution. -/
theorem IsAbel.mem_regularZeroSet_pairMergeDenominatorClearedAugmented_graphLift_iff
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hQ : ∀ row, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q row) = F row)
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (R : ℝ)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (holdDomain : restrictedPairMergeSourceMap K k i j x ∈
      restrictedAbelJetDomain (a := a) D representative offset)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hFdiff : DifferentiableAt ℝ (constraintMap F)
      (restrictedPairMergeSourceMap K k i j x)) :
    restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x ∈
      regularZeroSet
        (restrictedPairMergeExceptionalFlatCombinedDomain
          D R representative i j S)
        (constraintMap
          (restrictedPairMergeDenominatorClearedAugmentedEquationFamily
            A D representative offset K k i j S Q)) ↔
      x ∈ regularZeroSet
        (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
        (constraintMap F ∘ restrictedPairMergeSourceMap K k i j) := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let e := restrictedPairMergeExceptionalGraphContinuousLinearEquiv
    (m := m) (p := p) (a := a) (N := N)
  let qout := finFunctionProductContinuousLinearEquiv n N
  let eta := restrictedPairMergeExceptionalVectorShift
    (a := a) D representative offset K k i j S
  let lift := restrictedPairMergeExceptionalFiniteGraphLift (a := a)
    D representative offset K k i j S
  let P := restrictedPairMergeDenominatorClearedCompressedEquation
    A D representative offset K k i j S Q
  let aug := restrictedPairMergeDenominatorClearedAugmentedEquationFamily
    A D representative offset K k i j S Q
  let Omega := restrictedBaseOpenDomain (m := m + 1) (a := a)
    (restrictedPairMergeBox D) R
  let H : RestrictedSource (m + 1) (p + 1) a × (Fin N → ℝ) →
      (Fin n → ℝ) := constraintMap P ∘ e.symm
  let graphEquation := restrictedPairMergeExceptionalVectorGraphEquation
    (a := a) D representative offset K k i j S
  let implicitSystem := finiteImplicitGraphLiftSystem H graphEquation
  have helift : e (lift x) = (x, eta x) := by
    change restrictedPairMergeExceptionalGraphProduct
        (restrictedPairMergeExceptionalGraphLift
          (restrictedPairMergeExceptionalGraphShift
            D representative offset K k i j S) x) =
      (x, fun t ↦ restrictedPairMergeExceptionalGraphShift
        D representative offset K k i j S t x)
    exact restrictedPairMergeExceptionalGraphProduct_lift
      (restrictedPairMergeExceptionalGraphShift
        (a := a) D representative offset K k i j S) x
  have hlift : e.symm (x, eta x) = lift x := by
    apply e.injective
    rw [e.apply_symm_apply, helift]
  have hzDomain :=
    restrictedPairMergeExceptionalFiniteGraphLift_mem_commonJetDomain
      D representative offset hK i j S B hB hbB x holdDomain hw htail
  have hPdiff : DifferentiableAt ℝ (constraintMap P) (lift x) := by
    exact hA.differentiableAt_constraintMap_restrictedPairMergeDenominatorClearedCompressed
      D representative offset K k i j S Q hzDomain
  have hHdiff : DifferentiableAt ℝ H (x, eta x) := by
    have hc := hPdiff.comp (x, eta x) e.symm.differentiableAt
    simpa only [H, Function.comp_apply, hlift] using hc
  have hgraph :=
    mem_regularZeroSet_restrictedPairMergeExceptionalFiniteGraphLift_iff
      D representative offset hK i j S B hB hbB x hw htail
        (Omega := Omega) hHdiff
  have hgraphSub :
      finiteGraphSubstitution H eta =
        (fun y ↦ constraintMap P (lift y)) := by
    funext y
    change constraintMap P (e.symm (y, eta y)) = constraintMap P (lift y)
    congr 1
  rw [hgraphSub] at hgraph
  have hconstraint :
      constraintMap aug = qout ∘ implicitSystem ∘ e := by
    have haug : aug =
        restrictedPairMergeExceptionalFlattenedEquationFamily
          D representative offset K k i j S P := by
      funext r z
      refine Fin.addCases (fun row ↦ ?_) (fun t ↦ ?_) r
      · rfl
      · rfl
    rw [haug]
    simpa only [P, qout, implicitSystem, H, graphEquation, e, N] using
      (constraintMap_restrictedPairMergeExceptionalFlattenedEquationFamily
        D representative offset K k i j S P)
  have hset := regularZeroSet_preimage_continuousLinearEquiv
    e qout ((Prod.fst :
      RestrictedSource (m + 1) (p + 1) a × (Fin N → ℝ) →
        RestrictedSource (m + 1) (p + 1) a) ⁻¹' Omega) implicitSystem
  rw [← hconstraint] at hset
  have hflat := Set.ext_iff.mp hset (lift x)
  have hflat' :
      lift x ∈ regularZeroSet
          (restrictedPairMergeExceptionalFlatCombinedDomain
            D R representative i j S) (constraintMap aug) ↔
        (x, eta x) ∈ regularZeroSet
          ((Prod.fst :
            RestrictedSource (m + 1) (p + 1) a × (Fin N → ℝ) →
              RestrictedSource (m + 1) (p + 1) a) ⁻¹' Omega)
          implicitSystem := by
    simpa only [restrictedPairMergeExceptionalFlatCombinedDomain,
      restrictedPairMergeExceptionalCombinedDomain,
      e, N, Omega, Set.mem_preimage, helift] using hflat
  have hscale := hA.mem_regularZeroSet_denominatorCleared_graphSubstitution_iff
    D representative offset hK i j S Q F hQ B hB hbB Omega x
      holdDomain hw htail hFdiff
  exact hflat'.trans (hgraph.symm.trans hscale)

end AbelFormalization
