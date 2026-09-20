import AbelFormalization.WilkieCase2ProductFlatEquiv
import AbelFormalization.Wilkie28ExceptionalMathlibOnly

/-!
# Source-only exceptional-value transport across the Case 2 flat equivalence

This uncompiled scratch draft identifies the exact product/flat exceptional
scalar sets.  It supplies no weak selection and makes no family-membership
claim.  The only analytic premises are differentiability of the flat map and
pivot (or of the original product map in the specialization).
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Precomposition by a continuous linear equivalence preserves the singular
values of the augmented derivative.  At `x`, the augmented derivative of
`(H ∘ L, g ∘ L)` is the augmented derivative of `(H,g)` at `L x`
precomposed by the surjective map `L`. -/
theorem wilkie28_exceptionalParameterSet_comp_linearEquiv
    {E D K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (L : E ≃L[ℝ] D) (H : D → K) (g : D → ℝ) (a : K)
    (hHdiff : ∀ z, DifferentiableAt ℝ H z)
    (hgdiff : ∀ z, DifferentiableAt ℝ g z) :
    Wilkie28MathlibOnly.exceptionalParameterSet (H ∘ L) (g ∘ L) a =
      Wilkie28MathlibOnly.exceptionalParameterSet H g a := by
  have hHchain (x : E) :
      fderiv ℝ (H ∘ L) x = (fderiv ℝ H (L x)).comp
        (L : E →L[ℝ] D) := by
    exact ((hHdiff (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hgchain (x : E) :
      fderiv ℝ (g ∘ L) x = (fderiv ℝ g (L x)).comp
        (L : E →L[ℝ] D) := by
    exact ((hgdiff (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hsurj (x : E) :
      Function.Surjective
          (fun v : E ↦
            (fderiv ℝ (H ∘ L) x v, fderiv ℝ (g ∘ L) x v)) ↔
        Function.Surjective
          (fun w : D ↦
            (fderiv ℝ H (L x) w, fderiv ℝ g (L x) w)) := by
    rw [hHchain x, hgchain x]
    constructor
    · intro hs target
      obtain ⟨v, hv⟩ := hs target
      refine ⟨L v, ?_⟩
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe] using hv
    · intro hs target
      obtain ⟨w, hw⟩ := hs target
      refine ⟨L.symm w, ?_⟩
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, L.apply_symm_apply]
        using hw
  ext t
  change
    (∃ x : E, H (L x) = a ∧ g (L x) = t ∧
      ¬ Function.Surjective
        (fun v : E ↦
          (fderiv ℝ (H ∘ L) x v, fderiv ℝ (g ∘ L) x v))) ↔
    (∃ z : D, H z = a ∧ g z = t ∧
      ¬ Function.Surjective
        (fun w : D ↦
          (fderiv ℝ H z w, fderiv ℝ g z w)))
  constructor
  · rintro ⟨x, hxF, hxg, hxsing⟩
    exact ⟨L x, hxF, hxg, fun hs ↦ hxsing ((hsurj x).mpr hs)⟩
  · rintro ⟨z, hzF, hzg, hzsing⟩
    refine ⟨L.symm z, ?_, ?_, ?_⟩
    · simpa only [L.apply_symm_apply] using hzF
    · simpa only [L.apply_symm_apply] using hzg
    · intro hs
      apply hzsing
      have hflat := (hsurj (L.symm z)).mp hs
      simpa only [L.apply_symm_apply] using hflat

/-- The product map and its visible-coordinate pivot have exactly the same
exceptional scalar set as their flat conjugates.  This is the equality needed
to rewrite the flat Charbonnel-membership theorem to the product-shaped
`hBmem` premise in the recursive Case 2 draft. -/
theorem wilkieCase2_product_exceptional_eq_flat
    {m q : ℕ}
    (F : ((Fin (m + 1) → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (i : Fin (m + 1))
    (hFdiff : ∀ x, DifferentiableAt ℝ F x) :
    Wilkie28MathlibOnly.exceptionalParameterSet
        F (fun x ↦ x.1 i) a =
      Wilkie28MathlibOnly.exceptionalParameterSet
        (F ∘ (wilkieCase2ProductFlatEquiv (m + 1) q).symm)
        (fun z : RealEuclidean ((m + 1) + q) ↦
          z (Fin.castAdd q i)) a := by
  let L := wilkieCase2ProductFlatEquiv (m + 1) q
  let H := F ∘ L.symm
  let g : RealEuclideanFunction ((m + 1) + q) :=
    fun z ↦ z (Fin.castAdd q i)
  have hHdiff (z : RealEuclidean ((m + 1) + q)) :
      DifferentiableAt ℝ H z := by
    exact ((hFdiff (L.symm z)).hasFDerivAt.comp z
      L.symm.hasFDerivAt).differentiableAt
  have hgdiff (z : RealEuclidean ((m + 1) + q)) :
      DifferentiableAt ℝ g z := by
    change DifferentiableAt ℝ
      (ContinuousLinearMap.proj (Fin.castAdd q i) :
        RealEuclidean ((m + 1) + q) →L[ℝ] ℝ) z
    exact (ContinuousLinearMap.proj (Fin.castAdd q i) :
      RealEuclidean ((m + 1) + q) →L[ℝ] ℝ).differentiableAt
  have hFcomp : H ∘ L = F := by
    funext x
    exact congrArg F (L.symm_apply_apply x)
  have hgcomp : g ∘ L = (fun x ↦ x.1 i) := by
    funext x
    exact wilkieCase2ProductFlatEquiv_visible x i
  have htransport :=
    wilkie28_exceptionalParameterSet_comp_linearEquiv
      L H g a hHdiff hgdiff
  simpa only [hFcomp, hgcomp, H, g, L] using htransport

end AbelFormalization
