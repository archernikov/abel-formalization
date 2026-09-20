import AbelFormalization.WilkieCase2ReachableRecursiveAlternative
import AbelFormalization.WilkieCase2ExceptionalProductFlatTransport
import AbelFormalization.WilkieCase2FlatAffineFamilyClosure
import AbelFormalization.Wilkie28ExceptionalMembership

/-!
# Exceptional-set membership along reachable Case 2 slices

Flat tuple membership in a geometric family is preserved at every affine
descendant of the original map.  For the Abel geometric family, this gives
the unary exceptional-set membership required by the reachable Case 2
recursion.  Smooth singular-witness selection remains a separate premise.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Every reachable product map has a flat presentation whose coordinates
remain in the same geometric function family. -/
theorem wilkieCase2Reachable_flatTupleInFamily
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {n q m : ℕ} {F₀ : WilkieCase2StageMap n q}
    {F : WilkieCase2StageMap m q}
    (hReach : WilkieCase2Reachable F₀ m F)
    (hF₀ : FunctionTupleInFamily G (wilkieCase2Flatten F₀)) :
    FunctionTupleInFamily G (wilkieCase2Flatten F) := by
  induction hReach with
  | original => exact hF₀
  | @visibleSlice m F hReach i b ih =>
      have hsliced := functionTupleInFamily_comp_wilkieCase2FlatCastInsert
        hG (wilkieCase2Flatten F) ih i b
      rw [wilkieCase2Flatten_slice_eq]
      exact hsliced

/-- Smooth flat coordinates make the equivalent product map globally
smooth. -/
theorem contDiff_product_of_flatTupleInFamily
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {m q : ℕ} (F : WilkieCase2StageMap m q)
    (hF : FunctionTupleInFamily G (wilkieCase2Flatten F)) :
    ContDiff ℝ 1 F := by
  let E := wilkieCase2ProductFlatEquiv m q
  have hflat : ContDiff ℝ 1 (wilkieCase2Flatten F) := by
    rw [contDiff_pi]
    intro j
    exact (hsmooth _ _ (hF j)).of_le (by simp)
  have hcomp : ContDiff ℝ 1 (wilkieCase2Flatten F ∘ E) :=
    hflat.comp E.contDiff
  convert hcomp using 1
  funext x
  change F x = F (E.symm (E x))
  exact congrArg F (E.symm_apply_apply x).symm

/-- For every affine descendant of one Abel-family tuple, the exceptional
values of every visible coordinate form a member of the rank-one
Charbonnel closure. -/
theorem wilkieCase2Reachable_exceptional_mem_abelCharbonnel
    {A : ℝ → ℝ} (hA : IsAbel A)
    {n q m : ℕ} {F₀ : WilkieCase2StageMap n q}
    {F : WilkieCase2StageMap (m + 1) q}
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hReach : WilkieCase2Reachable F₀ (m + 1) F)
    (a : RealEuclidean q) (i : Fin (m + 1)) :
    {v : RealEuclidean 1 |
      v 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet
        F (fun x ↦ x.1 i) a} ∈
      charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A)) 1 := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hflat := wilkieCase2Reachable_flatTupleInFamily
    hG hReach hF₀
  let coordinate : Fin ((m + 1) + q) := Fin.castAdd q i
  let pivot : RealEuclideanFunction ((m + 1) + q) :=
    fun z ↦ z coordinate
  have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
    simpa [pivot, coordinate] using hG.polynomial (MvPolynomial.X coordinate)
  have hmem := wilkie28_exceptionalParameterSet_mem_literalZeroCharbonnel
    hG hsmooth hderiv (wilkieCase2Flatten F) pivot a hflat hpivot
  have hFdiff : ∀ x, DifferentiableAt ℝ F x := by
    have hFsmooth := contDiff_product_of_flatTupleInFamily hsmooth F hflat
    intro x
    exact hFsmooth.differentiable (by simp) x
  rw [wilkieCase2_product_exceptional_eq_flat F a i hFdiff]
  simpa only [pivot, coordinate, wilkieCase2Flatten] using hmem

end AbelFormalization
