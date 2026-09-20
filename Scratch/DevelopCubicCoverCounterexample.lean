import AbelFormalization.LionRankPatchLocalRegularSubtupleReduction

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

theorem test_constraintFDeriv_range_eq_top_of_lagrangeCriticalSystemMap_range_eq_top
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a)
    (z : RealEuclidean (a + k))
    (hH : ∀ i, DifferentiableAt ℝ (H i)
      (lagrangePrimalProjection a k z))
    (hsystem : DifferentiableAt ℝ (lagrangeCriticalSystemMap H rho) z)
    (hregular : (fderiv ℝ (lagrangeCriticalSystemMap H rho) z).range = ⊤) :
    (constraintFDeriv H (lagrangePrimalProjection a k z)).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  let target : RealEuclidean (a + k) :=
    realEuclideanAppend (0 : RealEuclidean a) y
  obtain ⟨dz, hdz⟩ := LinearMap.range_eq_top.mp hregular target
  let dx : RealEuclidean a := lagrangePrimalProjection a k dz
  refine ⟨dx, ?_⟩
  funext i
  have hcomponent := fderiv_apply hsystem (Fin.natAdd a i)
  let P := lagrangePrimalProjectionCLM a k
  have hHi : HasFDerivAt
      (fun w : RealEuclidean (a + k) ↦ H i (P w))
      ((fderiv ℝ (H i) (lagrangePrimalProjection a k z)).comp P) z := by
    exact (hH i).hasFDerivAt.comp z P.hasFDerivAt
  have hcomponent' :
      (ContinuousLinearMap.proj (Fin.natAdd a i)).comp
          (fderiv ℝ (lagrangeCriticalSystemMap H rho) z) =
        (fderiv ℝ (H i) (lagrangePrimalProjection a k z)).comp P := by
    rw [← hcomponent]
    have hfun :
        (fun w : RealEuclidean (a + k) ↦
          lagrangeCriticalSystemMap H rho w (Fin.natAdd a i)) =
        fun w ↦ H i (P w) := by
      funext w
      simp [P, lagrangeConstraintEquation]
    rw [hfun]
    exact hHi.fderiv
  have happ := congrArg
    (fun T : RealEuclidean (a + k) →L[ℝ] ℝ ↦ T dz) hcomponent'
  have hdzi := congrFun hdz (Fin.natAdd a i)
  simpa [constraintFDeriv, dx, P, target] using happ.symm.trans hdzi

theorem test_not_nonempty_canonicalRankMinorFiniteRegularLagrangeCover_of_three_singular_components
    {g : RealEuclidean 1 → RealEuclidean 1}
    (i : RankMinorPatchIndex 1 1) (t : RealEuclidean 1)
    (p : Fin 3 →
      constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
        {rankMinorPatchConstraintTarget i t})
    (hcomponent : ∀ q, connectedComponent (p q) = {p q})
    (hcoord : Function.Injective
      (fun q ↦ (p q : RealEuclidean 2) (0 : Fin 2)))
    (hfullC2 : ∀ c, ContDiff ℝ 2 (rankMinorPatchConstraintTuple g i c))
    (hnonzeroOnlyReciprocal : ∀ q c,
      fderiv ℝ (rankMinorPatchConstraintTuple g i c)
          (p q : RealEuclidean 2) ≠ 0 →
        c = Fin.last
          (1 + successorMinorCount 1 1 (i.1 : ℕ)))
    (hprimalDirectionZero : ∀ q c,
      fderiv ℝ (rankMinorPatchConstraintTuple g i c)
          (p q : RealEuclidean 2) (Pi.single (0 : Fin 2) 1) = 0) :
    ¬ Nonempty (CanonicalRankMinorFiniteRegularLagrangeCover g) := by
  intro hcover
  let cover := Classical.choice hcover
  choose chart y lambda hycomponent hsystem hregular using
    fun q ↦ cover.component_lift i t (p q)
  have hy : ∀ q, y q = p q := by
    intro q
    have hmem := hycomponent q
    rw [hcomponent q] at hmem
    exact hmem
  have hchartConstraintSurj : ∀ q,
      (constraintFDeriv
        (rankMinorPatchLagrangeSubtuple g i (chart q))
        (p q : RealEuclidean 2)).range = ⊤ := by
    intro q
    let H := rankMinorPatchLagrangeSubtuple g i (chart q)
    let center := cover.center i (chart q) t
    let rho : RealEuclideanFunction 2 := standardSquaredDistance center
    let z : RealEuclidean (2 + ((chart q).1 : ℕ)) :=
      realEuclideanAppend (y q : RealEuclidean 2) (lambda q)
    have hH2 : ∀ j, ContDiff ℝ 2 (H j) := by
      intro j
      exact hfullC2 ((chart q).2 j)
    have hfamilyC1 : ContDiff ℝ 1
        (lagrangeSquaredDistanceCriticalFamily H) :=
      contDiff_lagrangeSquaredDistanceCriticalFamily H hH2
    have hsystemDiff : DifferentiableAt ℝ
        (lagrangeCriticalSystemMap H rho) z := by
      have hs : ContDiff ℝ 1
          (fun w ↦ lagrangeSquaredDistanceCriticalFamily H (w, center)) :=
        hfamilyC1.comp (contDiff_id.prodMk contDiff_const)
      exact hs.differentiable (by norm_num) z
    have hsurjAtZ :=
      test_constraintFDeriv_range_eq_top_of_lagrangeCriticalSystemMap_range_eq_top
        H rho z
        (fun j ↦ ((hH2 j).differentiable (by norm_num)).differentiableAt)
        hsystemDiff (by simpa only [H, rho, z] using hregular q)
    have hprimal : lagrangePrimalProjection 2 ((chart q).1 : ℕ) z =
        (y q : RealEuclidean 2) := by
      exact lagrangePrimalProjection_append
        (y q : RealEuclidean 2) (lambda q)
    rw [hprimal] at hsurjAtZ
    simpa only [H, hy q] using hsurjAtZ
  have hchartOnlyReciprocal : ∀ q j,
      (chart q).2 j =
        Fin.last (1 + successorMinorCount 1 1 (i.1 : ℕ)) := by
    intro q j
    apply hnonzeroOnlyReciprocal q ((chart q).2 j)
    intro hzero
    obtain ⟨dx, hdx⟩ := LinearMap.range_eq_top.mp
      (hchartConstraintSurj q) (Pi.single j 1)
    have hj := congrFun hdx j
    have hfunction :
        rankMinorPatchLagrangeSubtuple g i (chart q) j =
          rankMinorPatchConstraintTuple g i ((chart q).2 j) := rfl
    have hj' :
        fderiv ℝ (rankMinorPatchLagrangeSubtuple g i (chart q) j)
            (p q : RealEuclidean 2) dx = 1 := by
      simpa [constraintFDeriv] using hj
    rw [hfunction, hzero] at hj'
    simpa using hj'
  have hchartSize : ∀ q, ((chart q).1 : ℕ) < 2 := by
    intro q
    let e : Fin ((chart q).1 : ℕ) ↪ Fin 1 :=
      { toFun := fun _ ↦ 0
        inj' := by
          intro j k _h
          apply (chart q).2.injective
          rw [hchartOnlyReciprocal q j, hchartOnlyReciprocal q k] }
    have hcard := Fintype.card_le_of_injective e e.injective
    simpa using Nat.lt_succ_of_le hcard
  have hcenterCoordinate : ∀ q,
      (cover.center i (chart q) t) (0 : Fin 2) =
        (p q : RealEuclidean 2) (0 : Fin 2) := by
    intro q
    have hs := congrFun (hsystem q)
      (Fin.castAdd ((chart q).1 : ℕ) (0 : Fin 2))
    have hsum : (∑ j,
        lagrangeMultiplierCoordinate (a := 2) j
            (realEuclideanAppend (y q : RealEuclidean 2) (lambda q)) *
          fderiv ℝ
            (rankMinorPatchLagrangeSubtuple g i (chart q) j)
            (y q : RealEuclidean 2) (Pi.single (0 : Fin 2) 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      rw [show rankMinorPatchLagrangeSubtuple g i (chart q) j =
          rankMinorPatchConstraintTuple g i ((chart q).2 j) by rfl,
        hy q, hprimalDirectionZero]
      simp
    simp only [lagrangeCriticalSystemMap_apply_castAdd,
      lagrangeStationarityEquation_standardSquaredDistance_apply,
      realEuclideanAppend_castAdd, Pi.zero_apply] at hs
    have hprimal : lagrangePrimalProjection 2 ((chart q).1 : ℕ)
        (realEuclideanAppend (y q : RealEuclidean 2) (lambda q)) =
          (y q : RealEuclidean 2) :=
      lagrangePrimalProjection_append (y q : RealEuclidean 2) (lambda q)
    rw [hprimal] at hs
    rw [hsum, sub_zero] at hs
    rw [hy q] at hs
    linarith
  let smallChart : Fin 3 → Fin 2 := fun q ↦
    ⟨((chart q).1 : ℕ), hchartSize q⟩
  have chart_eq_of_size_eq
      (q r : Fin 3)
      (hsize : ((chart q).1 : ℕ) = ((chart r).1 : ℕ)) :
      chart q = chart r := by
    rcases hq : chart q with ⟨k, ek⟩
    rcases hr : chart r with ⟨l, el⟩
    have hkl : k = l := by
      apply Fin.ext
      simpa [hq, hr] using hsize
    subst l
    have hemb : ek = el := by
      apply Function.Embedding.ext
      intro j
      have hqall := hchartOnlyReciprocal q
      have hrall := hchartOnlyReciprocal r
      rw [hq] at hqall
      rw [hr] at hrall
      exact (hqall j).trans (hrall j).symm
    subst el
    rfl
  have hsmallInjective : Function.Injective smallChart := by
    intro q r hqr
    have hval : ((chart q).1 : ℕ) = ((chart r).1 : ℕ) :=
      congrArg (fun s : Fin 2 ↦ (s : ℕ)) hqr
    have hchart : chart q = chart r := chart_eq_of_size_eq q r hval
    apply hcoord
    change (p q : RealEuclidean 2) 0 = (p r : RealEuclidean 2) 0
    rw [← hcenterCoordinate q, ← hcenterCoordinate r, hchart]
  have hcard := Fintype.card_le_of_injective smallChart hsmallInjective
  simp only [Fintype.card_fin] at hcard
  omega

end AbelFormalization
