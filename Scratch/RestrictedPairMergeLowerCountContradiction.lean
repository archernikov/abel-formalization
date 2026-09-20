import AbelFormalization.RestrictedPairMergeAugmentedRegularZero

/-!
# The pair branch contradicts lower representative-count finiteness
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type}

/-- An all-unbounded `q+2` regular-zero sequence with a fixed pair-merge
asymptotic is impossible once restricted base finiteness is known for `q+1`
representatives. -/
theorem IsAbel.false_of_restrictedPairMergeBranch_q_add_two
    {A : ℝ → ℝ} (hA : IsAbel A)
    {q : ℕ}
    (hlower : RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 1))
    [Finite ι] {p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin (q + 2))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := q + 2) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin (((q + 2) + p) + a) →
      RestrictedSource (q + 2) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource (q + 2) p a)
    (w₀ : RestrictedBoxSpace p)
    (i : Fin (q + 2)) (j : Fin (q + 1))
    {K k : ℕ} (hK : 1 ≤ K)
    (hxinj : Function.Injective x)
    (hxmem : ∀ n, x n ∈
      regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F))
    (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀))
    (hxrep : ∀ r, Tendsto (fun n ↦ (x n).1.1 r) atTop atTop)
    (hxi : Tendsto (fun n ↦
      L^[K + k] ((x n).1.1 i) -
        L^[K] ((x n).1.1 (i.succAbove j)))
      atTop (nhds 0)) : False := by
  classical
  obtain ⟨S, Q, _C, _hC, hQ, _ell, _T, _hT⟩ :=
    exists_restrictedPairMergeDenominatorClearedCompressedSystem
      A D representative offset K k i j F hF
  obtain ⟨j', n₀, y, B, n₁, w₁, φ, z, hj', hydef, hB, hbB,
      hφ, hzdef, hzinj, hw₁, hzlim, hzopen, hzrep, hzregular⟩ :=
    hA.exists_restrictedPairMergeExceptionalGraphSequence_q_add_two
      D representative offset R hDomain F hF x w₀ i (i.succAbove j)
        hK S hxinj hxmem hw₀ hxlim hxrep (Fin.succAbove_ne i j).symm hxi
  have hj'eq : j' = j := Fin.succAbove_right_injective hj'
  subst j'
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let Dg := restrictedPairMergeExceptionalGraphBox D N
  let rep := restrictedPairMergeCommonJetRepresentative representative i j S
  let off := restrictedPairMergeCommonJetOffset D representative offset i j S
  let aug := restrictedPairMergeDenominatorClearedAugmentedEquationFamily
    A D representative offset K k i j S Q
  obtain ⟨R', hDomain'⟩ :=
    exists_restrictedBaseClosedDomain_subset_AbelJetDomain
      (a := a) Dg rep off
  have hfinite :
      (regularZeroSet (restrictedBaseOpenDomain Dg R')
        (constraintMap aug)).Finite := by
    have hgen := restrictedPairMergeExceptionalCommonJetGenerators_eq_common
      (a := a) A D representative offset i j S
    have htower :=
      exists_commonTower_restrictedPairMergeDenominatorClearedAugmentedEquationFamily
        (a := a) A D representative offset K k i j S Q
    rw [hgen] at htower
    obtain ⟨ell, T, hT⟩ := htower
    have hbase : RestrictedBaseRegularZeroFinite A Dg rep off :=
      hlower Dg rep off
    let oldCount := (((q + 2) + p) + a) + N
    let newCount := ((q + 1) + ((p + 1) + N)) + a
    have hdim : oldCount = newCount := by
      simp only [oldCount, newCount]
      omega
    let eidx : Fin oldCount ≃ Fin newCount :=
      Equiv.cast (congrArg Fin hdim)
    let qout : (Fin oldCount → ℝ) ≃L[ℝ] (Fin newCount → ℝ) :=
      ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin newCount ↦ ℝ) eidx
    let augSquare : Fin newCount →
        RestrictedPairMergeExceptionalGraphSource
          (p := p) (a := a) representative i j S → ℝ :=
      fun r z' ↦ aug (eidx.symm r) z'
    have hSquareMap : constraintMap augSquare = qout ∘ constraintMap aug := by
      funext z' r
      change aug (eidx.symm r) z' =
        (Equiv.piCongrLeft (fun _ : Fin newCount ↦ ℝ) eidx)
          (constraintMap aug z') r
      rw [Equiv.piCongrLeft_apply]
      simp [constraintMap]
    have hTSquare : ∀ r, augSquare r ∈ T.level ell := by
      intro r
      exact hT (eidx.symm r)
    have hfiniteSquare :
        (regularZeroSet (restrictedBaseOpenDomain Dg R')
          (constraintMap augSquare)).Finite := by
      simpa only [Dg, rep, off, augSquare, newCount, N] using
        (hA.finite_regularZeroSet_terminalLevel_of_base
          rep off hbase T R' hDomain' augSquare hTSquare)
    have hset := regularZeroSet_preimage_continuousLinearEquiv
      (ContinuousLinearEquiv.refl ℝ
        (RestrictedPairMergeExceptionalGraphSource
          (p := p) (a := a) representative i j S))
      qout (restrictedBaseOpenDomain Dg R') (constraintMap aug)
    have hset' :
        regularZeroSet (restrictedBaseOpenDomain Dg R')
            (constraintMap augSquare) =
          regularZeroSet (restrictedBaseOpenDomain Dg R')
            (constraintMap aug) := by
      simpa only [hSquareMap, Set.preimage_id, Function.comp_id,
        ContinuousLinearEquiv.coe_refl'] using hset
    rw [hset'] at hfiniteSquare
    exact hfiniteSquare
  let sample : ℕ → ℕ := fun n ↦ n₁ + φ n
  let oldIndex : ℕ → ℕ := fun n ↦ n₀ + sample n
  have hsample : Tendsto sample atTop atTop := by
    have hadd : Tendsto (fun n : ℕ ↦ n₁ + n) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat n₁
    exact hadd.comp hφ.tendsto_atTop
  have holdIndex : Tendsto oldIndex atTop atTop := by
    have hadd : Tendsto (fun n : ℕ ↦ n₀ + n) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat n₀
    exact hadd.comp hsample
  have hxiPos : ∀ᶠ n in atTop, 0 < (x (oldIndex n)).1.1 i :=
    ((hxrep i).comp holdIndex).eventually (eventually_gt_atTop 0)
  have hxjPos : ∀ᶠ n in atTop,
      0 < (x (oldIndex n)).1.1 (i.succAbove j) :=
    ((hxrep (i.succAbove j)).comp holdIndex).eventually
      (eventually_gt_atTop 0)
  have hyopen : ∀ n, (y (sample n)).1.2 ∈
      (restrictedPairMergeBox D).openBox := by
    intro n
    have hopen :=
      (mem_openBox_restrictedPairMergeExceptionalGraphBox_iff
        D (z n).1.2).mp (hzopen n)
    rw [hzdef n] at hopen
    simpa only [sample,
      restrictedPairMergeExceptionalFiniteGraphLift,
      restrictedPairMergeExceptionalGraphLift_box_castAdd] using hopen.1
  have hzrepR : ∀ᶠ n in atTop, ∀ r, R < (z n).1.1 r :=
    Filter.eventually_all.mpr fun r ↦
      (hzrep r).eventually (eventually_gt_atTop R)
  have hzrepR' : ∀ᶠ n in atTop, ∀ r, R' < (z n).1.1 r :=
    Filter.eventually_all.mpr fun r ↦
      (hzrep r).eventually (eventually_gt_atTop R')
  have htail : ∀ᶠ n in atTop,
      ∀ t, B t + 2 <
        restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration
            representative i j S t) (y (sample n)) := by
    rw [Filter.eventually_all]
    intro t
    have hlarge : ∀ᶠ n in atTop, B t + 3 < (z n).1.1 j :=
      (hzrep j).eventually (eventually_gt_atTop (B t + 3))
    filter_upwards [hlarge] with n hn
    have hlast : -1 < (y (sample n)).1.2 (Fin.last p) := by
      have hopen := hyopen n
      rw [restrictedPairMergeBox, D.mem_openBox_snoc] at hopen
      exact hopen.2.1
    have hrepEq : (y (sample n)).1.1 j = (z n).1.1 j := by
      rw [hzdef n]
      rfl
    unfold restrictedPairMergeExceptionalBaseArgument
    split
    · rw [hrepEq]
      linarith
    · rw [hrepEq]
      linarith
  have hzFullDomain : ∀ᶠ n in atTop,
      z n ∈ restrictedBaseOpenDomain Dg R' := by
    filter_upwards [hzrepR'] with n hn
    exact ⟨hn, by simpa only [Dg, N] using hzopen n⟩
  have hzAugmented : ∀ᶠ n in atTop,
      z n ∈ regularZeroSet
        (restrictedPairMergeExceptionalFlatCombinedDomain
          D R representative i j S) (constraintMap aug) := by
    filter_upwards [hxiPos, hxjPos, hzrepR, htail] with n hin hjn hrep hnTail
    have hsource :
        restrictedPairMergeSourceMap K k i j (y (sample n)) =
          x (oldIndex n) := by
      rw [hydef (sample n)]
      exact restrictedPairMergeSourceMap_pullback K k i j
        (x (oldIndex n)) hin hjn
    have hyPos : y (sample n) ∈ restrictedPairMergeTail j := by
      rw [hydef (sample n)]
      exact restrictedPairMergePullback_mem_tail K k i j
        (x (oldIndex n)) hin hjn
    have holdDomain :
        restrictedPairMergeSourceMap K k i j (y (sample n)) ∈
          restrictedAbelJetDomain (a := a) D representative offset := by
      rw [hsource]
      exact hDomain
        (restrictedBaseOpenDomain_subset_closedDomain D R (hxmem (oldIndex n)).1)
    have hFdiff : DifferentiableAt ℝ (constraintMap F)
        (restrictedPairMergeSourceMap K k i j (y (sample n))) := by
      rw [hsource]
      exact hA.differentiableAt_constraintMap_pairGraph_of_mem_base
        D representative offset R hDomain F hF (hxmem (oldIndex n)).1
    have hyDomain : y (sample n) ∈
        restrictedBaseOpenDomain (restrictedPairMergeBox D) R := by
      refine ⟨?_, hyopen n⟩
      intro r
      have hrepEq : (y (sample n)).1.1 r = (z n).1.1 r := by
        rw [hzdef n]
        rfl
      rw [hrepEq]
      exact hrep r
    have hsourceDiff : DifferentiableAt ℝ
        (restrictedPairMergeSourceMap K k i j) (y (sample n)) :=
      ((contDiff_restrictedPairMergeSourceMap
        (p := p) (a := a) K k i j).differentiable
          (by simp)).differentiableAt
    have holdRegular :
        restrictedPairMergeSourceMap K k i j (y (sample n)) ∈
          regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) := by
      rw [hsource]
      exact hxmem (oldIndex n)
    have htransport := mem_regularZeroSet_comp_equiv_of_surjective_fderiv
      (ContinuousLinearEquiv.refl ℝ
        (Fin (((q + 2) + p) + a) → ℝ))
      (restrictedBaseOpenDomain D R) (constraintMap F) (y (sample n))
      hsourceDiff hFdiff
      (bijective_fderiv_restrictedPairMergeSourceMap
        K k i j (x := y (sample n)) hyPos.1 hyPos.2).2
    have hpull := htransport.mpr holdRegular
    have hpull' : y (sample n) ∈
        regularZeroSet
          (restrictedPairMergeSourceMap K k i j ⁻¹'
            restrictedBaseOpenDomain D R)
          (constraintMap F ∘ restrictedPairMergeSourceMap K k i j) := by
      simpa only [ContinuousLinearEquiv.coe_refl', Function.id_comp] using hpull
    have hlowerRegular : y (sample n) ∈
        regularZeroSet
          (restrictedBaseOpenDomain (restrictedPairMergeBox D) R)
          (constraintMap F ∘ restrictedPairMergeSourceMap K k i j) :=
      ⟨hyDomain, hpull'.2.1, hpull'.2.2⟩
    rw [hzdef n]
    exact
      (hA.mem_regularZeroSet_pairMergeDenominatorClearedAugmented_graphLift_iff
        D representative offset hK i j S Q F hQ B hB hbB R
          (y (sample n)) holdDomain (hyopen n) hnTail hFdiff).2
        hlowerRegular
  have hzFiniteSet : ∀ᶠ n in atTop,
      z n ∈ regularZeroSet (restrictedBaseOpenDomain Dg R')
        (constraintMap aug) := by
    filter_upwards [hzFullDomain, hzAugmented] with n hnew hold
    exact ⟨hnew, hold.2.1, hold.2.2⟩
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hzFiniteSet
  let ztail : ℕ → RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S :=
    fun n ↦ z (n₂ + n)
  have htailInjective : Function.Injective ztail := by
    intro r s hrs
    have hindex : n₂ + r = n₂ + s := hzinj hrs
    exact Nat.add_left_cancel hindex
  have htailMem : ∀ n, ztail n ∈
      regularZeroSet (restrictedBaseOpenDomain Dg R')
        (constraintMap aug) := by
    intro n
    exact hn₂ (n₂ + n) (Nat.le_add_right n₂ n)
  exact (Set.infinite_of_injective_forall_mem htailInjective htailMem) hfinite

end AbelFormalization
