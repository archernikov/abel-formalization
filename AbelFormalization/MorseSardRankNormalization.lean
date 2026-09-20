import AbelFormalization.WilkieArbitraryMinorDerivativeBridge
import AbelFormalization.SmoothFamilyConstantRankLocalFiber

/-!
# Local rank normalization for rectangular Morse--Sard

At a point where a map has exact rank `k`, choose a nonzero `k × k`
Jacobian minor.  The selected outputs together with the complementary source
coordinates form a local inverse-function chart.  Along the chart slice on
which the selected outputs are fixed, the full map has derivative zero.

This is the rank-normalization step that reduces the general nonflat
Morse--Sard induction to the rank-zero decomposition in
`MorseSardNonflatHypersurface`.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## A chart lemma with the fixed coordinate in the second factor -/

/-- If the kernels of `Df` and `Dg` agree and an inverse chart records `f` in
its second coordinate, then the derivative of `g` along the first-coordinate
slice is zero. -/
theorem fderiv_const_snd_openPartialHomeomorph_eq_zero
    {E F G K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (f : E → F) (g : E → G) (e : OpenPartialHomeomorph E (K × F))
    (hsnd : ∀ y, (e y).2 = f y) {q : K × F}
    (hq : q ∈ e.target) (hinv : DifferentiableAt ℝ e.symm q)
    (hf : DifferentiableAt ℝ f (e.symm q))
    (hg : DifferentiableAt ℝ g (e.symm q))
    (hker : LinearMap.ker (fderiv ℝ g (e.symm q)).toLinearMap =
      LinearMap.ker (fderiv ℝ f (e.symm q)).toLinearMap) :
    fderiv ℝ (fun z : K ↦ g (e.symm (z, q.2))) q.1 = 0 := by
  have hpair : HasFDerivAt (fun z : K ↦ (z, q.2))
      (ContinuousLinearMap.inl ℝ K F) q.1 :=
    hasFDerivAt_prodMk_left q.1 q.2
  have hinvPair : HasFDerivAt (fun z : K ↦ e.symm (z, q.2))
      ((fderiv ℝ e.symm q).comp (ContinuousLinearMap.inl ℝ K F)) q.1 :=
    hinv.hasFDerivAt.comp q.1 hpair
  have htotal : HasFDerivAt (fun z : K ↦ g (e.symm (z, q.2)))
      ((fderiv ℝ g (e.symm q)).comp
        ((fderiv ℝ e.symm q).comp (ContinuousLinearMap.inl ℝ K F))) q.1 :=
    hg.hasFDerivAt.comp q.1 hinvPair
  rw [htotal.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    zero_apply]
  let tangent := fderiv ℝ e.symm q (v, 0)
  have hright :
      (fun p : K × F ↦ f (e.symm p)) =ᶠ[nhds q] fun p ↦ p.2 :=
    (e.eventually_right_inverse hq).mono fun p hp ↦
      (hsnd (e.symm p)).symm.trans (congrArg Prod.snd hp)
  have hcomp : HasFDerivAt (fun p : K × F ↦ f (e.symm p))
      ((fderiv ℝ f (e.symm q)).comp (fderiv ℝ e.symm q)) q :=
    hf.hasFDerivAt.comp q hinv.hasFDerivAt
  have htangentSelected : fderiv ℝ f (e.symm q) tangent = 0 := by
    have hderiv := congrArg
      (fun L : (K × F) →L[ℝ] F ↦ L (v, 0)) hright.fderiv_eq
    rw [hcomp.fderiv] at hderiv
    rw [fderiv_snd] at hderiv
    change fderiv ℝ f (e.symm q) tangent = (0 : F) at hderiv
    exact hderiv
  have htangentMemSelected :
      tangent ∈ LinearMap.ker (fderiv ℝ f (e.symm q)).toLinearMap := by
    apply LinearMap.mem_ker.mpr
    exact htangentSelected
  have htangentMemFull :
      tangent ∈ LinearMap.ker (fderiv ℝ g (e.symm q)).toLinearMap := by
    rw [hker]
    exact htangentMemSelected
  exact LinearMap.mem_ker.mp htangentMemFull

/-! ## Exact-rank points normalize to rank zero on a residual slice -/

/-- At an exact rank-`k` point of a map on `ℝ^(n+k)`, a selected-minor
inverse-function chart has a residual `ℝⁿ` slice on which the full map has
zero derivative at the corresponding point.

The chart itself is returned because the next Morse--Sard step must transport
the nonflat hypersurface cover through it and then apply source-dimension
induction. -/
theorem exists_rankZeroResidualChart_of_mem_standardJacobianRankLocus
    {n b k : ℕ} {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) {x : RealEuclidean (n + k)}
    (hx : x ∈ standardJacobianRankLocus g k) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin (n + k),
      ∃ e : OpenPartialHomeomorph (RealEuclidean (n + k))
          (RealEuclidean n × RealEuclidean k),
        x ∈ e.source ∧
          (∀ y, e y =
            (wilkieColumnComplementaryProjection cols y,
              selectedOutputMap g rows y)) ∧
          fderiv ℝ
            (fun u : RealEuclidean n ↦
              g (e.symm
                (u, selectedOutputMap g rows x)))
            (wilkieColumnComplementaryProjection cols x) = 0 := by
  have hminors :=
    (finrank_range_fderiv_eq_iff_standardJacobianMinors
      (hg.differentiable one_ne_zero x)).mp hx
  obtain ⟨rows, cols, hminor⟩ := hminors.1
  let f : RealEuclidean (n + k) → RealEuclidean k :=
    selectedOutputMap g rows
  let q : RealEuclidean (n + k) →L[ℝ] RealEuclidean n :=
    wilkieColumnComplementaryProjection cols
  let M : RealEuclidean (n + k) →
      RealEuclidean n × RealEuclidean k := fun y ↦ (q y, f y)
  have hf : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (fun y i ↦ g y (rows i))
    rw [contDiff_pi]
    intro i
    exact contDiff_pi.mp hg (rows i)
  have hminorF : standardJacobianColumnMinor f cols x ≠ 0 := by
    rw [show standardJacobianColumnMinor f cols x =
        standardJacobianMinor g rows cols x by rfl]
    exact hminor
  obtain ⟨L, hMstrict⟩ :=
    wilkieColumnComplementarySquareMap_hasStrictFDerivAt_of_minor
      hf cols hminorF
  let e : OpenPartialHomeomorph (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k) :=
    hMstrict.toOpenPartialHomeomorph M
  have hxSource : x ∈ e.source :=
    hMstrict.mem_toOpenPartialHomeomorph_source
  have heApply : ∀ y, e y = (q y, f y) := by
    intro y
    rfl
  have hxTarget : e x ∈ e.target := e.map_source hxSource
  have heSymm : e.symm (e x) = x := e.left_inv hxSource
  have hMstrict' : HasStrictFDerivAt e
      (L : RealEuclidean (n + k) →L[ℝ]
        (RealEuclidean n × RealEuclidean k)) (e.symm (e x)) := by
    rw [heSymm]
    exact hMstrict
  have hinv : DifferentiableAt ℝ e.symm (e x) :=
    (e.hasStrictFDerivAt_symm hxTarget hMstrict').differentiableAt
  have hselectedSurj : Function.Surjective (fderiv ℝ f x) :=
    fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
      (hg.differentiable one_ne_zero x) rows cols hminor
  have hker : LinearMap.ker (fderiv ℝ g x).toLinearMap =
      LinearMap.ker (fderiv ℝ f x).toLinearMap :=
    ker_fderiv_eq_ker_fderiv_selectedOutputMap_of_rank_le
      (hg.differentiable one_ne_zero x) rows hselectedSurj hx.le
  have hzero := fderiv_const_snd_openPartialHomeomorph_eq_zero
    f g e (fun y ↦ congrArg Prod.snd (heApply y)) hxTarget hinv
    (by simpa only [heSymm] using (hf.differentiable one_ne_zero x))
    (by simpa only [heSymm] using (hg.differentiable one_ne_zero x))
    (by simpa only [heSymm] using hker)
  refine ⟨rows, cols, e, hxSource, ?_, ?_⟩
  · intro y
    simpa only [f, q] using heApply y
  · have hex : e x = (q x, f x) := heApply x
    have hfst : (e x).1 = q x := congrArg Prod.fst hex
    have hsnd : (e x).2 = f x := congrArg Prod.snd hex
    simpa only [f, q, hfst, hsnd] using hzero

/-! ## A whole chart neighborhood for the induction step -/

/-- The rank-normalizing chart can be chosen on an open neighborhood on
which its inverse retains all the available differentiability.  On every
point of that neighborhood where the full derivative has rank at most `k`,
the residual `n`-dimensional slice has derivative zero.

This is the local normal form needed by the rectangular Morse--Sard
induction: the selected `k` output coordinates become the second chart
coordinate, while the remaining source variables carry a rank-zero map.
The conclusion is neighborhood-wise rather than only a statement at the
chart center. -/
theorem exists_rankZeroResidualChartNeighborhood_of_mem_standardJacobianRankLocus
    {n b k r : ℕ} {g : RealEuclidean (n + k) → RealEuclidean b}
    (hr : 0 < r) (hg : ContDiff ℝ r g)
    {x : RealEuclidean (n + k)}
    (hx : x ∈ standardJacobianRankLocus g k) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin (n + k),
      ∃ e : OpenPartialHomeomorph (RealEuclidean (n + k))
          (RealEuclidean n × RealEuclidean k),
        ∃ U : Set (RealEuclidean (n + k)),
          IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
          (∀ y, e y =
            (wilkieColumnComplementaryProjection cols y,
              selectedOutputMap g rows y)) ∧
          (∀ y ∈ U, ContDiffAt ℝ r e.symm (e y)) ∧
          (∀ y ∈ U,
            ContDiffAt ℝ r
              (fun u : RealEuclidean n ↦
                g (e.symm (u, selectedOutputMap g rows y)))
              (wilkieColumnComplementaryProjection cols y)) ∧
          (∀ y ∈ U,
            Module.finrank ℝ
                (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k →
              fderiv ℝ
                (fun u : RealEuclidean n ↦
                  g (e.symm (u, selectedOutputMap g rows y)))
                (wilkieColumnComplementaryProjection cols y) = 0) := by
  have hgone : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast hr)
  have hminors :=
    (finrank_range_fderiv_eq_iff_standardJacobianMinors
      (hgone.differentiable one_ne_zero x)).mp hx
  obtain ⟨rows, cols, hminor⟩ := hminors.1
  let f : RealEuclidean (n + k) → RealEuclidean k :=
    selectedOutputMap g rows
  let q : RealEuclidean (n + k) →L[ℝ] RealEuclidean n :=
    wilkieColumnComplementaryProjection cols
  let M : RealEuclidean (n + k) →
      RealEuclidean n × RealEuclidean k := fun y ↦ (q y, f y)
  have hf : ContDiff ℝ r f := by
    change ContDiff ℝ r (fun y i ↦ g y (rows i))
    rw [contDiff_pi]
    intro i
    exact contDiff_pi.mp hg (rows i)
  have hfone : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast hr)
  have hminorF : standardJacobianColumnMinor f cols x ≠ 0 := by
    rw [show standardJacobianColumnMinor f cols x =
        standardJacobianMinor g rows cols x by rfl]
    exact hminor
  obtain ⟨L, hMstrict⟩ :=
    wilkieColumnComplementarySquareMap_hasStrictFDerivAt_of_minor
      hfone cols hminorF
  let e : OpenPartialHomeomorph (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k) :=
    hMstrict.toOpenPartialHomeomorph M
  have hxSource : x ∈ e.source :=
    hMstrict.mem_toOpenPartialHomeomorph_source
  have heApply : ∀ y, e y = (q y, f y) := by
    intro y
    rfl
  have hM : ContDiff ℝ r M := q.contDiff.prodMk hf
  have hxTarget : e x ∈ e.target := e.map_source hxSource
  have heSymmX : e.symm (e x) = x := e.left_inv hxSource
  have hinverseAt : ContDiffAt ℝ r e.symm (e x) := by
    apply e.contDiffAt_symm hxTarget
    · rw [heSymmX]
      exact hMstrict.hasFDerivAt
    · rw [heSymmX]
      exact hM.contDiffAt
  have hminorContinuous : Continuous (standardJacobianMinor g rows cols) :=
    continuous_standardJacobianMinor_of_contDiff_one hgone rows cols
  have hminorEventually :
      ∀ᶠ y in 𝓝 x, standardJacobianMinor g rows cols y ≠ 0 :=
    (isOpen_ne_fun hminorContinuous continuous_const).eventually_mem hminor
  have htendsto : Tendsto e.symm (𝓝 (e x)) (𝓝 x) :=
    e.tendsto_symm hxSource
  have hgood : ∀ᶠ p in 𝓝 (e x),
      p ∈ e.target ∧ ContDiffAt ℝ r e.symm p ∧
        standardJacobianMinor g rows cols (e.symm p) ≠ 0 := by
    filter_upwards [e.open_target.eventually_mem hxTarget,
      hinverseAt.eventually (by simp), htendsto.eventually hminorEventually]
      with p hpTarget hpInverse hpMinor
    exact ⟨hpTarget, hpInverse, hpMinor⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let U : Set (RealEuclidean (n + k)) :=
    e.source ∩ e ⁻¹' Metric.ball (e x) ε
  have hUopen : IsOpen U :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U :=
    ⟨hxSource, Metric.mem_ball_self hε⟩
  refine ⟨rows, cols, e, U, hUopen, hxU, inter_subset_left, ?_, ?_, ?_, ?_⟩
  · intro y
    simpa only [f, q] using heApply y
  · intro y hy
    have hyGood := hball hy.2
    simpa only [e.left_inv hy.1] using hyGood.2.1
  · intro y hy
    have hyGood := hball hy.2
    have hpair : ContDiffAt ℝ r
        (fun u : RealEuclidean n ↦ (u, f y)) (q y) :=
      (contDiff_id.prodMk contDiff_const).contDiffAt
    have hinvPair : ContDiffAt ℝ r
        (fun u : RealEuclidean n ↦ e.symm (u, f y)) (q y) := by
      have heY : e y = (q y, f y) := heApply y
      have hcomp := hyGood.2.1.comp (q y) hpair
      simpa only [Function.comp_def, heY] using hcomp
    have htotal := hg.contDiffAt.comp (q y) hinvPair
    simpa only [Function.comp_def, f, q] using htotal
  · intro y hy hrank
    have hyGood := hball hy.2
    have hyInverse : DifferentiableAt ℝ e.symm (e y) :=
      hyGood.2.1.differentiableAt (by exact_mod_cast hr.ne')
    have hyMinor : standardJacobianMinor g rows cols y ≠ 0 := by
      simpa only [e.left_inv hy.1] using hyGood.2.2
    have hsurj : Function.Surjective (fderiv ℝ f y) :=
      fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
        (hgone.differentiable one_ne_zero y) rows cols hyMinor
    have hker : LinearMap.ker (fderiv ℝ g y).toLinearMap =
        LinearMap.ker (fderiv ℝ f y).toLinearMap :=
      ker_fderiv_eq_ker_fderiv_selectedOutputMap_of_rank_le
        (hgone.differentiable one_ne_zero y) rows hsurj hrank
    have hzero := fderiv_const_snd_openPartialHomeomorph_eq_zero
      f g e (fun z ↦ congrArg Prod.snd (heApply z))
      hyGood.1 (by simpa only [e.left_inv hy.1] using hyInverse)
      (by simpa only [e.left_inv hy.1] using
        (hfone.differentiable one_ne_zero y))
      (by simpa only [e.left_inv hy.1] using
        (hgone.differentiable one_ne_zero y))
      (by simpa only [e.left_inv hy.1] using hker)
    have heY : e y = (q y, f y) := heApply y
    simpa only [f, q, heY] using hzero

end AbelFormalization
