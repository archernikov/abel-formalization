import AbelFormalization.ExponentialLogComparisonJacobian
import AbelFormalization.ExponentialAdjunctionJacobian

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The open one-dimensional locus `V` from the exponential-adjunction
argument, before adding the boundary reciprocal. -/
def exponentialAdjunctionOpenLocus {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) : Set (E × ℝ) :=
  {p | p.1 ∈ Omega ∧ Ftilde p = 0 ∧ 0 < p.2 ∧
    exponentialAdjunctionJacobian Ftilde g basis p ≠ 0}

theorem mem_exponentialAdjunctionOpenLocus_iff {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) :
    p ∈ exponentialAdjunctionOpenLocus Omega Ftilde g basis ↔
      p.1 ∈ Omega ∧ Ftilde p = 0 ∧ 0 < p.2 ∧
        exponentialAdjunctionJacobian Ftilde g basis p ≠ 0 :=
  Iff.rfl

theorem mem_openLocus_and_comparison_zero_iff_regularZero {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (x : E) (Y : ℝ)
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x) :
    ((x, Y) ∈ exponentialAdjunctionOpenLocus Omega Ftilde g basis ∧
        exponentialGraphComparison g (x, Y) = 0) ↔
      Y = Real.exp (g x) ∧
        x ∈ regularZeroSet Omega (exponentialGraphSubstitution Ftilde g) := by
  constructor
  · rintro ⟨hV, hcomparison⟩
    have hY : Y = Real.exp (g x) :=
      (exponentialGraphComparison_eq_zero_iff g hV.2.2.1).mp hcomparison
    have hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g)
        (x, Real.exp (g x)) := by
      unfold exponentialGraphLiftSystem graphLiftSystem
      fun_prop
    have hJglobal : exponentialAdjunctionJacobian Ftilde g basis
        (x, Real.exp (g x)) ≠ 0 := by
      simpa only [hY] using hV.2.2.2
    have hJ : exponentialGraphJacobian Ftilde g basis
        (x, Real.exp (g x)) ≠ 0 := by
      rwa [exponentialAdjunctionJacobian_on_graph Ftilde g basis hg]
        at hJglobal
    have hsurj : Function.Surjective
        (fderiv ℝ (exponentialGraphLiftSystem Ftilde g)
          (x, Real.exp (g x))) :=
      (exponentialGraphJacobian_ne_zero_iff_surjective
        Ftilde g basis (x, Real.exp (g x)) hG).mp hJ
    have hFzero : Ftilde (x, Real.exp (g x)) = 0 := by
      simpa only [hY] using hV.2.1
    have hlift : (x, Real.exp (g x)) ∈ regularZeroSet
        ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
        (exponentialGraphLiftSystem Ftilde g) := by
      refine ⟨hV.1, ?_, hsurj⟩
      simp [exponentialGraphLiftSystem, graphLiftSystem, hFzero]
    exact ⟨hY, (mem_regularZeroSet_exponentialGraphLift_iff hF hg).mpr hlift⟩
  · rintro ⟨rfl, hx⟩
    refine ⟨?_, exponentialGraphComparison_on_graph g x⟩
    exact ⟨hx.1, hx.2.1, Real.exp_pos (g x),
      exponentialAdjunctionJacobian_ne_zero_of_mem_regularZeroSet
        Ftilde g basis hF hg hx⟩

/-- The original regular-zero set is canonically equivalent to the zero set
of `log Y - g` on the open locus `V`. -/
def regularZeroSetEquivExponentialComparisonZero {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E)
    (hF : ∀ x, DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : Differentiable ℝ g) :
    regularZeroSet Omega (exponentialGraphSubstitution Ftilde g) ≃
      {p : E × ℝ | p ∈ exponentialAdjunctionOpenLocus Omega Ftilde g basis ∧
        exponentialGraphComparison g p = 0} where
  toFun x := ⟨(x, Real.exp (g x)),
    (mem_openLocus_and_comparison_zero_iff_regularZero
      Omega Ftilde g basis x (Real.exp (g x)) (hF x) (hg x)).mpr
        ⟨rfl, x.property⟩⟩
  invFun p := ⟨p.1.1,
    ((mem_openLocus_and_comparison_zero_iff_regularZero
      Omega Ftilde g basis p.1.1 p.1.2 (hF p.1.1) (hg p.1.1)).mp
        p.property).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    have hY := ((mem_openLocus_and_comparison_zero_iff_regularZero
      Omega Ftilde g basis p.1.1 p.1.2 (hF p.1.1) (hg p.1.1)).mp
        p.property).1
    exact Prod.ext rfl hY.symm

/-- Domain-local form of the canonical exponential-graph correspondence.
Only differentiability at points of `Omega` is used in the proof. -/
def regularZeroSetEquivExponentialComparisonZeroOn {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E)
    (hF : ∀ x ∈ Omega,
      DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : ∀ x ∈ Omega, DifferentiableAt ℝ g x) :
    regularZeroSet Omega (exponentialGraphSubstitution Ftilde g) ≃
      {p : E × ℝ | p ∈ exponentialAdjunctionOpenLocus Omega Ftilde g basis ∧
        exponentialGraphComparison g p = 0} where
  toFun x := ⟨(x, Real.exp (g x)),
    (mem_openLocus_and_comparison_zero_iff_regularZero
      Omega Ftilde g basis x (Real.exp (g x))
        (hF x x.property.1) (hg x x.property.1)).mpr
          ⟨rfl, x.property⟩⟩
  invFun p := ⟨p.1.1, by
    have hpOmega : p.1.1 ∈ Omega := p.property.1.1
    exact ((mem_openLocus_and_comparison_zero_iff_regularZero
      Omega Ftilde g basis p.1.1 p.1.2
        (hF p.1.1 hpOmega) (hg p.1.1 hpOmega)).mp p.property).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    have hpOmega : p.1.1 ∈ Omega := p.property.1.1
    have hY := ((mem_openLocus_and_comparison_zero_iff_regularZero
      Omega Ftilde g basis p.1.1 p.1.2
        (hF p.1.1 hpOmega) (hg p.1.1 hpOmega)).mp p.property).1
    exact Prod.ext rfl hY.symm


/-- Natural positive graph domain for the lower-level square comparison
system. -/
def exponentialAdjunctionComparisonDomain (Omega : Set E) : Set (E × ℝ) :=
  ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega) ∩ {p | 0 < p.2}

theorem exponentialGraphPoint_mem_regularZeroSet_logComparison {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x)
    (hx : x ∈ regularZeroSet Omega
      (exponentialGraphSubstitution Ftilde g)) :
    (x, Real.exp (g x)) ∈ regularZeroSet
      (exponentialAdjunctionComparisonDomain Omega)
      (constraintMap (exponentialLogComparisonTuple Ftilde g)) := by
  let p : E × ℝ := (x, Real.exp (g x))
  have htuple : ∀ i, DifferentiableAt ℝ
      (exponentialLogComparisonTuple Ftilde g i) p := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hcomparison : DifferentiableAt ℝ
          (exponentialGraphComparison g) p := by
        have hlog : DifferentiableAt ℝ (fun q : E × ℝ ↦ Real.log q.2) p :=
          (ContinuousLinearMap.snd ℝ E ℝ).differentiableAt.log
            (Real.exp_ne_zero (g x))
        have hgcomp : DifferentiableAt ℝ (fun q : E × ℝ ↦ g q.1) p :=
          hg.comp p (ContinuousLinearMap.fst ℝ E ℝ).differentiableAt
        exact hlog.sub hgcomp
      simpa [exponentialLogComparisonTuple] using hcomparison
    · simpa [exponentialLogComparisonTuple, Function.comp_def] using
        (differentiableAt_apply j (Ftilde p)).comp p hF
  refine ⟨⟨hx.1, Real.exp_pos (g x)⟩, ?_, ?_⟩
  · funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [constraintMap, exponentialLogComparisonTuple,
        exponentialGraphComparison]
    · simpa [p, constraintMap, exponentialLogComparisonTuple] using
        congrFun hx.2.1 j
  · rw [fderiv_constraintMap_eq_constraintFDeriv
      (exponentialLogComparisonTuple Ftilde g) p htuple]
    apply LinearMap.range_eq_top.mp
    apply (constraintJacobianInBasis_det_ne_zero_iff_surjective
      (exponentialLogComparisonTuple Ftilde g) (graphProductBasis basis) p).mp
    rw [← exponentialLogComparisonJacobian_eq_det_constraintJacobian]
    exact exponentialLogComparisonJacobian_ne_zero_of_mem_regularZeroSet
      Ftilde g basis hF hg hx


/-- Finiteness of the lower-level logarithmic square system implies
finiteness of the original regular zeros. -/
theorem finite_regularZeroSet_of_finite_logComparison {n : ℕ}
    (Omega : Set E) (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E)
    (hF : ∀ x, DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : Differentiable ℝ g)
    (hfinite : (regularZeroSet (exponentialAdjunctionComparisonDomain Omega)
      (constraintMap (exponentialLogComparisonTuple Ftilde g))).Finite) :
    (regularZeroSet Omega
      (exponentialGraphSubstitution Ftilde g)).Finite := by
  apply Set.Finite.of_finite_image
    (f := fun x ↦ (x, Real.exp (g x)))
  · exact hfinite.subset fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := hy
      exact exponentialGraphPoint_mem_regularZeroSet_logComparison
        Omega Ftilde g basis (hF x) (hg x) hx
  · exact (exponentialGraphLift_injective g).injOn

end AbelFormalization
