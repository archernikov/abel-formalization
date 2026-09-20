import AbelFormalization.CommonStripHermiteAnalytic

noncomputable section
set_option autoImplicit false

open Set Metric Polynomial
open scoped Topology

namespace AbelFormalization

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compose the joint complex Hermite coefficient with arbitrary real-analytic
center and real-node maps. -/
theorem normalizedHermiteCoeff_re_analyticAt_commonStrip_real
    {F : ℂ → ℂ} {X B : ℝ} (hB : 0 < B)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    (center : E → ℝ) (nodes : E → ι → ℝ) {x : E}
    (hcenter : AnalyticAt ℝ center x)
    (hnodes : AnalyticAt ℝ nodes x)
    (hxcenter : (center x : ℂ) ∈ rightHalfStrip (X + B + 1) 1)
    (hxnodes : (fun i => (nodes x i : ℂ)) ∈ hermiteNodeNeighborhood B) :
    AnalyticAt ℝ (fun y =>
      (normalizedCoeff
        (hermiteContourPolynomial
          (fun z => F ((center y : ℂ) + z))
          (nodePolynomial (fun i => (nodes y i : ℂ)) m) (B + 1)) r).re) x := by
  have hcenterC : AnalyticAt ℝ (fun y => (center y : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt (center x)).comp hcenter
  have hnodesC : AnalyticAt ℝ (fun y => fun i => (nodes y i : ℂ)) x := by
    apply AnalyticAt.pi
    intro i
    have hi : AnalyticAt ℝ (fun y => nodes y i) x :=
      ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : ι => ℝ) i).analyticAt (nodes x)).fun_comp hnodes
    exact (Complex.ofRealCLM.analyticAt (nodes x i)).fun_comp
      (f := fun y => nodes y i) hi
  have hjoint := normalizedHermiteCoeff_analyticAt_commonStrip hB hF m hr
    hxcenter hxnodes
  have hcomp : AnalyticAt ℝ (fun y =>
      normalizedCoeff
        (hermiteContourPolynomial
          (fun z => F ((center y : ℂ) + z))
          (nodePolynomial (fun i => (nodes y i : ℂ)) m) (B + 1)) r) x :=
    hjoint.restrictScalars.fun_comp
      (f := fun y => ((center y : ℂ), fun i => (nodes y i : ℂ)))
      (hcenterC.prod hnodesC)
  exact (Complex.reCLM.analyticAt _).fun_comp hcomp

end AbelFormalization
