import AbelFormalization.ParametricDividedDifference
import AbelFormalization.CentralCoefficientAnalytic
import AbelFormalization.AbelHermiteFamily

/-!
# Joint holomorphy of the central divided-difference remainder

The center, nodes, and scale are independent complex variables. Analyticity
of the actual central coefficient on a closed scale disk allows the generic
parametric divided-difference theorem to extend joint holomorphy through
zero scale. The node neighborhood remains the fixed one from the Hermite family.
-/

noncomputable section

namespace AbelFormalization

open Set Metric

variable {ι : Type*} [Fintype ι]

/-- The independent complex parameter domain in the manuscript, with center
and nodes grouped together and scale in the final coordinate. -/
def centralParameterDomain (X ε B : ℝ) : Set ((ℂ × (ι → ℂ)) × ℂ) :=
  (rightHalfStrip X ε ×ˢ hermiteNodeNeighborhood B) ×ˢ ball (0 : ℂ) ε

theorem isOpen_centralParameterDomain {B : ℝ} (hB : 0 < B) (X ε : ℝ) :
    IsOpen (centralParameterDomain (ι := ι) X ε B) :=
  ((isOpen_rightHalfStrip X ε).prod (isOpen_hermiteNodeNeighborhood hB)).prod isOpen_ball

/-- The actual divided-difference remainder is jointly complex Fréchet
differentiable in all independent parameters, including zero scale. -/
theorem centralRemainder_differentiableOn_joint
    {F : ℂ → ℂ} {X B : ℝ} (hB : 0 < B)
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (rightHalfStrip X 1 ×ˢ ball (0 : ℂ) (1 / 2)))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m) :
    DifferentiableOn ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralRemainder F m (1 / 4) v.1.1 v.2 v.1.2 r)
      ((rightHalfStrip X 1 ×ˢ hermiteNodeNeighborhood B) ×ˢ
        ball (0 : ℂ) (centralScaleRadius B / 2)) := by
  have hρ : 0 < centralScaleRadius B := centralScaleRadius_pos hB
  have ha : AnalyticOnNhd ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralCoefficient F m (1 / 4) v.1.1 v.2 v.1.2 r)
      ((rightHalfStrip X 1 ×ˢ hermiteNodeNeighborhood B) ×ˢ
        closedBall (0 : ℂ) (centralScaleRadius B / 2)) := by
    apply (centralCoefficient_analyticOnNhd_joint hB hH m hr).mono
    intro v hv
    refine ⟨⟨hv.1.1, fun i => (hv.1.2 i).le⟩, ?_⟩
    exact closedBall_subset_ball (half_lt_self hρ) hv.2
  simpa only [centralRemainder] using
    (differentiableOn_analyticRemainder_parameters
      (f := fun v : (ℂ × (ι → ℂ)) × ℂ =>
        centralCoefficient F m (1 / 4) v.1.1 v.2 v.1.2 r)
      (U := rightHalfStrip X 1 ×ˢ hermiteNodeNeighborhood B)
      (ρ := centralScaleRadius B / 2)
      ((isOpen_rightHalfStrip X 1).prod (isOpen_hermiteNodeNeighborhood hB)) (half_pos hρ) ha)

omit [Fintype ι] in
/-- Moving the threshold to the right and decreasing both radii stays inside
the uniform joint-holomorphy domain. -/
theorem centralParameterDomain_subset_joint {X X' ε B : ℝ}
    (hX : X ≤ X') (hε : ε ≤ 1) (hq : ε ≤ centralScaleRadius B / 2) :
    centralParameterDomain (ι := ι) X' ε B ⊆
      (rightHalfStrip X 1 ×ˢ hermiteNodeNeighborhood B) ×ˢ
        ball (0 : ℂ) (centralScaleRadius B / 2) := by
  intro v hv
  exact ⟨⟨⟨hX.trans_lt hv.1.1.1, hv.1.1.2.trans_le hε⟩, hv.1.2⟩,
    ball_subset_ball hq hv.2⟩

/-- The domain form used in the full Hermite remainder statement. -/
theorem centralRemainder_differentiableOn_domain
    {F : ℂ → ℂ} {X X' ε B : ℝ} (hB : 0 < B)
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (rightHalfStrip X 1 ×ˢ ball (0 : ℂ) (1 / 2)))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    (hX : X ≤ X') (hε : ε ≤ 1) (hq : ε ≤ centralScaleRadius B / 2) :
    DifferentiableOn ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralRemainder F m (1 / 4) v.1.1 v.2 v.1.2 r)
      (centralParameterDomain X' ε B) :=
  (centralRemainder_differentiableOn_joint hB hH m hr).mono
    (centralParameterDomain_subset_joint hX hε hq)

end AbelFormalization
