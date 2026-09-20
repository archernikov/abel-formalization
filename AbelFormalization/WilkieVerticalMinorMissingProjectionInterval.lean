import AbelFormalization.WilkieVerticalMinorDerivativeBridge

/-!
# A missed visible target point produces a fixed-minor interval

For a bounded regular level fiber over a connected open visible target, the
nonzero vertical-minor projection theorem has a useful contrapositive.  A
restricted component whose image misses a target point contains a zero of
that *same* vertical minor.  If the minor was nonzero at the component's base
point, connectedness gives the full initial interval of its squared values.
The assumptions state the regular value and boundedness explicitly.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A bounded regular component with a missed target point must contain a
zero of its fixed hidden-column maximal minor. -/
theorem wilkieVerticalMinor_zero_of_missed_projection
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hU : IsPreconnected U)
    (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    {x : RealEuclidean (n + k)}
    (hx : x ∈ wilkieFiberOver F a U)
    (hmissed : ∃ u ∈ U,
      u ∉ realEuclideanTakeLeft '' wilkieFiberComponent F a U x) :
    ∃ z ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) z = 0 := by
  have himageNe :
      realEuclideanTakeLeft '' wilkieFiberComponent F a U x ≠ U := by
    intro heq
    obtain ⟨u, huU, huMiss⟩ := hmissed
    exact huMiss (heq.symm ▸ huU)
  by_contra hzeroMissing
  have hminor : ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 := by
    intro y hyY hzero
    exact hzeroMissing ⟨y, hyY, hzero⟩
  exact himageNe
    (wilkieVerticalMinor_component_projection_eq_of_nonzeroMinor
      hF a hU hUopen hregular hbounded hx hminor)

/-- If the missed component starts where the same vertical minor is
nonzero, its squared values realize every sufficiently small nonnegative
level. -/
theorem wilkieVerticalMinor_squared_interval_of_missed_projection
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hU : IsPreconnected U)
    (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    {x : RealEuclidean (n + k)}
    (hx : x ∈ wilkieFiberOver F a U)
    (hminorAtX : standardJacobianColumnMinor F (Fin.natAddEmb n) x ≠ 0)
    (hmissed : ∃ u ∈ U,
      u ∉ realEuclideanTakeLeft '' wilkieFiberComponent F a U x) :
    ∃ η : ℝ, 0 < η ∧ Set.Icc (0 : ℝ) η ⊆
      (fun y ↦ (standardJacobianColumnMinor F (Fin.natAddEmb n) y) ^ 2) ''
        wilkieFiberComponent F a U x := by
  obtain ⟨z, hzY, hzZero⟩ :=
    wilkieVerticalMinor_zero_of_missed_projection
      hF a hU hUopen hregular hbounded hx hmissed
  have hxY : x ∈ wilkieFiberComponent F a U x :=
    mem_connectedComponentIn hx
  have hYpre : IsPreconnected (wilkieFiberComponent F a U x) :=
    isPreconnected_connectedComponentIn
  have hYfiber : wilkieFiberComponent F a U x ⊆ F ⁻¹' {a} := by
    intro y hyY
    exact (connectedComponentIn_subset (wilkieFiberOver F a U) x hyY).1
  exact squared_standardJacobianColumnMinor_interval_on_levelFiber
    hF a (Fin.natAddEmb n) hYpre hYfiber hzY hxY hzZero hminorAtX

end AbelFormalization
