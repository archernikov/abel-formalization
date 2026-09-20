import AbelFormalization.WilkieArbitraryMinorDerivativeBridge

/-!
# Wilkie 2.9: the finite visible projection case

When the bounded restricted regular fiber has finite visible image, its full
fiber component through a point is compact.  Regularity supplies one
nonzero maximal Jacobian minor at that point.  The arbitrary-column square
chart and compact-open obstruction force the *same* minor to vanish on the
component, and connectedness supplies a positive initial interval of its
squared values on the restricted fiber.  This is Corollary 2.9's Case 1; its
Case 2 regular-coordinate-slice induction is separate.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The unconditional fixed-minor interval in the finite-visible-image
branch of Wilkie's regular-fiber corollary. -/
theorem wilkieFiniteVisibleImage_sameMinor_squared_interval
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hn : 0 < n) (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    (hfinite : (realEuclideanTakeLeft '' wilkieFiberOver F a U).Finite)
    {x : RealEuclidean (n + k)} (hx : x ∈ wilkieFiberOver F a U) :
    ∃ cols : Fin k ↪ Fin (n + k), ∃ η : ℝ,
      0 < η ∧ Set.Icc (0 : ℝ) η ⊆
        (fun y ↦ (standardJacobianColumnMinor F cols y) ^ 2) ''
          wilkieFiberOver F a U := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : ConnectedSpace (RealEuclidean n) := inferInstance
  haveI : NoncompactSpace (RealEuclidean n) := inferInstance
  have hFdiff : DifferentiableAt ℝ F x :=
    (hF.differentiable (by simp)).differentiableAt
  obtain ⟨cols, hminorAtX⟩ :=
    (fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
      hFdiff).mp (hregular x hx.1)
  refine ⟨cols, ?_⟩
  exact wilkieFiniteVisibleImage_sameMinor_squared_interval_of_squareChart
    hF a hUopen hregular hbounded hfinite hx cols hminorAtX
    (wilkieColumnComplementaryProjection cols)
    (wilkieColumnComplementaryProjection_fullComponent_squareChart
      hF a cols)

end AbelFormalization
