import AbelFormalization.WilkieCase2FlatJacobianInsertion
import AbelFormalization.WilkieCase2SliceRegularity

/-!
# Lift a sliced minor interval to the original ball fiber

The Jacobian and image-inclusion premises of the general Case 2 minor
transport theorem are discharged here for literal coordinate insertion and
the literal ball-slice fiber.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- A squared-minor interval on the fiber obtained by fixing one coordinate
is an interval of the corresponding minor on the original fiber inside the
ambient ball.  The fixed coordinate is omitted from the selected columns;
the output rows retain their order, while the selected slice columns may be
reordered. -/
theorem wilkieCase2_ballSliceMinor_squared_interval_lift
    {a k : ℕ}
    (F : RealEuclidean (a + 1) → RealEuclidean k)
    (fixed : Fin (a + 1)) (b : ℝ)
    (target : RealEuclidean k)
    (center : RealEuclidean (a + 1)) (radius : ℝ)
    (cols : Fin k ↪ Fin a) (order : Equiv.Perm (Fin k))
    (hFdiff : ∀ z : RealEuclidean (a + 1),
      DifferentiableAt ℝ F z)
    {η : ℝ} (hη : 0 < η)
    (hinterval : Set.Icc (0 : ℝ) η ⊆
      (fun y ↦ (standardJacobianColumnMinor
        (fun x ↦ F (wilkieCase2_coordinateInsert fixed b x))
        (order.toEmbedding.trans cols) y) ^ 2) ''
        wilkieCase2BallSliceFiber F target
          (wilkieCase2_coordinateInsert fixed b) center radius) :
    0 < η ∧ Set.Icc (0 : ℝ) η ⊆
      (fun z ↦ (standardJacobianColumnMinor F
        (cols.trans (Fin.succAboveEmb fixed)) z) ^ 2) ''
        {z | F z = target ∧ z ∈ Metric.ball center radius} := by
  let S : Set (RealEuclidean a) :=
    wilkieCase2BallSliceFiber F target
      (wilkieCase2_coordinateInsert fixed b) center radius
  let X : Set (RealEuclidean (a + 1)) :=
    {z | F z = target ∧ z ∈ Metric.ball center radius}
  have hJac : ∀ y ∈ S,
      standardRectangularJacobian
        (fun x ↦ F (wilkieCase2_coordinateInsert fixed b x)) y =
          (standardRectangularJacobian F
            (wilkieCase2_coordinateInsert fixed b y)).submatrix
            (Equiv.refl (Fin k)) (Fin.succAboveEmb fixed) := by
    intro y _
    exact wilkieCase2_flatJacobian_coordinateInsert F fixed b y
      (hFdiff _)
  have himage :
      (wilkieCase2_coordinateInsert fixed b) '' S ⊆ X := by
    rintro z ⟨y, hy, rfl⟩
    change F (wilkieCase2_coordinateInsert fixed b y) = target ∧
      wilkieCase2_coordinateInsert fixed b y ∈ Metric.ball center radius at hy
    exact hy
  exact wilkieCase2_sliceMinor_squared_interval_transport
    F
    (fun x ↦ F (wilkieCase2_coordinateInsert fixed b x))
    (wilkieCase2_coordinateInsert fixed b)
    (Fin.succAboveEmb fixed) cols
    (Equiv.refl (Fin k)) order
    hJac himage hη hinterval

end AbelFormalization
