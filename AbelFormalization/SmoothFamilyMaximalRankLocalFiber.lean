import AbelFormalization.SmoothFamilyConstantRankLocalFiber

/-!
# Local fibers at a point of globally maximal derivative rank

Suppose the derivative of a smooth map has rank at most `k` everywhere and
has rank exactly `k` at one point.  Exact rank supplies a nonzero `k × k`
Jacobian minor.  The global upper bound supplies the local rank hypothesis of
`exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le`.  Hence, on one
neighborhood of the point, equality of the full map is equivalent to equality
of the output coordinates selected by that minor.

The argument includes `k = 0`, when the selected output space is a singleton
and the map is locally constant.  All conclusions here are local; no global or
uniform bound on connected components is asserted.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- A certificate that `k` is the global maximum derivative rank of `g`,
attained at `x`. -/
structure MaximalDerivativeRankCertificate {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (x : RealEuclidean a) (k : ℕ) : Prop where
  rank_le : ∀ y,
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k
  rank_eq_at : Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g x).toLinearMap) = k

/-- At a point where the globally maximal derivative rank is `k`, some
`k × k` standard Jacobian minor is nonzero.  This also applies when `k = 0`;
the unique empty minor has determinant one. -/
theorem MaximalDerivativeRankCertificate.exists_standardJacobianMinor_ne_zero
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (h : MaximalDerivativeRankCertificate g x k)
    (hg : DifferentiableAt ℝ g x) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
      standardJacobianMinor g rows cols x ≠ 0 :=
  ((finrank_range_fderiv_eq_iff_standardJacobianMinors hg).mp
    h.rank_eq_at).1

/-- Near a point where the globally maximal derivative rank is attained,
some selected output coordinates have exactly the same equality relation as
the full map. -/
theorem MaximalDerivativeRankCertificate.exists_local_selectedOutput_eq_iff
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (h : MaximalDerivativeRankCertificate g x k)
    (hg : ContDiff ℝ 1 g) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
      standardJacobianMinor g rows cols x ≠ 0 ∧
        ∃ U : Set (RealEuclidean a),
          IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, ∀ z ∈ U,
              (g y = g z ↔
                selectedOutputMap g rows y = selectedOutputMap g rows z) := by
  obtain ⟨rows, cols, hminor⟩ :=
    h.exists_standardJacobianMinor_ne_zero
      (hg.differentiable one_ne_zero x)
  have hrank : ∀ᶠ y in 𝓝 x,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k :=
    Filter.Eventually.of_forall h.rank_le
  obtain ⟨U, hUopen, hxU, hselected⟩ :=
    exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le
      hg x rows cols hminor hrank
  refine ⟨rows, cols, hminor, U, hUopen, hxU, ?_⟩
  intro y hy z hz
  constructor
  · intro hyz
    change (fun i : Fin k => g y (rows i)) =
      fun i : Fin k => g z (rows i)
    exact congrArg
      (fun v : RealEuclidean b => fun i : Fin k => v (rows i)) hyz
  · exact hselected y hy z hz

/-- Set-level form of the local maximal-rank conclusion: inside one
neighborhood, the fiber of the full map through `x` equals the corresponding
fiber of a selected output map. -/
theorem MaximalDerivativeRankCertificate.exists_local_fiber_eq_selectedOutput_fiber
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (h : MaximalDerivativeRankCertificate g x k)
    (hg : ContDiff ℝ 1 g) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
      standardJacobianMinor g rows cols x ≠ 0 ∧
        ∃ U : Set (RealEuclidean a),
          IsOpen U ∧ x ∈ U ∧
            U ∩ g ⁻¹' {g x} =
              U ∩ selectedOutputMap g rows ⁻¹'
                {selectedOutputMap g rows x} := by
  obtain ⟨rows, cols, hminor, U, hUopen, hxU, hiff⟩ :=
    h.exists_local_selectedOutput_eq_iff hg
  refine ⟨rows, cols, hminor, U, hUopen, hxU, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyU, hyx⟩
    exact ⟨hyU, (hiff y hyU x hxU).mp hyx⟩
  · rintro ⟨hyU, hyx⟩
    exact ⟨hyU, (hiff y hyU x hxU).mpr hyx⟩

/-- The zero maximal-rank case is local constancy.  This is the `k = 0`
specialization of the same constant-rank argument, with no positive-rank
side condition. -/
theorem MaximalDerivativeRankCertificate.exists_open_nhds_const_of_rank_zero
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (h : MaximalDerivativeRankCertificate g x 0)
    (hg : ContDiff ℝ 1 g) :
    ∃ U : Set (RealEuclidean a),
      IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, g y = g z := by
  apply exists_open_nhds_eq_of_fderiv_rank_zero hg x
  exact Filter.Eventually.of_forall h.rank_le

end AbelFormalization
