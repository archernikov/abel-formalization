import AbelFormalization.LionCarpetCompactification
import AbelFormalization.GeneralCodimensionLagrange
import AbelFormalization.SquaredDistanceProper

/-!
# The standard carpet on Euclidean space

Lion starts the proof on each smooth affine piece with a positive proper
carpet.  For the globally smooth Abel family the whole Euclidean space is one
piece, and the rational function `1 / (1 + ‖x‖²)` is a carpet belonging to
the geometric function family.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Squared distance in standard coordinates is nonnegative. -/
theorem standardSquaredDistance_nonneg {n : ℕ}
    (center x : RealEuclidean n) :
    0 ≤ standardSquaredDistance center x := by
  unfold standardSquaredDistance
  rw [algebraicSquaredDistance_apply]
  exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)

/-- Lion's standard carpet on all of `ℝⁿ`. -/
def lionStandardCarpet (n : ℕ) : RealEuclideanFunction n :=
  fun x ↦ (1 + standardSquaredDistance (0 : RealEuclidean n) x)⁻¹

theorem lionStandardCarpet_pos {n : ℕ} (x : RealEuclidean n) :
    0 < lionStandardCarpet n x := by
  apply inv_pos.mpr
  have := standardSquaredDistance_nonneg
    (0 : RealEuclidean n) x
  linarith

/-- A positive superlevel of the standard carpet is exactly a squared-distance
sublevel. -/
theorem lionStandardCarpet_superlevel_eq {n : ℕ} (eta : ℝ)
    (heta : 0 < eta) :
    {x : RealEuclidean n | eta ≤ lionStandardCarpet n x} =
      {x | standardSquaredDistance (0 : RealEuclidean n) x ≤ eta⁻¹ - 1} := by
  ext x
  let rho := standardSquaredDistance (0 : RealEuclidean n) x
  have hrho : 0 ≤ rho := standardSquaredDistance_nonneg
    (0 : RealEuclidean n) x
  have hden : 0 < 1 + rho := by linarith
  change eta ≤ (1 + rho)⁻¹ ↔ rho ≤ eta⁻¹ - 1
  constructor
  · intro h
    rw [inv_eq_one_div] at h ⊢
    have hmul : eta * (1 + rho) ≤ 1 := by
      exact (le_div_iff₀ hden).mp h
    have hdiv : 1 + rho ≤ 1 / eta := by
      apply (le_div_iff₀ heta).mpr
      nlinarith
    linarith
  · intro h
    rw [inv_eq_one_div] at h ⊢
    have hdiv : 1 + rho ≤ 1 / eta := by
      linarith
    have hmul : eta * (1 + rho) ≤ 1 := by
      have := (le_div_iff₀ heta).mp hdiv
      nlinarith
    exact (le_div_iff₀ hden).mpr hmul

/-- The standard rational carpet satisfies Lion's compactness interface on
the whole Euclidean space. -/
theorem isLionCarpetOn_univ_lionStandardCarpet (n : ℕ) :
    IsLionCarpetOn (Set.univ : Set (RealEuclidean n))
      (lionStandardCarpet n) := by
  constructor
  · intro x _hx
    exact lionStandardCarpet_pos x
  · intro eta heta
    have hcompact : IsCompact
        {x : RealEuclidean n |
          standardSquaredDistance (0 : RealEuclidean n) x ≤ eta⁻¹ - 1} := by
      simpa only [standardSquaredDistance] using
        (isCompact_algebraicSquaredDistance_basis_sublevel
          (Pi.basisFun ℝ (Fin n)) (0 : Fin n → ℝ) (eta⁻¹ - 1))
    simpa only [Set.mem_univ, true_and,
      lionStandardCarpet_superlevel_eq eta heta] using hcompact

/-- The standard carpet belongs to every geometric function family. -/
theorem IsGeometricFunctionFamily.lionStandardCarpet_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    lionStandardCarpet n ∈ G n := by
  apply hG.inv
  · exact hG.add hG.one_mem
      (by simpa only [standardSquaredDistance] using
        hG.standardSquaredDistance_mem (0 : RealEuclidean n))
  · intro x hzero
    have hpos : 0 < 1 + standardSquaredDistance
        (0 : RealEuclidean n) x := by
      have := standardSquaredDistance_nonneg
        (0 : RealEuclidean n) x
      linarith
    exact (ne_of_gt hpos) hzero

/-- The canonical thresholds used in the compact exhaustion. -/
def lionStandardThreshold (j : ℕ) : ℝ :=
  1 / (j + 1 : ℝ)

theorem lionStandardThreshold_pos (j : ℕ) :
    0 < lionStandardThreshold j := by
  exact one_div_pos.mpr (by positivity)

theorem lionStandardThreshold_antitone :
    Antitone lionStandardThreshold := by
  intro j k hjk
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hjk 1

theorem lionStandardThreshold_tendToZero :
    LionThresholdsTendToZero lionStandardThreshold := by
  intro epsilon hepsilon
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hepsilon
  exact ⟨j, le_of_lt (by simpa only [lionStandardThreshold] using hj)⟩

end AbelFormalization
