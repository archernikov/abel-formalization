import AbelFormalization.SquaredDistanceCriticalFamilyContDiff

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def squaredDistanceCriticalEquation {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (center : Fin (r + 1) → ℝ) : E → ℝ := fun x =>
  criticalDeterminant H
    (algebraicSquaredDistance (fun i x => basis.equivFun x i) center)
    basis x

theorem squaredDistanceCriticalFamily_fixed_center {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (center : Fin (r + 1) → ℝ) :
    (fun x => squaredDistanceCriticalFamily H basis (x, center)) =
      criticalSystemMap H (squaredDistanceCriticalEquation H basis center) := by
  rfl

theorem fderiv_squaredDistanceCriticalFamily_fixed_center {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (x : E) (center : Fin (r + 1) → ℝ)
    (hfamily : DifferentiableAt ℝ
      (squaredDistanceCriticalFamily H basis) (x, center)) :
    fderiv ℝ (criticalSystemMap H
      (squaredDistanceCriticalEquation H basis center)) x =
      fstPartial (fderiv ℝ (squaredDistanceCriticalFamily H basis) (x, center)) := by
  let I : E →L[ℝ] E × (Fin (r + 1) → ℝ) :=
    ContinuousLinearMap.inl ℝ E (Fin (r + 1) → ℝ)
  have hins : HasFDerivAt
      (fun y : E => (y, center)) I x := by
    exact hasFDerivAt_prodMk_left x center
  have hcomp := hfamily.hasFDerivAt.comp x hins
  have hcomp' : HasFDerivAt
      (fun y => squaredDistanceCriticalFamily H basis (y, center))
      ((fderiv ℝ (squaredDistanceCriticalFamily H basis) (x, center)).comp I) x := by
    simpa [Function.comp_def] using hcomp
  rw [squaredDistanceCriticalFamily_fixed_center] at hcomp'
  simpa [fstPartial, I] using hcomp'.fderiv

theorem exists_squaredDistanceCenter_regular_criticalSystem {r : ℕ}
    (M : Set E) (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (hzero : ∀ x ∈ M, ∀ i, H i x = 0)
    (hH : ∀ x ∈ M, ∀ i, ContDiffAt ℝ 2 (H i) x)
    (hconstraint : ∀ x ∈ M, (constraintFDeriv H x).range = ⊤) :
    ∃ center : Fin (r + 1) → ℝ, ∀ x ∈ M,
      squaredDistanceCriticalEquation H basis center x = 0 →
      (fderiv ℝ (criticalSystemMap H
        (squaredDistanceCriticalEquation H basis center)) x).range = ⊤ := by
  let Phi := squaredDistanceCriticalFamily H basis
  let S : Set (E × (Fin (r + 1) → ℝ)) :=
    {p | p.1 ∈ M ∧ Phi p = 0}
  have hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p := by
    intro p hp
    exact contDiffAt_squaredDistanceCriticalFamily H basis p.1 p.2 (hH p.1 hp.1)
  have hSurj : ∀ p ∈ S, (fderiv ℝ Phi p).range = ⊤ := by
    intro p hp
    apply squaredDistanceCriticalFamily_fderiv_range_eq_top
      H (fun _ => 0) basis p.1 p.2
    · exact (hPhi p hp).differentiableAt one_ne_zero
    · intro i
      exact (hH p.1 hp.1 i).differentiableAt (by norm_num)
    · exact hconstraint p.1 hp.1
  have hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis basis]
    simp
  obtain ⟨center, hcenter⟩ := exists_parameter_with_regular_fixed_slice
    Phi S 0 hPhi hdim (fun p hp => hp.2) hSurj
  refine ⟨center, ?_⟩
  intro x hxM hxCritical
  have hzeroFamily : Phi (x, center) = 0 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Phi, squaredDistanceCriticalEquation] using hxCritical
    · simpa [Phi] using hzero x hxM j
  have hxS : (x, center) ∈ S := ⟨hxM, hzeroFamily⟩
  have hfixed := hcenter (x, center) hxS rfl
  have hfamilyAt : DifferentiableAt ℝ
      (squaredDistanceCriticalFamily H basis) (x, center) := by
    change DifferentiableAt ℝ Phi (x, center)
    exact (hPhi (x, center) hxS).differentiableAt one_ne_zero
  rw [fderiv_squaredDistanceCriticalFamily_fixed_center
    H basis x center hfamilyAt]
  exact hfixed

end AbelFormalization
