import AbelFormalization.AnalyticGerm
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The local ring of real-analytic germs

A germ is invertible exactly when its value at the base point is nonzero.
Thus the actual analytic-germ ring is local, its maximal ideal consists of
the germs vanishing at the base point, and its residue field is the reals.
These statements require no Noetherian or dimension hypothesis.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An analytic germ is a unit exactly when its base-point value is nonzero.
The inverse is represented by the analytic reciprocal of any representative. -/
theorem isUnit_analyticGerm_iff {x : E} (g : AnalyticGermAt x) :
    IsUnit g ↔ analyticGermValue x g ≠ 0 := by
  constructor
  · intro hg
    exact isUnit_iff_ne_zero.mp (hg.map (analyticGermValue x))
  · intro hg
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    have hfx : f x ≠ 0 := hg
    have hfi : AnalyticAt ℝ (fun y => (f y)⁻¹) x := hf.inv hfx
    apply isUnit_iff_exists_inv.mpr
    refine ⟨analyticGermOf (fun y => (f y)⁻¹) hfi, ?_⟩
    rw [← analyticGermOf_mul hf hfi]
    change analyticGermOf (f * fun y => (f y)⁻¹) (hf.mul hfi) =
      analyticGermOf (fun _ => 1) analyticAt_const
    apply (analyticGermOf_eq_iff _ _).mpr
    filter_upwards [hf.continuousAt.eventually_ne hfx] with y hy
    exact mul_inv_cancel₀ hy

/-- Locality is a theorem of the analytic representatives, not an assumption
about an abstract coefficient ring. -/
instance analyticGermIsLocalRing (x : E) : IsLocalRing (AnalyticGermAt x) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro g
  by_cases hg : analyticGermValue x g = 0
  · right
    rw [isUnit_analyticGerm_iff]
    simp [hg]
  · exact Or.inl ((isUnit_analyticGerm_iff g).mpr hg)

/-- The base-point evaluation kernel is a maximal ideal. -/
theorem analyticGermValue_ker_isMaximal (x : E) :
    (RingHom.ker (analyticGermValue x)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (analyticGermValue x) (analyticGermValue_surjective x)

/-- The unique maximal ideal consists exactly of the germs vanishing at the
base point. -/
theorem analyticGerm_maximalIdeal_eq_ker (x : E) :
    IsLocalRing.maximalIdeal (AnalyticGermAt x) = RingHom.ker (analyticGermValue x) := by
  ext g
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_analyticGerm_iff, not_ne_iff, RingHom.mem_ker]

@[simp]
theorem analyticGerm_mem_maximalIdeal_iff {x : E} (g : AnalyticGermAt x) :
    g ∈ IsLocalRing.maximalIdeal (AnalyticGermAt x) ↔ analyticGermValue x g = 0 := by
  rw [analyticGerm_maximalIdeal_eq_ker]
  rfl

/-- Constant germs give the canonical real coefficient map. -/
def analyticGermConst (x : E) : ℝ →+* AnalyticGermAt x where
  toFun c := analyticGermOf (fun _ => c) analyticAt_const
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance analyticGermAlgebra (x : E) : Algebra ℝ (AnalyticGermAt x) :=
  (analyticGermConst x).toAlgebra

@[simp]
theorem analyticGerm_algebraMap (x : E) (c : ℝ) :
    algebraMap ℝ (AnalyticGermAt x) c = analyticGermOf (fun _ => c) analyticAt_const := rfl

@[simp]
theorem analyticGermValue_algebraMap (x : E) (c : ℝ) :
    analyticGermValue x (algebraMap ℝ (AnalyticGermAt x) c) = c := rfl

/-- Evaluation identifies the actual residue field with the real numbers. -/
def analyticGermResidueEquiv (x : E) :
    IsLocalRing.ResidueField (AnalyticGermAt x) ≃+* ℝ :=
  (Ideal.quotEquivOfEq (analyticGerm_maximalIdeal_eq_ker x)).trans
    ((analyticGermValue x).quotientKerEquivOfSurjective (analyticGermValue_surjective x))

@[simp]
theorem analyticGermResidueEquiv_residue (x : E) (g : AnalyticGermAt x) :
    analyticGermResidueEquiv x (IsLocalRing.residue (AnalyticGermAt x) g) =
      analyticGermValue x g := by
  change ((analyticGermValue x).quotientKerEquivOfSurjective (analyticGermValue_surjective x))
    ((Ideal.quotEquivOfEq (analyticGerm_maximalIdeal_eq_ker x))
      (Ideal.Quotient.mk _ g)) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk (analyticGermValue_surjective x) g

end AbelFormalization
