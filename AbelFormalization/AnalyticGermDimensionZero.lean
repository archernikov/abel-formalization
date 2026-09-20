import AbelFormalization.AnalyticGermLocal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.SimpleModule.Basic

/-! # The zero-dimensional analytic-germ ring

On a subsingleton parameter space, analytic germs are determined by their
value at the base point. Evaluation is therefore a ring equivalence with
the reals. In particular, the actual ring of real-analytic germs in zero
variables is Noetherian and has Krull dimension zero. No corresponding
property in a positive number of variables is assumed here.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]

/-- In a subsingleton parameter space, equality of values forces equality of
analytic representatives everywhere, hence equality of their germs. -/
theorem analyticGermValue_injective_of_subsingleton (x : E) :
    Function.Injective (analyticGermValue x) := by
  intro a b hab
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative a
  obtain ⟨g, hg, rfl⟩ := exists_analyticGerm_representative b
  change f x = g x at hab
  apply (analyticGermOf_eq_iff hf hg).mpr
  exact Eventually.of_forall fun y => by simpa only [Subsingleton.elim y x] using hab

/-- Evaluation identifies the analytic-germ ring over a subsingleton space
with the scalar field. -/
def analyticGermEquivRealOfSubsingleton (x : E) : AnalyticGermAt x ≃+* ℝ :=
  RingEquiv.ofBijective (analyticGermValue x)
    ⟨analyticGermValue_injective_of_subsingleton x, analyticGermValue_surjective x⟩

@[simp]
theorem analyticGermEquivRealOfSubsingleton_apply (x : E) (g : AnalyticGermAt x) :
    analyticGermEquivRealOfSubsingleton x g = analyticGermValue x g := rfl

instance analyticGermIsNoetherianRingOfSubsingleton (x : E) :
    IsNoetherianRing (AnalyticGermAt x) :=
  isNoetherianRing_of_ringEquiv ℝ (analyticGermEquivRealOfSubsingleton x).symm

theorem analyticGerm_ringKrullDim_eq_zero_of_subsingleton (x : E) :
    ringKrullDim (AnalyticGermAt x) = 0 := by
  rw [(analyticGermEquivRealOfSubsingleton x).ringKrullDim,
    ringKrullDim_eq_zero_of_field ℝ]

/-- The dimension-zero base case in the manuscript's notation. -/
def realAnalyticGermZeroEquivReal : RealAnalyticGerm 0 ≃+* ℝ :=
  analyticGermEquivRealOfSubsingleton (0 : Fin 0 → ℝ)

theorem realAnalyticGerm_zero_isNoetherian : IsNoetherianRing (RealAnalyticGerm 0) :=
  inferInstance

theorem realAnalyticGerm_zero_ringKrullDim : ringKrullDim (RealAnalyticGerm 0) = 0 :=
  analyticGerm_ringKrullDim_eq_zero_of_subsingleton (0 : Fin 0 → ℝ)

end AbelFormalization
