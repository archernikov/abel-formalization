import AbelFormalization.Analytic
import AbelFormalization.DerivativeBounds
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Continuity and differentiability of the inverse

The positive-domain bijection is an order isomorphism. Its inverse is therefore
continuous, and the inverse differentiation theorem gives its derivative.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

/-- The inverse Abel function as an order isomorphism onto the positive reals. -/
noncomputable def inverseOrderIso : ℝ ≃o Set.Ioi (0 : ℝ) where
  toFun s := ⟨inverse A s, hA.inverse_pos s⟩
  invFun x := A x
  left_inv s := hA.apply_inverse s
  right_inv x := Subtype.ext (hA.inverse_apply x.property)
  map_rel_iff' := hA.inverse_strictMono.le_iff_le

include hA

theorem inverse_continuous : Continuous (inverse A) :=
  continuous_subtype_val.comp hA.inverseOrderIso.continuous

theorem inverse_hasDerivAt (s : ℝ) :
    HasDerivAt (inverse A) (deriv A (inverse A s))⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse hA.inverse_continuous.continuousAt
    (hA.differentiableAt (hA.inverse_pos s)).hasDerivAt
    (ne_of_gt (hA.deriv_pos _ (hA.inverse_pos s)))
  exact Filter.Eventually.of_forall hA.apply_inverse

theorem inverse_deriv (s : ℝ) :
    deriv (inverse A) s = (deriv A (inverse A s))⁻¹ :=
  (hA.inverse_hasDerivAt s).deriv

theorem inverse_deriv_pos (s : ℝ) : 0 < deriv (inverse A) s := by
  rw [hA.inverse_deriv]
  exact inv_pos.mpr (hA.deriv_pos _ (hA.inverse_pos s))

theorem inverse_tendsto_atTop : Tendsto (inverse A) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (A (max b 1))] with s hs
  have hp : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  have h := hA.inverse_strictMono.monotone hs
  rw [hA.inverse_apply hp] at h
  exact (le_max_left b 1).trans h

/-- The first strict inverse-derivative inequality in the paper. -/
theorem eventually_inverse_lt_deriv :
    ∀ᶠ s : ℝ in atTop, inverse A s < deriv (inverse A) s := by
  have hlim := hA.tendsto_mul_deriv_atTop.comp hA.inverse_tendsto_atTop
  have he : ∀ᶠ s : ℝ in atTop, inverse A s * deriv A (inverse A s) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he] with s hs
  rw [hA.inverse_deriv]
  simpa only [one_div] using (lt_div_iff₀ (hA.deriv_pos _ (hA.inverse_pos s))).mpr hs

end IsAbel

end AbelFormalization
