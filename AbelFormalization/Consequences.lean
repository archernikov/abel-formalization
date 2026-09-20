import AbelFormalization.Statement
import AbelFormalization.Growth

/-!
# Unconditional consequences of the Abel hypotheses

These results do not use or assume o-minimality.
-/

namespace AbelFormalization

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem isPositiveInverse : IsPositiveInverse A (inverse A) :=
  ⟨fun s => ⟨hA.inverse_pos s, hA.apply_inverse s⟩,
    fun _ hx => hA.inverse_apply hx⟩

/-- The full growth clause of the proposed main theorem. -/
theorem isTransexponential : IsTransexponential (inverse A) := by
  apply transexponential_of_recurrence hA.inverse_strictMono.monotone hA.inverse_add_one
  refine ⟨A 2, ?_⟩
  rw [hA.inverse_apply (by norm_num : (0 : ℝ) < 2)]

end IsAbel

end AbelFormalization
