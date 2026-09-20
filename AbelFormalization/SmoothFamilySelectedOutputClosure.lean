import AbelFormalization.SmoothFamilyMaximalRankLocalFiber

/-!
# Family closure for selected-output local fibers

Selecting output coordinates of a tuple preserves componentwise membership in
the same function family.  In a geometric family, translating those selected
coordinates by a fixed target also preserves membership.

Combined with the maximal-rank local fiber theorem, this gives the exact local
reduction needed by a rank induction: near a point of globally maximal
derivative rank, the original fiber agrees with a fiber cut out by a tuple
still belonging to the family.  This is only a local reduction.  It supplies
neither global component finiteness of a rank piece nor a bound uniform in the
fiber target.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- Selecting output coordinates preserves componentwise family membership. -/
theorem FunctionTupleInFamily.selectedOutputMap
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : FunctionTupleInFamily G g) (rows : Fin k ↪ Fin b) :
    FunctionTupleInFamily G (selectedOutputMap g rows) := by
  intro i
  change (fun x => g x (rows i)) ∈ G a
  exact hg (rows i)

/-- The equations defining a selected-output fiber remain in a geometric
function family. -/
theorem IsGeometricFunctionFamily.selectedOutput_sub_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : FunctionTupleInFamily G g) (rows : Fin k ↪ Fin b)
    (t : RealEuclidean k) :
    FunctionTupleInFamily G
      (fun x ↦ selectedOutputMap g rows x - t) := by
  intro i
  change (fun x ↦ g x (rows i) - t i) ∈ G a
  exact hG.sub_mem (hg (rows i)) (hG.const_mem (t i))

/-- At a point attaining the global maximal derivative rank, the local
selected-output fiber can be chosen inside the original function family. -/
theorem MaximalDerivativeRankCertificate.exists_local_family_selectedOutput_fiber_eq
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a}
    (h : MaximalDerivativeRankCertificate g x k)
    (hg : FunctionTupleInFamily G g) (hsmooth : ContDiff ℝ 1 g) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
      standardJacobianMinor g rows cols x ≠ 0 ∧
        FunctionTupleInFamily G (selectedOutputMap g rows) ∧
          ∃ U : Set (RealEuclidean a),
            IsOpen U ∧ x ∈ U ∧
              U ∩ g ⁻¹' {g x} =
                U ∩ selectedOutputMap g rows ⁻¹'
                  {selectedOutputMap g rows x} := by
  obtain ⟨rows, cols, hminor, U, hUopen, hxU, hfiber⟩ :=
    h.exists_local_fiber_eq_selectedOutput_fiber hsmooth
  exact ⟨rows, cols, hminor, hg.selectedOutputMap rows,
    U, hUopen, hxU, hfiber⟩

end AbelFormalization
