import AbelFormalization.SmoothGeometricFamily

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

theorem smoothRegularFiber_eq_regularZeroSet_univ_sub
    {n : ℕ} (g : RealEuclidean n → RealEuclidean n)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean n) :
    smoothRegularFiber g t =
      regularZeroSet Set.univ (fun x ↦ g x - t) := by
  ext x
  rw [mem_smoothRegularFiber_iff_of_contDiff_square g hg t x]
  simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_univ, true_and,
    sub_eq_zero, fderiv_sub_const]

theorem IsZeroRegularFunctionFamily.of_regularZeroSet_finite
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hfinite : ∀ n (g : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily G g → ∀ t,
        (regularZeroSet Set.univ (fun x ↦ g x - t)).Finite) :
    IsZeroRegularFunctionFamily G := by
  intro n g hg t
  rw [smoothRegularFiber_eq_regularZeroSet_univ_sub g
    (by
      rw [contDiff_pi]
      intro i
      exact (hsmooth n (fun x ↦ g x i) (hg i)).of_le (by simp)) t]
  exact hfinite n g hg t

end AbelFormalization
