import AbelFormalization.AnalyticGermDerivation
import Mathlib.Algebra.Algebra.Equiv

/-! # Analytic pullbacks on the actual germ algebra

An analytic map taking one base point to another induces a real-algebra
homomorphism in the opposite direction on analytic germs. The construction
uses neighborhood germs, so its value depends only on the local map.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pullback by an analytic map preserving the specified base points. -/
def analyticGermPullback {x : E} {y : F} (φ : E → F)
    (hφ : AnalyticAt ℝ φ x) (hxy : φ x = y) :
    AnalyticGermAt y →ₐ[ℝ] AnalyticGermAt x where
  toFun g := ⟨g.val.compTendsto φ (hxy ▸ hφ.continuousAt), by
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    exact ⟨f ∘ φ, hf.comp_of_eq hφ hxy, rfl⟩⟩
  map_zero' := by apply Subtype.ext; rfl
  map_one' := by apply Subtype.ext; rfl
  map_add' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    obtain ⟨k, hk, rfl⟩ := exists_analyticGerm_representative h
    apply Subtype.ext
    rfl
  map_mul' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    obtain ⟨k, hk, rfl⟩ := exists_analyticGerm_representative h
    apply Subtype.ext
    rfl
  commutes' c := by apply Subtype.ext; rfl

/-- The pullback is represented by ordinary composition. -/
@[simp]
theorem analyticGermPullback_of {x : E} {y : F} (φ : E → F)
    (hφ : AnalyticAt ℝ φ x) (hxy : φ x = y) (f : F → ℝ)
    (hf : AnalyticAt ℝ f y) :
    analyticGermPullback φ hφ hxy (analyticGermOf f hf) =
      analyticGermOf (f ∘ φ) (hf.comp_of_eq hφ hxy) := rfl

@[simp]
theorem analyticGermValue_pullback {x : E} {y : F} (φ : E → F)
    (hφ : AnalyticAt ℝ φ x) (hxy : φ x = y) (g : AnalyticGermAt y) :
    analyticGermValue x (analyticGermPullback φ hφ hxy g) = analyticGermValue y g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  simp [hxy]

@[simp]
theorem analyticGermPullback_id (x : E) :
    analyticGermPullback id analyticAt_id (show id x = x from rfl) =
      AlgHom.id ℝ (AnalyticGermAt x) := by
  apply AlgHom.ext
  intro g
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  apply Subtype.ext
  rfl

/-- The contravariant composition rule for analytic pullbacks. -/
theorem analyticGermPullback_comp {x : E} {y : F} {z : G}
    (φ : E → F) (ψ : F → G) (hφ : AnalyticAt ℝ φ x)
    (hψ : AnalyticAt ℝ ψ y) (hxy : φ x = y) (hyz : ψ y = z) :
    (analyticGermPullback φ hφ hxy).comp (analyticGermPullback ψ hψ hyz) =
      analyticGermPullback (ψ ∘ φ) (hψ.comp_of_eq hφ hxy)
        (show (ψ ∘ φ) x = z by simp [hxy, hyz]) := by
  apply AlgHom.ext
  intro g
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  apply Subtype.ext
  rfl

/-- Only the germ of the analytic coordinate map matters. -/
theorem analyticGermPullback_congr {x : E} {y : F} {φ ψ : E → F}
    (hφ : AnalyticAt ℝ φ x) (hψ : AnalyticAt ℝ ψ x)
    (hφx : φ x = y) (hψx : ψ x = y) (he : φ =ᶠ[𝓝 x] ψ) :
    analyticGermPullback φ hφ hφx = analyticGermPullback ψ hψ hψx := by
  apply AlgHom.ext
  intro g
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  rw [analyticGermPullback_of, analyticGermPullback_of, analyticGermOf_eq_iff]
  exact he.fun_comp f

/-- Locally inverse analytic coordinate maps give inverse algebra maps on germs.
The inverse identities need only hold on neighborhoods of the base points. -/
def analyticGermEquivOfLocalInverse {x : E} {y : F} (φ : E → F) (ψ : F → E)
    (hφ : AnalyticAt ℝ φ x) (hψ : AnalyticAt ℝ ψ y)
    (hxy : φ x = y) (hyx : ψ y = x)
    (hleft : ψ ∘ φ =ᶠ[𝓝 x] id) (hright : φ ∘ ψ =ᶠ[𝓝 y] id) :
    AnalyticGermAt y ≃ₐ[ℝ] AnalyticGermAt x where
  toFun := analyticGermPullback φ hφ hxy
  invFun := analyticGermPullback ψ hψ hyx
  left_inv g := by
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    rw [analyticGermPullback_of, analyticGermPullback_of, analyticGermOf_eq_iff]
    exact hright.fun_comp f
  right_inv g := by
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    rw [analyticGermPullback_of, analyticGermPullback_of, analyticGermOf_eq_iff]
    exact hleft.fun_comp f
  map_mul' := (analyticGermPullback φ hφ hxy).map_mul
  map_add' := (analyticGermPullback φ hφ hxy).map_add
  commutes' := (analyticGermPullback φ hφ hxy).commutes

/-- Continuous linear coordinate equivalences act on analytic germs. -/
def analyticGermEquivOfContinuousLinearEquiv (e : E ≃L[ℝ] F) (x : E) :
    AnalyticGermAt (e x) ≃ₐ[ℝ] AnalyticGermAt x :=
  analyticGermEquivOfLocalInverse e e.symm
    (e.toContinuousLinearMap.analyticAt x)
    (e.symm.toContinuousLinearMap.analyticAt (e x)) rfl (e.symm_apply_apply x)
    (Filter.Eventually.of_forall e.symm_apply_apply)
    (Filter.Eventually.of_forall e.apply_symm_apply)

/-- Scalar and single-coordinate conventions give the same analytic-germ algebra. -/
def analyticGermOneEquiv : AnalyticGermAt (0 : ℝ) ≃ₐ[ℝ] RealAnalyticGerm 1 :=
  analyticGermEquivOfContinuousLinearEquiv
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)) (0 : Fin 1 → ℝ)

@[simp]
theorem analyticGermOneEquiv_value (g : AnalyticGermAt (0 : ℝ)) :
    analyticGermValue (0 : Fin 1 → ℝ) (analyticGermOneEquiv g) =
      analyticGermValue (0 : ℝ) g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  rfl

/-- The ordinary scalar coordinate becomes the unique finite-tuple coordinate. -/
@[simp]
theorem analyticGermOneEquiv_coordinate :
    analyticGermOneEquiv (analyticGermOf id (analyticAt_id (𝕜 := ℝ) (z := (0 : ℝ)))) =
      analyticGermCoordinate 1 0 := by
  apply Subtype.ext
  rfl

/-- Drop the first coordinate of a finite real tuple. -/
def analyticGermDropCoordinate (p : ℕ) : (Fin (p + 1) → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)

/-- Insert zero as the first coordinate of a finite real tuple. -/
def analyticGermInsertCoordinate (p : ℕ) : (Fin p → ℝ) →L[ℝ] (Fin (p + 1) → ℝ) :=
  ContinuousLinearMap.finCons 0 (ContinuousLinearMap.id ℝ (Fin p → ℝ))

@[simp]
theorem analyticGermDropCoordinate_apply (p : ℕ) (x : Fin (p + 1) → ℝ) (i : Fin p) :
    analyticGermDropCoordinate p x i = x i.succ := rfl

@[simp]
theorem analyticGermInsertCoordinate_apply (p : ℕ) (x : Fin p → ℝ) :
    analyticGermInsertCoordinate p x = Fin.cons 0 x := rfl

/-- Regard a germ in `p` variables as independent of a new first coordinate. -/
def analyticGermAddVariable (p : ℕ) : RealAnalyticGerm p →ₐ[ℝ] RealAnalyticGerm (p + 1) :=
  analyticGermPullback (analyticGermDropCoordinate p)
    ((analyticGermDropCoordinate p).analyticAt 0) (map_zero _)

/-- Restrict a germ to the coordinate hyperplane where its first coordinate is zero. -/
def analyticGermRestrictVariable (p : ℕ) : RealAnalyticGerm (p + 1) →ₐ[ℝ] RealAnalyticGerm p :=
  analyticGermPullback (analyticGermInsertCoordinate p)
    ((analyticGermInsertCoordinate p).analyticAt 0) (map_zero _)

@[simp]
theorem analyticGermRestrict_addVariable (p : ℕ) (g : RealAnalyticGerm p) :
    analyticGermRestrictVariable p (analyticGermAddVariable p g) = g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  unfold analyticGermRestrictVariable analyticGermAddVariable
  rw [analyticGermPullback_of, analyticGermPullback_of, analyticGermOf_eq_iff]
  filter_upwards with x
  rfl

theorem analyticGermAddVariable_injective (p : ℕ) :
    Function.Injective (analyticGermAddVariable p) :=
  Function.LeftInverse.injective (analyticGermRestrict_addVariable p)

theorem analyticGermRestrictVariable_surjective (p : ℕ) :
    Function.Surjective (analyticGermRestrictVariable p) :=
  Function.RightInverse.surjective (analyticGermRestrict_addVariable p)

@[simp]
theorem analyticGermAddVariable_coordinate (p : ℕ) (i : Fin p) :
    analyticGermAddVariable p (analyticGermCoordinate p i) =
      analyticGermCoordinate (p + 1) i.succ := by
  apply Subtype.ext
  rfl

@[simp]
theorem analyticGermRestrictVariable_coordinate_zero (p : ℕ) :
    analyticGermRestrictVariable p (analyticGermCoordinate (p + 1) 0) = 0 := by
  apply Subtype.ext
  rfl

@[simp]
theorem analyticGermRestrictVariable_coordinate_succ (p : ℕ) (i : Fin p) :
    analyticGermRestrictVariable p (analyticGermCoordinate (p + 1) i.succ) =
      analyticGermCoordinate p i := by
  apply Subtype.ext
  rfl

end AbelFormalization
