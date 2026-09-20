import AbelFormalization.AnalyticGermComposition
import AbelFormalization.AnalyticGermOneVariable
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Nonzero analytic directions

A nonzero actual analytic germ remains nonzero on some line through its base
point. The proof uses its convergent multilinear expansion and uniqueness of
the one-variable series obtained by restricting to a line.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear parametrization of the line in direction `v`. -/
def analyticDirectionMap (v : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

@[simp]
theorem analyticDirectionMap_apply (v : E) (t : ℝ) : analyticDirectionMap v t = t • v := rfl

/-- Restriction to a line preserves real analyticity. -/
theorem analyticAt_comp_direction {f : E → ℝ} (hf : AnalyticAt ℝ f 0) (v : E) :
    AnalyticAt ℝ (fun t : ℝ => f (t • v)) 0 :=
  hf.comp_of_eq ((analyticDirectionMap v).analyticAt 0) (zero_smul ℝ v)

/-- Vanishing as a germ on every line forces an analytic function to vanish
as a multivariable germ. The line neighborhoods need not be uniform. -/
theorem analyticAt_eventuallyEq_zero_of_line_restrictions {f : E → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hlines : ∀ v : E, (fun t : ℝ => f (t • v)) =ᶠ[𝓝 0] 0) :
    f =ᶠ[𝓝 0] 0 := by
  obtain ⟨p, r, hp⟩ := hf
  have hdiag : ∀ (n : ℕ) (v : E), p n (fun _ => v) = 0 := by
    intro n v
    have hseries : HasFPowerSeriesAt f p (analyticDirectionMap v 0) := by
      simpa using hp.hasFPowerSeriesAt
    have hzero := (hseries.compContinuousLinearMap).eq_zero_of_eventually (hlines v)
    have he := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q n (fun _ => 1)) hzero
    simpa [FormalMultilinearSeries.compContinuousLinearMap, analyticDirectionMap] using he
  filter_upwards [Metric.eball_mem_nhds (0 : E) hp.r_pos] with y hy
  have hsum := hp.hasSum hy
  have hsumzero : HasSum (fun n : ℕ => p n (fun _ => y)) (0 : ℝ) := by
    simpa only [hdiag] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  simpa only [zero_add, Pi.zero_apply] using hsum.unique hsumzero

/-- Restrict an actual analytic germ to a line through zero. -/
def analyticGermAlong (v : E) : AnalyticGermAt (0 : E) →ₐ[ℝ] AnalyticGermAt (0 : ℝ) :=
  analyticGermPullback (analyticDirectionMap v)
    ((analyticDirectionMap v).analyticAt 0) (map_zero _)

@[simp]
theorem analyticGermAlong_of (v : E) (f : E → ℝ) (hf : AnalyticAt ℝ f 0) :
    analyticGermAlong v (analyticGermOf f hf) =
      analyticGermOf (fun t : ℝ => f (t • v)) (analyticAt_comp_direction hf v) := rfl

@[simp]
theorem analyticGermAlong_value (v : E) (g : AnalyticGermAt (0 : E)) :
    analyticGermValue (0 : ℝ) (analyticGermAlong v g) = analyticGermValue (0 : E) g :=
  analyticGermValue_pullback _ _ _ _

/-- Every nonzero analytic germ has a nonzero restriction to some real line. -/
theorem exists_analyticGermAlong_ne_zero (g : AnalyticGermAt (0 : E)) (hg : g ≠ 0) :
    ∃ v : E, analyticGermAlong v g ≠ 0 := by
  classical
  by_contra! hzero
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  apply hg
  apply (analyticGermOf_eq_zero_iff hf).mpr
  apply analyticAt_eventuallyEq_zero_of_line_restrictions hf
  intro v
  exact (analyticGermOf_eq_zero_iff (analyticAt_comp_direction hf v)).mp (hzero v)

/-- For a nonunit germ, a nonzero line restriction necessarily has nonzero direction. -/
theorem analyticGermAlong_direction_ne_zero {g : AnalyticGermAt (0 : E)}
    (hunit : ¬ IsUnit g) {v : E} (hv : analyticGermAlong v g ≠ 0) : v ≠ 0 := by
  intro he
  subst v
  have hg0 : analyticGermValue (0 : E) g = 0 := by
    by_contra hne
    exact hunit ((isUnit_analyticGerm_iff g).mpr hne)
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  apply hv
  rw [analyticGermAlong_of]
  apply (analyticGermOf_eq_zero_iff (analyticAt_comp_direction hf 0)).mpr
  change f 0 = 0 at hg0
  exact Eventually.of_forall fun t => by simpa only [smul_zero, Pi.zero_apply] using hg0

/-- In a nontrivial parameter space, the regular direction can always be
chosen nonzero, including when the original germ is a unit. -/
theorem exists_nonzero_analyticGermAlong [Nontrivial E]
    (g : AnalyticGermAt (0 : E)) (hg : g ≠ 0) :
    ∃ v : E, v ≠ 0 ∧ analyticGermAlong v g ≠ 0 := by
  classical
  by_cases hu : IsUnit g
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact ⟨v, hv, (hu.map (analyticGermAlong v).toRingHom).ne_zero⟩
  · obtain ⟨v, hv⟩ := exists_analyticGermAlong_ne_zero g hg
    exact ⟨v, analyticGermAlong_direction_ne_zero hu hv, hv⟩

/-- A nonzero analytic function germ has a nonzero direction with finite
one-variable analytic order. This statement concerns ordinary functions. -/
theorem analyticAt_exists_direction_finite_order [Nontrivial E] {f : E → ℝ}
    (hf : AnalyticAt ℝ f 0) (hne : ¬ f =ᶠ[𝓝 0] 0) :
    ∃ v : E, v ≠ 0 ∧ AnalyticAt ℝ (fun t : ℝ => f (t • v)) 0 ∧
      analyticOrderAt (fun t : ℝ => f (t • v)) 0 ≠ ⊤ := by
  have hg : analyticGermOf f hf ≠ 0 := fun h => hne ((analyticGermOf_eq_zero_iff hf).mp h)
  obtain ⟨v, hv, hline⟩ := exists_nonzero_analyticGermAlong (analyticGermOf f hf) hg
  refine ⟨v, hv, analyticAt_comp_direction hf v, fun h => hline ?_⟩
  exact (analyticGermOf_eq_zero_iff (analyticAt_comp_direction hf v)).mpr
    (analyticOrderAt_eq_top.mp h)

/-- A linear coordinate change acts on germs at zero. -/
def analyticGermLinearChange (e : E ≃L[ℝ] E) :
    AnalyticGermAt (0 : E) ≃ₐ[ℝ] AnalyticGermAt (0 : E) :=
  analyticGermEquivOfLocalInverse e e.symm
    (e.toContinuousLinearMap.analyticAt 0) (e.symm.toContinuousLinearMap.analyticAt 0)
    (map_zero _) (map_zero _)
    (Eventually.of_forall e.symm_apply_apply) (Eventually.of_forall e.apply_symm_apply)

@[simp]
theorem analyticGermLinearChange_value (e : E ≃L[ℝ] E) (g : AnalyticGermAt (0 : E)) :
    analyticGermValue (0 : E) (analyticGermLinearChange e g) =
      analyticGermValue (0 : E) g :=
  analyticGermValue_pullback e (e.toContinuousLinearMap.analyticAt 0) (map_zero e) g

/-- Restricting after a coordinate change is restriction along the image direction. -/
theorem analyticGermAlong_linearChange (e : E ≃L[ℝ] E) (v : E)
    (g : AnalyticGermAt (0 : E)) :
    analyticGermAlong v (analyticGermLinearChange e g) = analyticGermAlong (e v) g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  let hcomp : AnalyticAt ℝ (f ∘ e) 0 :=
    hf.comp_of_eq (e.toContinuousLinearMap.analyticAt 0) (map_zero e)
  change analyticGermOf (fun t : ℝ => f (e (t • v)))
      (analyticAt_comp_direction hcomp v) =
    analyticGermOf (fun t : ℝ => f (t • e v)) (analyticAt_comp_direction hf (e v))
  apply (analyticGermOf_eq_iff (analyticAt_comp_direction hcomp v)
    (analyticAt_comp_direction hf (e v))).mpr
  exact Eventually.of_forall fun t => congrArg f (e.map_smul t v)

/-- A nonzero vector is the image of any selected coordinate vector under an
invertible continuous linear change of finite real coordinates. -/
theorem exists_continuousLinearEquiv_coordinate_axis {σ : Type*} [Fintype σ]
    [DecidableEq σ] (i : σ) (v : σ → ℝ) (hv : v ≠ 0) :
    ∃ e : (σ → ℝ) ≃L[ℝ] (σ → ℝ), e (Pi.single i 1) = v := by
  classical
  let b : σ → ℝ := Pi.single i 1
  have hform : ∃ φ : Module.Dual ℝ (σ → ℝ), φ b = 1 ∧ φ v ≠ 0 := by
    by_cases hvi : v i = 0
    · have hex : ∃ j, v j ≠ 0 := by
        by_contra! hz
        exact hv (funext hz)
      obtain ⟨j, hj⟩ := hex
      have hji : j ≠ i := by intro h; subst j; exact hj hvi
      refine ⟨LinearMap.proj (R := ℝ) (φ := fun _ : σ => ℝ) i +
        LinearMap.proj j, ?_, ?_⟩
      · simp [b, hji]
      · simpa [hvi] using hj
    · exact ⟨LinearMap.proj (R := ℝ) (φ := fun _ : σ => ℝ) i,
        by simp [b], hvi⟩
  obtain ⟨φ, hφb, hφv⟩ := hform
  have hunit : IsUnit (1 + φ (v - b)) := by
    rw [map_sub, hφb]
    simpa only [add_sub_cancel] using (isUnit_iff_ne_zero.mpr hφv)
  let e := LinearEquiv.dilatransvection hunit
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  change b + φ b • (v - b) = v
  rw [hφb, one_smul]
  abel

/-- A nonzero vector is the image of the first coordinate vector. -/
theorem exists_continuousLinearEquiv_first_axis (p : ℕ)
    (v : Fin (p + 1) → ℝ) (hv : v ≠ 0) :
    ∃ e : (Fin (p + 1) → ℝ) ≃L[ℝ] (Fin (p + 1) → ℝ),
      e (Pi.single 0 1) = v :=
  exists_continuousLinearEquiv_coordinate_axis 0 v hv

/-- Every nonzero germ becomes regular on any selected coordinate axis after
an actual linear coordinate automorphism. -/
theorem exists_regularizing_coordinate_linearChange {σ : Type*} [Fintype σ]
    [DecidableEq σ] (i : σ) (g : AnalyticGermAt (0 : σ → ℝ)) (hg : g ≠ 0) :
    ∃ e : (σ → ℝ) ≃L[ℝ] (σ → ℝ),
      analyticGermAlong (Pi.single i 1) (analyticGermLinearChange e g) ≠ 0 := by
  let : Nonempty σ := ⟨i⟩
  obtain ⟨v, hv, hgv⟩ := exists_nonzero_analyticGermAlong g hg
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_coordinate_axis i v hv
  refine ⟨e, ?_⟩
  rwa [analyticGermAlong_linearChange, he]

/-- Every nonzero multivariable analytic germ becomes regular on the first
coordinate axis after an actual linear coordinate automorphism. -/
theorem exists_regularizing_linearChange (p : ℕ) (g : RealAnalyticGerm (p + 1))
    (hg : g ≠ 0) :
    ∃ e : (Fin (p + 1) → ℝ) ≃L[ℝ] (Fin (p + 1) → ℝ),
      analyticGermAlong (Pi.single 0 1) (analyticGermLinearChange e g) ≠ 0 :=
  exists_regularizing_coordinate_linearChange 0 g hg

/-- The regularized axis germ has a finite order and an invertible leading factor. -/
theorem exists_regularizing_linearChange_order (p : ℕ) (g : RealAnalyticGerm (p + 1))
    (hg : g ≠ 0) :
    ∃ e : (Fin (p + 1) → ℝ) ≃L[ℝ] (Fin (p + 1) → ℝ),
      ∃ n : ℕ, ∃ u : AnalyticGermAt (0 : ℝ), IsUnit u ∧
        analyticGermAlong (Pi.single 0 1) (analyticGermLinearChange e g) =
          analyticGermParameter 0 ^ n * u := by
  obtain ⟨e, he⟩ := exists_regularizing_linearChange p g hg
  obtain ⟨n, u, hu, hfactor⟩ := analyticGerm_exists_parameter_pow_mul_unit _ he
  exact ⟨e, n, u, hu, hfactor⟩

/-- A nonzero nonunit becomes regular of a finite positive order after a
linear coordinate automorphism. -/
theorem exists_regularizing_linearChange_positive_order (p : ℕ)
    (g : RealAnalyticGerm (p + 1)) (hg : g ≠ 0) (hunit : ¬ IsUnit g) :
    ∃ e : (Fin (p + 1) → ℝ) ≃L[ℝ] (Fin (p + 1) → ℝ),
      ∃ n : ℕ, 0 < n ∧ ∃ u : AnalyticGermAt (0 : ℝ), IsUnit u ∧
        analyticGermAlong (Pi.single 0 1) (analyticGermLinearChange e g) =
          analyticGermParameter 0 ^ n * u := by
  obtain ⟨e, n, u, hu, hfactor⟩ := exists_regularizing_linearChange_order p g hg
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hline : IsUnit (analyticGermAlong (Pi.single 0 1) (analyticGermLinearChange e g)) := by
      rw [hfactor]
      simpa only [pow_zero, one_mul] using hu
    apply hunit
    apply (isUnit_analyticGerm_iff g).mpr
    simpa only [analyticGermAlong_value, analyticGermLinearChange_value] using
      (isUnit_analyticGerm_iff _).mp hline
  exact ⟨e, n, Nat.pos_of_ne_zero hn, u, hu, hfactor⟩

end AbelFormalization
