import AbelFormalization.AnalyticGermGenerators
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The cotangent space of the real-analytic germ ring

Differentiation at zero identifies the cotangent space with the coordinate
space. In particular its real dimension is the number of variables, without
assuming Noetherianity of the analytic germ ring.
-/

noncomputable section

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation is linear over the actual constant real germs. -/
def analyticGermValueLinear (x : E) : AnalyticGermAt x →ₗ[ℝ] ℝ where
  toFun := analyticGermValue x
  map_add' := map_add (analyticGermValue x)
  map_smul' c g := by
    change analyticGermValue x (algebraMap ℝ (AnalyticGermAt x) c * g) =
      c * analyticGermValue x g
    rw [map_mul, analyticGermValue_algebraMap]

/-- The gradient of an analytic germ, evaluated at the origin. -/
def analyticGermGradient (p : ℕ) : RealAnalyticGerm p →ₗ[ℝ] (Fin p → ℝ) :=
  LinearMap.pi fun i => (analyticGermValueLinear 0).comp (analyticGermPartial p i).toLinearMap

@[simp]
theorem analyticGermGradient_apply (p : ℕ) (g : RealAnalyticGerm p) (i : Fin p) :
    analyticGermGradient p g i =
      analyticGermValue 0 (analyticGermPartial p i g) := rfl

@[simp]
theorem analyticGermValue_coordinate (p : ℕ) (i : Fin p) :
    analyticGermValue 0 (analyticGermCoordinate p i) = 0 := rfl

theorem analyticGermCoordinate_mem_maximalIdeal (p : ℕ) (i : Fin p) :
    analyticGermCoordinate p i ∈ IsLocalRing.maximalIdeal (RealAnalyticGerm p) := by
  rw [analyticGerm_mem_maximalIdeal_iff, analyticGermValue_coordinate]

theorem analyticGermGradient_mul (p : ℕ) (f g : RealAnalyticGerm p) (i : Fin p) :
    analyticGermGradient p (f * g) i =
      analyticGermValue 0 f * analyticGermGradient p g i +
        analyticGermValue 0 g * analyticGermGradient p f i := by
  simp only [analyticGermGradient_apply, Derivation.leibniz, smul_eq_mul, map_add, map_mul]

/-- At zero, differentiation of a coordinate decomposition recovers the
values of its analytic coefficient germs. -/
theorem analyticGermGradient_sum_coordinates (p : ℕ)
    (g : Fin p → RealAnalyticGerm p) (j : Fin p) :
    analyticGermGradient p (∑ i, analyticGermCoordinate p i * g i) j =
      analyticGermValue 0 (g j) := by
  classical
  change analyticGermValue 0
    (analyticGermPartial p j (∑ i, analyticGermCoordinate p i * g i)) = _
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    analyticGermValue_coordinate, zero_mul, zero_add]
  simp_rw [analyticGermPartial_coordinate]
  simp

/-- A germ vanishing to first order belongs to the square of the maximal
ideal; the proof uses the convergent analytic Hadamard coefficients. -/
theorem analyticGerm_mem_maximalIdeal_sq_of_gradient_zero (p : ℕ)
    (f : RealAnalyticGerm p)
    (hf : f ∈ IsLocalRing.maximalIdeal (RealAnalyticGerm p))
    (hgrad : analyticGermGradient p f = 0) :
    f ∈ IsLocalRing.maximalIdeal (RealAnalyticGerm p) ^ 2 := by
  obtain ⟨g, rfl⟩ := analyticGerm_exists_eq_sum_coordinates p f
    ((analyticGerm_mem_maximalIdeal_iff f).mp hf)
  rw [pow_two]
  apply Submodule.sum_mem
  intro i hi
  apply Ideal.mul_mem_mul (analyticGermCoordinate_mem_maximalIdeal p i)
  rw [analyticGerm_mem_maximalIdeal_iff]
  have he := congrFun hgrad i
  simpa only [analyticGermGradient_sum_coordinates, Pi.zero_apply] using he

/-- The derivative of a cotangent class, using the actual quotient by the
square of the maximal ideal. -/
def analyticGermCotangentGradient (p : ℕ) :
    IsLocalRing.CotangentSpace (RealAnalyticGerm p) →ₗ[ℝ] (Fin p → ℝ) :=
  Ideal.Cotangent.lift
    ((analyticGermGradient p).comp
      ((IsLocalRing.maximalIdeal (RealAnalyticGerm p)).subtype.restrictScalars ℝ))
    (by
      intro f g
      ext i
      change analyticGermGradient p ((f : RealAnalyticGerm p) * g) i = 0
      rw [analyticGermGradient_mul,
        (analyticGerm_mem_maximalIdeal_iff _).mp f.property,
        (analyticGerm_mem_maximalIdeal_iff _).mp g.property]
      simp)

@[simp]
theorem analyticGermCotangentGradient_toCotangent (p : ℕ)
    (f : IsLocalRing.maximalIdeal (RealAnalyticGerm p)) :
    analyticGermCotangentGradient p
      ((IsLocalRing.maximalIdeal (RealAnalyticGerm p)).toCotangent f) =
        analyticGermGradient p f := rfl

theorem analyticGermCotangentGradient_injective (p : ℕ) :
    Function.Injective (analyticGermCotangentGradient p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal (RealAnalyticGerm p)).toCotangent_surjective x
  rw [Ideal.toCotangent_eq_zero]
  exact analyticGerm_mem_maximalIdeal_sq_of_gradient_zero p f f.property hx

theorem analyticGermCotangentGradient_surjective (p : ℕ) :
    Function.Surjective (analyticGermCotangentGradient p) := by
  intro v
  let f : RealAnalyticGerm p :=
    ∑ i, analyticGermCoordinate p i * algebraMap ℝ (RealAnalyticGerm p) (v i)
  have hf : f ∈ IsLocalRing.maximalIdeal (RealAnalyticGerm p) := by
    apply Submodule.sum_mem
    intro i hi
    exact Ideal.mul_mem_right _ _ (analyticGermCoordinate_mem_maximalIdeal p i)
  refine ⟨(IsLocalRing.maximalIdeal (RealAnalyticGerm p)).toCotangent ⟨f, hf⟩, ?_⟩
  ext i
  change analyticGermGradient p f i = v i
  simp only [f, analyticGermGradient_sum_coordinates, analyticGermValue_algebraMap]

/-- The actual cotangent space is linearly isomorphic to the real coordinate
space through the gradient at zero. -/
def analyticGermCotangentEquiv (p : ℕ) :
    IsLocalRing.CotangentSpace (RealAnalyticGerm p) ≃ₗ[ℝ] (Fin p → ℝ) :=
  LinearEquiv.ofBijective (analyticGermCotangentGradient p)
    ⟨analyticGermCotangentGradient_injective p, analyticGermCotangentGradient_surjective p⟩

instance analyticGermCotangentFiniteDimensional (p : ℕ) :
    FiniteDimensional ℝ (IsLocalRing.CotangentSpace (RealAnalyticGerm p)) :=
  Module.Finite.equiv (analyticGermCotangentEquiv p).symm

/-- The cotangent dimension is exactly the number of analytic variables. -/
theorem analyticGerm_cotangent_finrank (p : ℕ) :
    Module.finrank ℝ (IsLocalRing.CotangentSpace (RealAnalyticGerm p)) = p := by
  rw [(analyticGermCotangentEquiv p).finrank_eq]
  simp

/-- Gradient coordinates respect the actual residue-field action via its
canonical identification with the real numbers. -/
theorem analyticGermCotangentGradient_residue_smul (p : ℕ)
    (a : IsLocalRing.ResidueField (RealAnalyticGerm p))
    (x : IsLocalRing.CotangentSpace (RealAnalyticGerm p)) :
    analyticGermCotangentGradient p (a • x) =
      analyticGermResidueEquiv 0 a • analyticGermCotangentGradient p x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal (RealAnalyticGerm p)).toCotangent_surjective x
  have he : analyticGermResidueEquiv 0
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (RealAnalyticGerm p)) a) =
        analyticGermValue 0 a := analyticGermResidueEquiv_residue 0 a
  rw [he]
  change analyticGermCotangentGradient p
      (a • (IsLocalRing.maximalIdeal (RealAnalyticGerm p)).toCotangent f) = _
  rw [← map_smul, analyticGermCotangentGradient_toCotangent]
  ext i
  change analyticGermGradient p (a * (f : RealAnalyticGerm p)) i =
    analyticGermValue 0 a * analyticGermGradient p f i
  rw [analyticGermGradient_mul, (analyticGerm_mem_maximalIdeal_iff _).mp f.property]
  simp

/-- The embedding dimension over the actual residue field is exactly the
number of variables. This conclusion does not require Noetherianity. -/
theorem analyticGerm_cotangent_residue_finrank (p : ℕ) :
    Module.finrank (IsLocalRing.ResidueField (RealAnalyticGerm p))
      (IsLocalRing.CotangentSpace (RealAnalyticGerm p)) = p := by
  have h := rank_eq_of_equiv_equiv (analyticGermResidueEquiv (0 : Fin p → ℝ))
    (analyticGermCotangentEquiv p).toAddEquiv (analyticGermResidueEquiv 0).bijective
    (analyticGermCotangentGradient_residue_smul p)
  have hn := congrArg Cardinal.toNat h
  change Module.finrank (IsLocalRing.ResidueField (RealAnalyticGerm p))
    (IsLocalRing.CotangentSpace (RealAnalyticGerm p)) = Module.finrank ℝ (Fin p → ℝ) at hn
  simpa only [Module.finrank_pi, Fintype.card_fin] using hn

end AbelFormalization
