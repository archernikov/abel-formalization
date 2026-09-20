import AbelFormalization.PolynomialExtraction
import AbelFormalization.AnalyticGermNoetherian

/-! # Real polynomial extraction from high-height analytic-germ ideals

This specializes the local-ring extraction theorem to the actual ring of
real-analytic germs. Noetherianity, locality, the dimension, and the real
augmentation have all been established from the analytic representatives.
The conclusion is Lemma `lem:height`(3) of the manuscript, strengthened to a
monic univariate polynomial.
-/

noncomputable section

namespace AbelFormalization

open scoped Polynomial

section Value

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Base-point evaluation as the actual real-algebra augmentation. -/
def analyticGermValueAlgHom (x : E) : AnalyticGermAt x →ₐ[ℝ] ℝ where
  toRingHom := analyticGermValue x
  commutes' c := analyticGermValue_algebraMap x c

@[simp]
theorem analyticGermValueAlgHom_apply (x : E) (g : AnalyticGermAt x) :
    analyticGermValueAlgHom x g = analyticGermValue x g := rfl

end Value

/-- Lemma `lem:height`(3), with the stronger monic conclusion. -/
theorem analyticGerm_polynomial_monic_extraction (p m : ℕ)
    (I : Ideal (MvPolynomial (Fin m) (RealAnalyticGerm p)))
    (hI : (p + m : ℕ∞) ≤ I.height) (i : Fin m) :
    ∃ f : ℝ[X], f.Monic ∧
      scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i f ∈ I :=
  mvPolynomial_contains_monic_univariate_of_height
    (analyticGermValueAlgHom (0 : Fin p → ℝ)) p m
    (realAnalyticGerm_dimension p) I hI i

/-- A high-height ideal contains a nonzero real polynomial in each selected
variable. Nonvanishing is supplied both before and after coefficient embedding. -/
theorem analyticGerm_height_polynomial_extraction (p m : ℕ)
    (I : Ideal (MvPolynomial (Fin m) (RealAnalyticGerm p)))
    (hI : (p + m : ℕ∞) ≤ I.height) (i : Fin m) :
    ∃ f : ℝ[X], f ≠ 0 ∧
      scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i f ≠ 0 ∧
      scalarUnivariateEmbedding ℝ (RealAnalyticGerm p) i f ∈ I :=
  mvPolynomial_contains_nonzero_univariate_of_height
    (analyticGermValueAlgHom (0 : Fin p → ℝ)) p m
    (realAnalyticGerm_dimension p) I hI i

end AbelFormalization
