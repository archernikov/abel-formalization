import AbelFormalization.FullRankMinor
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

/-!
# Full row rank from a surjective Jacobian factorization

Surjectivity of the matrix linear map identifies its range with the entire
finite-dimensional target. A factorization through an arbitrary source map
then gives full row rank without choosing coordinates or a basis on that
source.
-/

noncomputable section

namespace AbelFormalization

section MatrixRank

variable {K E ι : Type*} [Field K] [Fintype ι] {n : ℕ}

/-- A surjective matrix linear map has full row rank. -/
theorem matrix_rank_eq_of_mulVecLin_surjective
    (A : Matrix (Fin n) ι K) (hA : Function.Surjective A.mulVecLin) :
    A.rank = n := by
  rw [Matrix.rank, LinearMap.range_eq_top.mpr hA, finrank_top,
    Module.finrank_pi, Fintype.card_fin]

/-- A surjective function factoring through a matrix makes the matrix
linear map surjective. The intermediary map need not be linear. -/
theorem matrix_mulVecLin_surjective_of_factorization
    (A : Matrix (Fin n) ι K) (L : E → (Fin n → K))
    (H : E → (ι → K)) (hL : Function.Surjective L)
    (hfactor : ∀ h, L h = A.mulVec (H h)) :
    Function.Surjective A.mulVecLin := by
  intro y
  obtain ⟨h, hy⟩ := hL y
  refine ⟨H h, ?_⟩
  rw [Matrix.mulVecLin_apply, ← hfactor h, hy]

/-- A surjective factorization gives full row rank, without any vector
space structure or dimension assumption on its source. -/
theorem matrix_rank_eq_of_surjective_factorization
    (A : Matrix (Fin n) ι K) (L : E → (Fin n → K))
    (H : E → (ι → K)) (hL : Function.Surjective L)
    (hfactor : ∀ h, L h = A.mulVec (H h)) :
    A.rank = n :=
  matrix_rank_eq_of_mulVecLin_surjective A
    (matrix_mulVecLin_surjective_of_factorization A L H hL hfactor)

end MatrixRank

section RealMinorPositivity

variable {E ι : Type*} [Fintype ι] {n : ℕ}

/-- Over the reals, the squared-minor denominator is positive whenever
the matrix factors a surjection, for an arbitrary source set. -/
theorem sumSquaresColumnMinors_pos_of_surjective_factorization
    (A : Matrix (Fin n) ι ℝ) (L : E → (Fin n → ℝ))
    (H : E → (ι → ℝ)) (hL : Function.Surjective L)
    (hfactor : ∀ h, L h = A.mulVec (H h)) :
    0 < sumSquaresColumnMinors A :=
  sumSquaresColumnMinors_pos_of_rank_eq A
    (matrix_rank_eq_of_surjective_factorization A L H hL hfactor)

/-- The chain-rule application for a surjective continuous linear map.
The source can be infinite-dimensional, and no source basis is required. -/
theorem sumSquaresColumnMinors_pos_of_surjective_continuousLinearMap_factorization
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Matrix (Fin n) ι ℝ) (L : E →L[ℝ] (Fin n → ℝ))
    (H : E → (ι → ℝ)) (hL : Function.Surjective L)
    (hfactor : ∀ h, L h = A.mulVec (H h)) :
    0 < sumSquaresColumnMinors A :=
  sumSquaresColumnMinors_pos_of_surjective_factorization A L H hL hfactor

end RealMinorPositivity

end AbelFormalization
