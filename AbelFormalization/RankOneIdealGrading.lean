import AbelFormalization.LexicographicInitialIdealComponents
import AbelFormalization.RankOneIdealPolynomialModule

set_option autoImplicit false

/-!
# The canonical rank-one polynomial grading

An ideal has zero module shift.  These declarations package its positive
ordinary variable degrees and lexicographic variable weights as the concrete
`PolynomialGradedLexData` used by the bounded-window descent API.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

/-- The zero-shift rank-one grading attached to ordinary and vector weights
on the polynomial variables. -/
abbrev rankOnePolynomialGradedLexData
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ) :
    PolynomialGradedLexData n 1 h where
  ordinaryDegree := ordinaryDegree
  multiDegree := multiDegree
  ordinaryShift := fun _ => 0
  multiShift := fun _ _ => 0

@[simp]
theorem rankOnePolynomialGradedLexData_ordinaryDegree
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ) :
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).ordinaryDegree =
      ordinaryDegree := rfl

@[simp]
theorem rankOnePolynomialGradedLexData_multiDegree
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ) :
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).multiDegree =
      multiDegree := rfl

@[simp]
theorem rankOnePolynomialGradedLexData_ordinaryShift
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ) (k : Fin 1) :
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).ordinaryShift k = 0 := rfl

@[simp]
theorem rankOnePolynomialGradedLexData_multiShift
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ) (k : Fin 1) :
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).multiShift k = 0 := by
  funext j
  rfl

/-- Taking `toLex` commutes with an actual finitely supported weight sum. -/
theorem toLex_finsupp_weight
    (multiDegree : Fin n → Fin h → ℤ) (d : Fin n →₀ ℕ) :
    Finsupp.weight (fun i => toLex (multiDegree i)) d =
      toLex (Finsupp.weight multiDegree d) := by
  apply ofLex.injective
  exact lexicographicWeight_ofLex multiDegree d

@[simp]
theorem rankOnePolynomialGradedLexData_termOrdinaryDegree
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (d : Fin n →₀ ℕ) :
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).termOrdinaryDegree
        ((0 : Fin 1), d) =
      (Finsupp.weight ordinaryDegree d : ℤ) := by
  simp [PolynomialGradedLexData.termOrdinaryDegree,
    artinianPolynomialTermDegree]

@[simp]
theorem rankOnePolynomialGradedLexData_termWeight
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (d : Fin n →₀ ℕ) :
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).termWeight
        ((0 : Fin 1), d) =
      Finsupp.weight (fun i => toLex (multiDegree i)) d := by
  change toLex (Finsupp.weight multiDegree d + 0) = _
  rw [add_zero]
  exact (toLex_finsupp_weight multiDegree d).symm

/-- The unique coordinate of the module weight projection is the ordinary
multivariate-polynomial weight projection. -/
theorem rankOnePolynomial_weightFiberComponent_zero
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (weight : PolynomialLexWeight h)
    (P : MvPolynomial (Fin n) B) :
    (artinianPolynomialModuleFiberComponent
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).termWeight
        weight (rankOnePolynomialModuleCoeffEquiv P) 0) =
      MvPolynomial.weightedHomogeneousComponent
        (fun i => toLex (multiDegree i)) weight P := by
  classical
  ext d
  rw [artinianPolynomialModuleFiberComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [rankOnePolynomialModuleCoeffEquiv_apply,
    rankOnePolynomialGradedLexData_termWeight]

end AbelFormalization
