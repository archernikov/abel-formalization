import AbelFormalization.AnalyticGermDerivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Coefficient and symbol derivations over actual analytic germs

Coefficient derivations act on every coefficient and fix the polynomial
symbols. Symbol derivations fix the coefficient algebra. Their definitions
are derivations over the actual constant scalar algebra, with explicit
coefficient formulas. The germ specialization differentiates actual analytic
representatives; it does not introduce a formal replacement coefficient ring.
-/

noncomputable section

namespace AbelFormalization

section Polynomial

variable {K B : Type*} [CommRing K] [CommRing B] [Algebra K B]

/-- Coefficientwise extension of a derivation to one additional symbol. -/
def polynomialCoefficientDerivation (D : Derivation K B B) :
    Derivation K (Polynomial B) (Polynomial B) :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem polynomialCoefficientDerivation_coeff (D : Derivation K B B)
    (P : Polynomial B) (n : ℕ) :
    (polynomialCoefficientDerivation D P).coeff n = D (P.coeff n) := rfl

@[simp]
theorem polynomialCoefficientDerivation_C (D : Derivation K B B) (b : B) :
    polynomialCoefficientDerivation D (Polynomial.C b) = Polynomial.C (D b) := by
  classical
  ext n
  by_cases hn : n = 0 <;> simp [Polynomial.coeff_C, hn]

@[simp]
theorem polynomialCoefficientDerivation_X (D : Derivation K B B) :
    polynomialCoefficientDerivation D Polynomial.X = 0 := by
  classical
  ext n
  simp [Polynomial.coeff_X, apply_ite]

/-- Differentiation in the extra symbol, viewed as a derivation over `K`. -/
def polynomialSymbolDerivation : Derivation K (Polynomial B) (Polynomial B) :=
  Polynomial.derivative'.restrictScalars K

@[simp]
theorem polynomialSymbolDerivation_apply (P : Polynomial B) :
    polynomialSymbolDerivation (K := K) P = Polynomial.derivative P := rfl

@[simp]
theorem polynomialSymbolDerivation_C (b : B) :
    polynomialSymbolDerivation (K := K) (Polynomial.C b) = 0 := by
  simp

@[simp]
theorem polynomialSymbolDerivation_X :
    polynomialSymbolDerivation (K := K) (Polynomial.X : Polynomial B) = 1 := by
  simp

end Polynomial

section MvPolynomial

variable {K B ι : Type*} [CommRing K] [CommRing B] [Algebra K B]

/-- The genuine coefficientwise linear map on multivariate polynomials. -/
def mvPolynomialCoefficientLinearMap (L : B →ₗ[K] B) :
    MvPolynomial ι B →ₗ[K] MvPolynomial ι B where
  toFun := AddMonoidAlgebra.map L.toAddMonoidHom
  map_add' := AddMonoidAlgebra.map_add L.toAddMonoidHom
  map_smul' c P := by
    apply MvPolynomial.ext
    intro d
    simp only [AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply,
      MvPolynomial.coeff_smul, LinearMap.toAddMonoidHom_coe, map_smul, RingHom.id_apply]

@[simp]
theorem mvPolynomialCoefficientLinearMap_coeff (L : B →ₗ[K] B)
    (P : MvPolynomial ι B) (d : ι →₀ ℕ) :
    (mvPolynomialCoefficientLinearMap L P).coeff d = L (P.coeff d) := rfl

@[simp]
theorem mvPolynomialCoefficientLinearMap_monomial (L : B →ₗ[K] B)
    (d : ι →₀ ℕ) (b : B) :
    mvPolynomialCoefficientLinearMap L (MvPolynomial.monomial d b) =
      MvPolynomial.monomial d (L b) := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases hde : d = e <;> simp [MvPolynomial.coeff_monomial, hde]

/-- Every derivation of the coefficient algebra extends to multivariate
polynomials by fixing all symbols. Leibniz is proved by coefficient convolution. -/
def mvPolynomialCoefficientDerivation (D : Derivation K B B) :
    Derivation K (MvPolynomial ι B) (MvPolynomial ι B) where
  toLinearMap := mvPolynomialCoefficientLinearMap D.toLinearMap
  map_one_eq_zero' := by
    change mvPolynomialCoefficientLinearMap D.toLinearMap
      (MvPolynomial.monomial 0 1) = 0
    rw [mvPolynomialCoefficientLinearMap_monomial]
    simp
  leibniz' P Q := by
    classical
    change mvPolynomialCoefficientLinearMap D.toLinearMap (P * Q) =
      P * mvPolynomialCoefficientLinearMap D.toLinearMap Q +
        Q * mvPolynomialCoefficientLinearMap D.toLinearMap P
    rw [mul_comm Q (mvPolynomialCoefficientLinearMap D.toLinearMap P)]
    apply MvPolynomial.ext
    intro d
    simp only [mvPolynomialCoefficientLinearMap_coeff, Derivation.coeFn_coe,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_mul,
      map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    exact mul_comm _ _

@[simp]
theorem mvPolynomialCoefficientDerivation_coeff (D : Derivation K B B)
    (P : MvPolynomial ι B) (d : ι →₀ ℕ) :
    (mvPolynomialCoefficientDerivation D P).coeff d = D (P.coeff d) := rfl

@[simp]
theorem mvPolynomialCoefficientDerivation_monomial (D : Derivation K B B)
    (d : ι →₀ ℕ) (b : B) :
    mvPolynomialCoefficientDerivation D (MvPolynomial.monomial d b) =
      MvPolynomial.monomial d (D b) :=
  mvPolynomialCoefficientLinearMap_monomial D.toLinearMap d b

@[simp]
theorem mvPolynomialCoefficientDerivation_C (D : Derivation K B B) (b : B) :
    mvPolynomialCoefficientDerivation (ι := ι) D (MvPolynomial.C b) =
      MvPolynomial.C (D b) :=
  mvPolynomialCoefficientDerivation_monomial D 0 b

@[simp]
theorem mvPolynomialCoefficientDerivation_X (D : Derivation K B B) (i : ι) :
    mvPolynomialCoefficientDerivation D (MvPolynomial.X i) = 0 := by
  classical
  change mvPolynomialCoefficientDerivation D
    (MvPolynomial.monomial (Finsupp.single i 1) 1) = 0
  simp

/-- The usual symbol partial derivative is linear over the scalar subalgebra. -/
def mvPolynomialSymbolDerivation (i : ι) :
    Derivation K (MvPolynomial ι B) (MvPolynomial ι B) :=
  (MvPolynomial.pderiv i).restrictScalars K

@[simp]
theorem mvPolynomialSymbolDerivation_apply (i : ι) (P : MvPolynomial ι B) :
    mvPolynomialSymbolDerivation (K := K) i P = MvPolynomial.pderiv i P := rfl

@[simp]
theorem mvPolynomialSymbolDerivation_C (i : ι) (b : B) :
    mvPolynomialSymbolDerivation (K := K) i (MvPolynomial.C b) = 0 := by
  exact MvPolynomial.pderiv_C

theorem mvPolynomialSymbolDerivation_X [DecidableEq ι] (i j : ι) :
    mvPolynomialSymbolDerivation (K := K) i (MvPolynomial.X j : MvPolynomial ι B) =
      if i = j then 1 else 0 := by
  classical
  simp [Pi.single_apply, eq_comm]

theorem mvPolynomialSymbolDerivation_coeff (i : ι) (P : MvPolynomial ι B)
    (d : ι →₀ ℕ) :
    (mvPolynomialSymbolDerivation (K := K) i P).coeff d =
      P.coeff (d + Finsupp.single i 1) * (d i + 1) :=
  MvPolynomial.coeff_pderiv P d

end MvPolynomial

section Germs

variable {ι : Type*}

/-- Differentiate the actual analytic-germ coefficients in coordinate `i`,
leaving every polynomial symbol fixed. -/
def analyticGermCoefficientPartial (p : ℕ) (i : Fin p) :
    Derivation ℝ (MvPolynomial ι (RealAnalyticGerm p))
      (MvPolynomial ι (RealAnalyticGerm p)) :=
  mvPolynomialCoefficientDerivation (analyticGermPartial p i)

@[simp]
theorem analyticGermCoefficientPartial_coeff (p : ℕ) (i : Fin p)
    (P : MvPolynomial ι (RealAnalyticGerm p)) (d : ι →₀ ℕ) :
    (analyticGermCoefficientPartial p i P).coeff d = analyticGermPartial p i (P.coeff d) := rfl

@[simp]
theorem analyticGermCoefficientPartial_C (p : ℕ) (i : Fin p) (g : RealAnalyticGerm p) :
    analyticGermCoefficientPartial (ι := ι) p i (MvPolynomial.C g) =
      MvPolynomial.C (analyticGermPartial p i g) :=
  mvPolynomialCoefficientDerivation_C _ _

@[simp]
theorem analyticGermCoefficientPartial_X (p : ℕ) (i : Fin p) (j : ι) :
    analyticGermCoefficientPartial p i (MvPolynomial.X j) = 0 :=
  mvPolynomialCoefficientDerivation_X _ _

/-- The coefficient partials differentiate coordinate germs by the usual
Kronecker rule inside the actual polynomial algebra. -/
theorem analyticGermCoefficientPartial_C_coordinate (p : ℕ) (i j : Fin p) :
    analyticGermCoefficientPartial (ι := ι) p i
        (MvPolynomial.C (analyticGermCoordinate p j)) =
      MvPolynomial.C (algebraMap ℝ (RealAnalyticGerm p) (if i = j then 1 else 0)) := by
  rw [analyticGermCoefficientPartial_C, analyticGermPartial_coordinate]

/-- On any coefficient represented by an analytic function, the coefficient
partial has the actual analytic partial derivative as representative. -/
theorem analyticGermCoefficientPartial_coeff_of (p : ℕ) (i : Fin p)
    (P : MvPolynomial ι (RealAnalyticGerm p)) (d : ι →₀ ℕ)
    (f : (Fin p → ℝ) → ℝ) (hf : AnalyticAt ℝ f 0)
    (hcoeff : P.coeff d = analyticGermOf f hf) :
    (analyticGermCoefficientPartial p i P).coeff d =
      analyticGermOf (fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)))
        (analyticAt_directionalDerivative hf (Pi.single i (1 : ℝ))) := by
  rw [analyticGermCoefficientPartial_coeff, hcoeff]
  exact analyticGermDerivation_of _ f hf

theorem analyticGermCoefficientPartial_coeff_value_of (p : ℕ) (i : Fin p)
    (P : MvPolynomial ι (RealAnalyticGerm p)) (d : ι →₀ ℕ)
    (f : (Fin p → ℝ) → ℝ) (hf : AnalyticAt ℝ f 0)
    (hcoeff : P.coeff d = analyticGermOf f hf) :
    analyticGermValue 0 ((analyticGermCoefficientPartial p i P).coeff d) =
      fderiv ℝ f 0 (Pi.single i (1 : ℝ)) := by
  rw [analyticGermCoefficientPartial_coeff_of p i P d f hf hcoeff]
  rfl

/-- Symbol partials on the same actual germ-coefficient polynomial algebra. -/
def analyticGermSymbolPartial (p : ℕ) (i : ι) :
    Derivation ℝ (MvPolynomial ι (RealAnalyticGerm p))
      (MvPolynomial ι (RealAnalyticGerm p)) :=
  mvPolynomialSymbolDerivation i

@[simp]
theorem analyticGermSymbolPartial_apply (p : ℕ) (i : ι)
    (P : MvPolynomial ι (RealAnalyticGerm p)) :
    analyticGermSymbolPartial p i P = MvPolynomial.pderiv i P := rfl

end Germs

end AbelFormalization
