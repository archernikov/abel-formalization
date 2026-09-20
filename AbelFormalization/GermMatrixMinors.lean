import AbelFormalization.FullRankMinor
import AbelFormalization.PolynomialGermIdentities

set_option autoImplicit false

/-!
# Matrix minors and their actual germ representatives

Determinants and finite sums of squared column minors commute with ring
homomorphisms. In particular, matrices of function representatives represent
the corresponding matrices over a germ ring. For analytic-germ coefficients
we apply the actual polynomial-valued germ homomorphism. This does not require
or construct a simultaneous nearby evaluation map on all analytic germs.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

section RingNaturality

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] {n : ℕ}

/-- The finite squared-minor sum is natural under every ring homomorphism. -/
theorem map_sumSquaresColumnMinors (φ : R →+* S)
    (A : Matrix (Fin n) ι R) :
    φ (sumSquaresColumnMinors A) = sumSquaresColumnMinors (A.map φ) := by
  classical
  unfold sumSquaresColumnMinors
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hmatrix : φ.mapMatrix (A.submatrix id c) = (A.map φ).submatrix id c := by
    funext i j
    rfl
  rw [map_pow, φ.map_det (A.submatrix id c), hmatrix]

/-- Evaluation of the independent polynomial symbols preserves the entire
squared-minor sum, with no restriction on their values. -/
theorem eval_sumSquaresColumnMinors {σ : Type*}
    (z : σ → R) (A : Matrix (Fin n) ι (MvPolynomial σ R)) :
    MvPolynomial.eval z (sumSquaresColumnMinors A) =
      sumSquaresColumnMinors (A.map (MvPolynomial.eval z)) :=
  map_sumSquaresColumnMinors (MvPolynomial.eval z) A

end RingNaturality

section GermRepresentatives

variable {E R S κ ι : Type*} [CommRing R] [CommRing S]

/-- The determinant of a matrix of function germs is represented by the
pointwise determinant of those functions. -/
theorem germ_coe_det [Fintype κ] [DecidableEq κ]
    (l : Filter E) (F : E → Matrix κ κ R) :
    ((fun w => (F w).det) : Germ l R) =
      Matrix.det (fun i j => ((fun w => F w i j) : Germ l R)) := by
  let A : Matrix κ κ (E → R) := fun i j w => F w i j
  have hpoint : (fun w => (F w).det) = A.det := by
    funext w
    have hmatrix : (Pi.evalRingHom (fun _ : E => R) w).mapMatrix A = F w := by
      funext i j
      rfl
    have hdet := (Pi.evalRingHom (fun _ : E => R) w).map_det A
    rw [hmatrix] at hdet
    exact hdet.symm
  have hmatrix : (Germ.coeRingHom l).mapMatrix A =
      (fun i j => ((fun w => F w i j) : Germ l R)) := by
    funext i j
    rfl
  rw [hpoint]
  have hdet := (Germ.coeRingHom l).map_det A
  rw [hmatrix] at hdet
  exact hdet

/-- The same representative identity for the finite squared-minor sum. -/
theorem germ_coe_sumSquaresColumnMinors [Fintype ι] {n : ℕ}
    (l : Filter E) (F : E → Matrix (Fin n) ι R) :
    ((fun w => sumSquaresColumnMinors (F w)) : Germ l R) =
      sumSquaresColumnMinors
        (fun i j => ((fun w => F w i j) : Germ l R)) := by
  let A : Matrix (Fin n) ι (E → R) := fun i j w => F w i j
  have hpoint : (fun w => sumSquaresColumnMinors (F w)) =
      sumSquaresColumnMinors A := by
    funext w
    have hmatrix : A.map (Pi.evalRingHom (fun _ : E => R) w) = F w := by
      funext i j
      rfl
    have hsum := map_sumSquaresColumnMinors (Pi.evalRingHom (fun _ : E => R) w) A
    rw [hmatrix] at hsum
    exact hsum.symm
  have hmatrix : A.map (Germ.coeRingHom l) =
      (fun i j => ((fun w => F w i j) : Germ l R)) := by
    funext i j
    rfl
  rw [hpoint]
  rw [← hmatrix]
  exact map_sumSquaresColumnMinors (Germ.coeRingHom l) A

/-- Any entrywise representatives of a matrix mapped to a germ ring also
represent its determinant. -/
theorem map_det_eq_germ_of_representatives [Fintype κ] [DecidableEq κ]
    (l : Filter E) (φ : R →+* Germ l S)
    (A : Matrix κ κ R) (F : E → Matrix κ κ S)
    (hF : ∀ i j, φ (A i j) = ((fun w => F w i j) : Germ l S)) :
    φ A.det = ((fun w => (F w).det) : Germ l S) := by
  have hmatrix : A.map φ =
      (fun i j => ((fun w => F w i j) : Germ l S)) := by
    funext i j
    exact hF i j
  rw [φ.map_det A, RingHom.mapMatrix_apply, hmatrix]
  exact (germ_coe_det l F).symm

/-- Any entrywise representatives of a matrix mapped to a germ ring also
represent its squared-minor sum. -/
theorem map_sumSquaresColumnMinors_eq_germ_of_representatives
    [Fintype ι] {n : ℕ} (l : Filter E) (φ : R →+* Germ l S)
    (A : Matrix (Fin n) ι R) (F : E → Matrix (Fin n) ι S)
    (hF : ∀ i j, φ (A i j) = ((fun w => F w i j) : Germ l S)) :
    φ (sumSquaresColumnMinors A) =
      ((fun w => sumSquaresColumnMinors (F w)) : Germ l S) := by
  have hmatrix : A.map φ =
      (fun i j => ((fun w => F w i j) : Germ l S)) := by
    funext i j
    exact hF i j
  rw [map_sumSquaresColumnMinors, hmatrix]
  exact (germ_coe_sumSquaresColumnMinors l F).symm

end GermRepresentatives

section AnalyticPolynomialMatrixRepresentatives

variable {E σ κ ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A formal determinant with actual analytic-germ coefficients is
represented by the determinant of any chosen polynomial-valued matrix
representative. -/
theorem analyticPolynomialGermHom_det [Fintype κ] [DecidableEq κ]
    (x : E) (A : Matrix κ κ (MvPolynomial σ (AnalyticGermAt x)))
    (F : E → Matrix κ κ (MvPolynomial σ ℝ))
    (hF : ∀ i j, analyticPolynomialGermHom x (A i j) =
      ((fun w => F w i j) : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    analyticPolynomialGermHom x A.det =
      ((fun w => (F w).det) : Germ (𝓝 x) (MvPolynomial σ ℝ)) :=
  map_det_eq_germ_of_representatives (𝓝 x)
    (analyticPolynomialGermHom x) A F hF

/-- The formal squared-minor denominator is represented by the pointwise
squared-minor polynomial of the supplied matrix representatives. -/
theorem analyticPolynomialGermHom_sumSquaresColumnMinors
    [Fintype ι] {n : ℕ} (x : E)
    (A : Matrix (Fin n) ι (MvPolynomial σ (AnalyticGermAt x)))
    (F : E → Matrix (Fin n) ι (MvPolynomial σ ℝ))
    (hF : ∀ i j, analyticPolynomialGermHom x (A i j) =
      ((fun w => F w i j) : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    analyticPolynomialGermHom x (sumSquaresColumnMinors A) =
      ((fun w => sumSquaresColumnMinors (F w)) :
        Germ (𝓝 x) (MvPolynomial σ ℝ)) :=
  map_sumSquaresColumnMinors_eq_germ_of_representatives (𝓝 x)
    (analyticPolynomialGermHom x) A F hF

/-- Any separately chosen representative of the formal denominator agrees
eventually as a literal polynomial with the pointwise squared-minor sum. -/
theorem analyticPolynomialMinorDenominator_eventually_eq
    [Fintype ι] {n : ℕ} (x : E)
    (A : Matrix (Fin n) ι (MvPolynomial σ (AnalyticGermAt x)))
    (F : E → Matrix (Fin n) ι (MvPolynomial σ ℝ))
    (D : E → MvPolynomial σ ℝ)
    (hF : ∀ i j, analyticPolynomialGermHom x (A i j) =
      ((fun w => F w i j) : Germ (𝓝 x) (MvPolynomial σ ℝ)))
    (hD : analyticPolynomialGermHom x (sumSquaresColumnMinors A) =
      (D : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    D =ᶠ[𝓝 x] (fun w => sumSquaresColumnMinors (F w)) :=
  Germ.coe_eq.mp (hD.symm.trans
    (analyticPolynomialGermHom_sumSquaresColumnMinors x A F hF))

/-- On one open neighborhood the denominator identity holds for every
assignment of the independent symbols. The neighborhood does not depend on
the symbol values, which need not be bounded. -/
theorem exists_open_analyticPolynomialMinorDenominator_forall_eval
    [Fintype ι] {n : ℕ} (x : E)
    (A : Matrix (Fin n) ι (MvPolynomial σ (AnalyticGermAt x)))
    (F : E → Matrix (Fin n) ι (MvPolynomial σ ℝ))
    (D : E → MvPolynomial σ ℝ)
    (hF : ∀ i j, analyticPolynomialGermHom x (A i j) =
      ((fun w => F w i j) : Germ (𝓝 x) (MvPolynomial σ ℝ)))
    (hD : analyticPolynomialGermHom x (sumSquaresColumnMinors A) =
      (D : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      (∀ w ∈ U, D w = sumSquaresColumnMinors (F w)) ∧
      ∀ w ∈ U, ∀ z : σ → ℝ,
        MvPolynomial.eval z (D w) =
          sumSquaresColumnMinors ((F w).map (MvPolynomial.eval z)) := by
  have hlocal := analyticPolynomialMinorDenominator_eventually_eq x A F D hF hD
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp hlocal
  refine ⟨U, hUopen, hxU, hU, ?_⟩
  intro w hw z
  rw [hU w hw]
  exact eval_sumSquaresColumnMinors z (F w)

end AnalyticPolynomialMatrixRepresentatives

end AbelFormalization
