import AbelFormalization.HermiteLemma
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Reality of Abel--Hermite coefficients at real nodes

The contour construction has complex codomain because the node tuple is
allowed to be complex.  On a tuple obtained from real nodes, however, its
coefficients are real.  The argument uses only the analytic and real-axis
agreement fields already present in `AbelHermiteFamilySpec`:

* the jets of the shifted extension at a real node are real;
* coefficientwise conjugation therefore gives a second polynomial with the
  same grouped Hermite jets;
* uniqueness below `totalMultiplicity m` fixes the polynomial under
  conjugation, hence fixes every normalized coefficient.

The final cast equality is the bridge needed to replace the real-part source
coordinate in `RealTransferJetSubstitution` by the unsplit complex coefficient
from the Hermite lemma.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Metric Polynomial Set
open scoped ComplexConjugate Topology

variable {ι : Type*} [Fintype ι]

/-! ## Generic analytic and polynomial lemmas -/

/-- Conjugating every coefficient of a polynomial conjugates each formal jet
at a real argument. -/
theorem iteratedDeriv_polynomial_map_conj_eval_ofReal
    (P : ℂ[X]) (r : ℕ) (x : ℝ) :
    iteratedDeriv r
        (fun z => (P.map (starRingEnd ℂ)).eval z) (x : ℂ) =
      conj (iteratedDeriv r (fun z => P.eval z) (x : ℂ)) := by
  rw [iteratedDeriv_polynomial_eval, iteratedDeriv_polynomial_eval,
    Polynomial.iterate_derivative_map]
  have h := Polynomial.eval_map_apply
    (p := Polynomial.derivative^[r] P)
    (f := starRingEnd ℂ) (x := (x : ℂ))
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal] at h
  exact h

/-- A holomorphic function that is real on the real diameter of a disk has
real iterated derivatives at every real point of that disk. -/
theorem iteratedDeriv_im_eq_zero_of_real_axis
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ ball (0 : ℂ) R →
      (f (x : ℂ)).im = 0)
    {x : ℝ} (hx : (x : ℂ) ∈ ball (0 : ℂ) R) (r : ℕ) :
    (iteratedDeriv r f (x : ℂ)).im = 0 := by
  have hg : AnalyticAt ℝ (fun y : ℝ => (f (y : ℂ)).re) x :=
    (hf (x : ℂ) hx).re_ofReal
  have hmem : ∀ᶠ y : ℝ in 𝓝 x,
      (y : ℂ) ∈ ball (0 : ℂ) R :=
    Complex.continuous_ofReal.continuousAt.tendsto.eventually
      (isOpen_ball.mem_nhds hx)
  have he : (fun y : ℝ => f (y : ℂ)) =ᶠ[𝓝 x]
      fun y => ((f (y : ℂ)).re : ℂ) := by
    filter_upwards [hmem] with y hy
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hreal y hy
  rw [iteratedDeriv_complex_extension hg (hf (x : ℂ) hx) he r]
  exact Complex.ofReal_im _

/-- For real interpolation nodes and real data on the real diameter, the
contour Hermite polynomial is fixed by coefficientwise conjugation. -/
theorem hermiteContourPolynomial_map_conj_eq_of_real_nodes
    {f : ℂ → ℂ} (δ : ι → ℝ) (m : ι → ℕ)
    {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, (δ i : ℂ) ∈ ball (0 : ℂ) R)
    (hd : 0 < totalMultiplicity m)
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ ball (0 : ℂ) R →
      (f (x : ℂ)).im = 0) :
    (hermiteContourPolynomial f
        (nodePolynomial (fun i => (δ i : ℂ)) m) R).map
          (starRingEnd ℂ) =
      hermiteContourPolynomial f
        (nodePolynomial (fun i => (δ i : ℂ)) m) R := by
  let δc : ι → ℂ := fun i => (δ i : ℂ)
  let P : ℂ[X] :=
    hermiteContourPolynomial f (nodePolynomial δc m) R
  change P.map (starRingEnd ℂ) = P
  have hPdegree : P.degree < (totalMultiplicity m : WithBot ℕ) := by
    simpa only [P] using hermiteContour_node_degree_lt f δc m R
  have hPcdegree :
      (P.map (starRingEnd ℂ)).degree <
        (totalMultiplicity m : WithBot ℕ) := by
    simpa only [Polynomial.degree_map] using hPdegree
  apply polynomial_eq_of_grouped_jets δc m hPcdegree hPdegree
  intro ξ r hr
  obtain ⟨i, hi, _⟩ := (nodeMultiplicity_pos_iff δc m ξ).mp
    ((Nat.zero_le r).trans_lt hr)
  have hξ : ξ = (δ i : ℂ) := by
    simpa only [δc] using hi.symm
  subst ξ
  rw [iteratedDeriv_polynomial_map_conj_eval_ofReal]
  have hinterp := hermiteContour_interpolates_combined δc m hR hf hδ hd hr
  change iteratedDeriv r f (δ i : ℂ) =
    iteratedDeriv r (fun z => P.eval z) (δ i : ℂ) at hinterp
  rw [← hinterp]
  exact Complex.conj_eq_iff_im.mpr
    (iteratedDeriv_im_eq_zero_of_real_axis
      (hf.mono ball_subset_closedBall) hreal (hδ i) r)

/-- Every factorial-normalized contour coefficient is real under the same
hypotheses. -/
theorem normalizedCoeff_im_eq_zero_of_real_nodes
    {f : ℂ → ℂ} (δ : ι → ℝ) (m : ι → ℕ)
    {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, (δ i : ℂ) ∈ ball (0 : ℂ) R)
    (hd : 0 < totalMultiplicity m)
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ ball (0 : ℂ) R →
      (f (x : ℂ)).im = 0) (j : ℕ) :
    (normalizedCoeff
      (hermiteContourPolynomial f
        (nodePolynomial (fun i => (δ i : ℂ)) m) R) j).im = 0 := by
  let P : ℂ[X] := hermiteContourPolynomial f
    (nodePolynomial (fun i => (δ i : ℂ)) m) R
  have hP := hermiteContourPolynomial_map_conj_eq_of_real_nodes
    δ m hR hf hδ hd hreal
  have hcoeff : conj (P.coeff j) = P.coeff j := by
    have h := congrArg (fun Q : ℂ[X] => Q.coeff j) hP
    rw [Polynomial.coeff_map] at h
    change conj (P.coeff j) = P.coeff j at h
    exact h
  have hcoeffIm : (P.coeff j).im = 0 :=
    Complex.conj_eq_iff_im.mp hcoeff
  simp [normalizedCoeff, P, Complex.mul_im, hcoeffIm]

/-! ## The coefficient-reality bridge -/

/-- On a real node tuple, every relevant Abel--Hermite coefficient has zero
imaginary part.  `hB` is the radius positivity already available at every
construction of `AbelHermiteFamilySpec`; no extra analytic hypothesis is
needed. -/
theorem AbelHermiteFamilySpec.abelHermiteCoeff_im_eq_zero_of_real_nodes
    {A : ℝ → ℝ} {B : ℝ} {m : ι → ℕ}
    {X0 K K0 : ℝ} {branch : ℝ → ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B m X0 K K0 branch)
    (hB : 0 < B) {x : ℝ} (hx : X0 < x) (δ : ι → ℝ)
    (hδ : (fun i => (δ i : ℂ)) ∈ hermiteNodeNeighborhood B)
    {j : ℕ} (hj : j < totalMultiplicity m) :
    (abelHermiteCoeff branch B m x
      (fun i => (δ i : ℂ)) j).im = 0 := by
  have hnodes : ∀ i, (δ i : ℂ) ∈ ball (0 : ℂ) (B + 1) := by
    intro i
    have hi : ‖(δ i : ℂ)‖ < B + 1 / 4 := hδ i
    simp only [mem_ball, dist_zero_right]
    linarith
  have hreal : ∀ t : ℝ,
      (t : ℂ) ∈ ball (0 : ℂ) (B + 1) →
      (shiftedAbelExtension branch x (t : ℂ)).im = 0 := by
    intro t ht
    have ht' : |t| ≤ B + 1 := by
      have hn : ‖(t : ℂ)‖ < B + 1 := by
        simpa only [mem_ball, dist_zero_right] using ht
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hn.le
    rw [H.shifted_realAgreement x hx t ht']
    exact Complex.ofReal_im _
  have hd : 0 < totalMultiplicity m := (Nat.zero_le j).trans_lt hj
  simpa only [abelHermiteCoeff, abelHermitePolynomial] using
    (normalizedCoeff_im_eq_zero_of_real_nodes δ m
      (by linarith : 0 < B + 1) (H.shifted_analytic x hx)
      hnodes hd hreal j)

/-- Exact cast form used by the real transfer wrapper: the real part is the
original, unsplit Abel--Hermite coefficient at a real node tuple. -/
theorem AbelHermiteFamilySpec.ofReal_re_abelHermiteCoeff_eq_of_real_nodes
    {A : ℝ → ℝ} {B : ℝ} {m : ι → ℕ}
    {X0 K K0 : ℝ} {branch : ℝ → ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B m X0 K K0 branch)
    (hB : 0 < B) {x : ℝ} (hx : X0 < x) (δ : ι → ℝ)
    (hδ : (fun i => (δ i : ℂ)) ∈ hermiteNodeNeighborhood B)
    {j : ℕ} (hj : j < totalMultiplicity m) :
    ((abelHermiteCoeff branch B m x
        (fun i => (δ i : ℂ)) j).re : ℂ) =
      abelHermiteCoeff branch B m x
        (fun i => (δ i : ℂ)) j := by
  apply Complex.conj_eq_iff_re.mp
  apply Complex.conj_eq_iff_im.mpr
  exact H.abelHermiteCoeff_im_eq_zero_of_real_nodes hB hx δ hδ hj

/-- The exact specialization needed for a positive Hermite source-jet block
at the central scale. -/
theorem FullHermiteLemmaSpec.ofReal_re_abelHermiteCoeff_eq_of_real_nodes
    {A : ℝ → ℝ} {B : ℝ} {m : ι → ℕ}
    {X0 K K0 u0 ε Kr : ℝ}
    {branch : ℝ → ℂ → ℂ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B m X0 K K0 u0 ε Kr branch F)
    (hB : 0 < B) (d : ℕ) (hd : d + 1 = totalMultiplicity m)
    {u : ℝ} (hu : u0 < u) (δ : ι → ℝ)
    (hδ : (fun i => (δ i : ℂ)) ∈ hermiteNodeNeighborhood B)
    (r : Fin d) :
    ((abelHermiteCoeff branch B m (E u)
        (fun i => (δ i : ℂ)) (r.val + 1)).re : ℂ) =
      abelHermiteCoeff branch B m (E u)
        (fun i => (δ i : ℂ)) (r.val + 1) := by
  apply H.family.ofReal_re_abelHermiteCoeff_eq_of_real_nodes hB
  · exact H.threshold_compatible.trans (E_strictMono hu)
  · exact hδ
  · omega

end AbelFormalization
