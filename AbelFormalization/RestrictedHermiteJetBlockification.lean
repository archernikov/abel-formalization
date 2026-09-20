import AbelFormalization.PaperRankClusterCurrying
import AbelFormalization.HermiteCoefficientReality
import AbelFormalization.RestrictedBasePaperRankElimination

set_option autoImplicit false

/-!
# Hermite polynomialization of retained paper-rank jets

This module fills the analytic step immediately before cluster currying.  A
finite selected jet list determines one finite Hermite node type, padded by a
zero node of multiplicity two.  Every selected shifted Abel jet is then an
explicit polynomial in the time and positive Hermite-coefficient variables of
its representative block.  The coefficients are the original analytic offset
representatives, so the same polynomials map canonically to analytic germs.
-/

noncomputable section

namespace AbelFormalization

open Filter Metric Set
open scoped Topology

universe u v w

variable {ι : Type*}

/-- Largest derivative order occurring in a finite selected jet list. -/
def paperRankHermiteOrderBound (S : Finset (ι × ℕ)) : ℕ :=
  S.sup Prod.snd

/-- A common multiplicity for every selected node, together with a synthetic
zero node of multiplicity two.  Repeated labels or equal offsets are harmless:
`nodeMultiplicity` combines their multiplicities. -/
def paperRankHermiteNodeMultiplicity (S : Finset (ι × ℕ)) :
    Option (Fin S.card) → ℕ
  | none => 2
  | some _ => paperRankHermiteOrderBound S + 1

/-- Total number of Hermite coefficients in the common padded family. -/
abbrev paperRankHermiteCoefficientCount (S : Finset (ι × ℕ)) : ℕ :=
  totalMultiplicity (paperRankHermiteNodeMultiplicity S)

/-- Number of positive-order Hermite coefficients in each representative
block.  Coefficient zero is represented by the separate time variable. -/
abbrev paperRankHermitePositiveDerivativeCount
    (S : Finset (ι × ℕ)) : ℕ :=
  paperRankHermiteCoefficientCount S - 1

theorem paperRankHermiteCoefficientCount_pos (S : Finset (ι × ℕ)) :
    0 < paperRankHermiteCoefficientCount S := by
  classical
  unfold paperRankHermiteCoefficientCount totalMultiplicity
  have hle : paperRankHermiteNodeMultiplicity S none ≤
      ∑ i : Option (Fin S.card), paperRankHermiteNodeMultiplicity S i := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (none : Option (Fin S.card)))
  have hpos : 0 < paperRankHermiteNodeMultiplicity S none := by
    simp [paperRankHermiteNodeMultiplicity]
  exact hpos.trans_le hle

theorem paperRankHermitePositiveDerivativeCount_add_one
    (S : Finset (ι × ℕ)) :
    paperRankHermitePositiveDerivativeCount S + 1 =
      paperRankHermiteCoefficientCount S := by
  exact Nat.sub_add_cancel
    (paperRankHermiteCoefficientCount_pos S)

theorem restrictedJetEnumeration_order_le_paperRankHermiteOrderBound
    (S : Finset (ι × ℕ)) (j : Fin S.card) :
    (restrictedJetEnumeration S j).2 ≤ paperRankHermiteOrderBound S := by
  classical
  apply Finset.le_sup
  exact (S.equivFin.symm j).2

theorem restrictedJetEnumeration_order_lt_paperRankHermiteNodeMultiplicity
    (S : Finset (ι × ℕ)) (j : Fin S.card) :
    (restrictedJetEnumeration S j).2 <
      paperRankHermiteNodeMultiplicity S (some j) := by
  simpa [paperRankHermiteNodeMultiplicity] using
    restrictedJetEnumeration_order_le_paperRankHermiteOrderBound S j

/-- The real Hermite nodes belonging to one representative block.  Selected
coordinates represented by another block are placed at zero; they only adjoin
unused coefficients and cannot invalidate interpolation. -/
def paperRankHermiteNodes
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (block : Fin m)
    (w : RestrictedBoxSpace p) : Option (Fin S.card) → ℝ
  | none => 0
  | some j =>
      if representative (restrictedJetEnumeration S j).1 = block then
        (offset (restrictedJetEnumeration S j).1 :
          RestrictedBoxSpace p → ℝ) w
      else 0

@[simp]
theorem paperRankHermiteNodes_none
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (block : Fin m)
    (w : RestrictedBoxSpace p) :
    paperRankHermiteNodes D representative offset S block w none = 0 :=
  rfl

@[simp]
theorem paperRankHermiteNodes_selected
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (j : Fin S.card)
    (w : RestrictedBoxSpace p) :
    paperRankHermiteNodes D representative offset S
        (representative (restrictedJetEnumeration S j).1) w (some j) =
      (offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w := by
  simp [paperRankHermiteNodes]

/-- The formal coefficient `a_j` in one split Hermite block.  `a_0` is its
time variable and `a_{r+1}` is its `r`th positive coefficient variable. -/
def splitClusterHermiteCoefficientVariable
    (R : Type u) [CommSemiring R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) :
    Fin (Sum.elim dActive dCoeff block + 1) →
      MvPolynomial
        (SplitClusterBlockSymbol Active Coeff dActive dCoeff) R :=
  Fin.cases
    (MvPolynomial.X (Sum.inr (Sum.inr block)))
    (fun r => MvPolynomial.X (Sum.inr (Sum.inl ⟨block, r⟩)))

@[simp]
theorem splitClusterHermiteCoefficientVariable_zero
    (R : Type u) [CommSemiring R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) :
    splitClusterHermiteCoefficientVariable R dActive dCoeff block 0 =
      MvPolynomial.X (Sum.inr (Sum.inr block)) :=
  rfl

@[simp]
theorem splitClusterHermiteCoefficientVariable_succ
    (R : Type u) [CommSemiring R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff)
    (r : Fin (Sum.elim dActive dCoeff block)) :
    splitClusterHermiteCoefficientVariable R dActive dCoeff block r.succ =
      MvPolynomial.X (Sum.inr (Sum.inl ⟨block, r⟩)) :=
  rfl

/-- Nat-indexed wrapper, equal to zero outside the available coefficient
range.  This keeps finite sums independent of proof terms. -/
def splitClusterHermiteCoefficientVariableNat
    (R : Type u) [CommSemiring R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) (j : ℕ) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff dActive dCoeff) R :=
  if hj : j < Sum.elim dActive dCoeff block + 1 then
    splitClusterHermiteCoefficientVariable R dActive dCoeff block ⟨j, hj⟩
  else 0

theorem splitClusterHermiteCoefficientVariableNat_of_lt
    (R : Type u) [CommSemiring R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) {j : ℕ}
    (hj : j < Sum.elim dActive dCoeff block + 1) :
    splitClusterHermiteCoefficientVariableNat R dActive dCoeff block j =
      splitClusterHermiteCoefficientVariable R dActive dCoeff block ⟨j, hj⟩ := by
  simp only [splitClusterHermiteCoefficientVariableNat, dif_pos hj]

@[simp]
theorem map_splitClusterHermiteCoefficientVariable
    {R : Type u} {T : Type*} [CommSemiring R] [CommSemiring T]
    {Active : Type v} {Coeff : Type w}
    (f : R →+* T) (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff)
    (j : Fin (Sum.elim dActive dCoeff block + 1)) :
    MvPolynomial.map f
        (splitClusterHermiteCoefficientVariable R dActive dCoeff block j) =
      splitClusterHermiteCoefficientVariable T dActive dCoeff block j := by
  refine Fin.cases ?_ (fun r => ?_) j <;>
    simp [splitClusterHermiteCoefficientVariable]

@[simp]
theorem map_splitClusterHermiteCoefficientVariableNat
    {R : Type u} {T : Type*} [CommSemiring R] [CommSemiring T]
    {Active : Type v} {Coeff : Type w}
    (f : R →+* T) (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) (j : ℕ) :
    MvPolynomial.map f
        (splitClusterHermiteCoefficientVariableNat R dActive dCoeff block j) =
      splitClusterHermiteCoefficientVariableNat T dActive dCoeff block j := by
  unfold splitClusterHermiteCoefficientVariableNat
  split_ifs with hj
  · exact map_splitClusterHermiteCoefficientVariable
      f dActive dCoeff block ⟨j, hj⟩
  · simp

/-- Evaluate the representative argument and the Hermite coefficient list in
each block. -/
def splitClusterHermiteBlockValue
    {T : Type*}
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (argument : Active ⊕ Coeff → T)
    (coefficient : ∀ block : Active ⊕ Coeff,
      Fin (Sum.elim dActive dCoeff block + 1) → T) :
    SplitClusterBlockSymbol Active Coeff dActive dCoeff → T
  | Sum.inl block => argument block
  | Sum.inr (Sum.inl ⟨block, r⟩) => coefficient block r.succ
  | Sum.inr (Sum.inr block) => coefficient block 0

/-- Nat-indexed numerical coefficient, padded by zero outside its block. -/
def splitClusterHermiteCoefficientValueNat
    {T : Type*} [Zero T]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (coefficient : ∀ block : Active ⊕ Coeff,
      Fin (Sum.elim dActive dCoeff block + 1) → T)
    (block : Active ⊕ Coeff) (j : ℕ) : T :=
  if hj : j < Sum.elim dActive dCoeff block + 1 then
    coefficient block ⟨j, hj⟩
  else 0

theorem splitClusterHermiteCoefficientValueNat_of_lt
    {T : Type*} [Zero T]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (coefficient : ∀ block : Active ⊕ Coeff,
      Fin (Sum.elim dActive dCoeff block + 1) → T)
    (block : Active ⊕ Coeff) {j : ℕ}
    (hj : j < Sum.elim dActive dCoeff block + 1) :
    splitClusterHermiteCoefficientValueNat dActive dCoeff coefficient block j =
      coefficient block ⟨j, hj⟩ := by
  simp only [splitClusterHermiteCoefficientValueNat, dif_pos hj]

@[simp]
theorem eval₂Hom_splitClusterHermiteCoefficientVariable
    {R : Type u} {T : Type*} [CommSemiring R] [CommSemiring T]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (argument : Active ⊕ Coeff → T)
    (coefficient : ∀ block : Active ⊕ Coeff,
      Fin (Sum.elim dActive dCoeff block + 1) → T)
    (c : R →+* T) (block : Active ⊕ Coeff)
    (j : Fin (Sum.elim dActive dCoeff block + 1)) :
    MvPolynomial.eval₂Hom c
        (splitClusterHermiteBlockValue dActive dCoeff argument coefficient)
        (splitClusterHermiteCoefficientVariable R dActive dCoeff block j) =
      coefficient block j := by
  refine Fin.cases ?_ (fun r => ?_) j <;>
    simp [splitClusterHermiteCoefficientVariable,
      splitClusterHermiteBlockValue]

@[simp]
theorem eval₂Hom_splitClusterHermiteCoefficientVariableNat_of_lt
    {R : Type u} {T : Type*} [CommSemiring R] [CommSemiring T]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (argument : Active ⊕ Coeff → T)
    (coefficient : ∀ block : Active ⊕ Coeff,
      Fin (Sum.elim dActive dCoeff block + 1) → T)
    (c : R →+* T) (block : Active ⊕ Coeff) {j : ℕ}
    (hj : j < Sum.elim dActive dCoeff block + 1) :
    MvPolynomial.eval₂Hom c
        (splitClusterHermiteBlockValue dActive dCoeff argument coefficient)
        (splitClusterHermiteCoefficientVariableNat R dActive dCoeff block j) =
      coefficient block ⟨j, hj⟩ := by
  rw [splitClusterHermiteCoefficientVariableNat_of_lt R dActive dCoeff block hj]
  exact eval₂Hom_splitClusterHermiteCoefficientVariable
    dActive dCoeff argument coefficient c block ⟨j, hj⟩

/-- The manuscript polynomial
`sum_{j=r}^{d} a_j δ^(j-r)/(j-r)!` in one split block. -/
def splitClusterHermiteJetPolynomial
    (R : Type u) [CommRing R] [Algebra ℝ R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) (offsetCoefficient : R) (r : ℕ) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff dActive dCoeff) R := by
  classical
  exact ∑ j ∈ Finset.Ico r (Sum.elim dActive dCoeff block + 1),
    MvPolynomial.C
        (offsetCoefficient ^ (j - r) *
          algebraMap ℝ R (((j - r).factorial : ℝ)⁻¹)) *
      splitClusterHermiteCoefficientVariableNat R dActive dCoeff block j

/-- Direct evaluation of the formal Hermite jet polynomial. -/
theorem eval₂Hom_splitClusterHermiteJetPolynomial
    {R : Type u} {T : Type*} [CommRing R] [CommRing T]
    [Algebra ℝ R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) (offsetCoefficient : R) (r : ℕ)
    (c : R →+* T)
    (value : SplitClusterBlockSymbol Active Coeff dActive dCoeff → T) :
    MvPolynomial.eval₂Hom c value
        (splitClusterHermiteJetPolynomial R dActive dCoeff block
          offsetCoefficient r) =
      ∑ j ∈ Finset.Ico r (Sum.elim dActive dCoeff block + 1),
        (c offsetCoefficient) ^ (j - r) *
          c (algebraMap ℝ R (((j - r).factorial : ℝ)⁻¹)) *
          MvPolynomial.eval₂Hom c value
            (splitClusterHermiteCoefficientVariableNat R dActive dCoeff
              block j) := by
  classical
  simp [splitClusterHermiteJetPolynomial, mul_assoc]

/-- Evaluation against a block coefficient list is the numerical Hermite
sum with the same normalization. -/
theorem eval₂Hom_splitClusterHermiteJetPolynomial_blockValue
    {R : Type u} {T : Type*} [CommRing R] [CommRing T]
    [Algebra ℝ R]
    {Active : Type v} {Coeff : Type w}
    (dActive : Active → ℕ) (dCoeff : Coeff → ℕ)
    (block : Active ⊕ Coeff) (offsetCoefficient : R) (r : ℕ)
    (c : R →+* T) (argument : Active ⊕ Coeff → T)
    (coefficient : ∀ block : Active ⊕ Coeff,
      Fin (Sum.elim dActive dCoeff block + 1) → T) :
    MvPolynomial.eval₂Hom c
        (splitClusterHermiteBlockValue dActive dCoeff argument coefficient)
        (splitClusterHermiteJetPolynomial R dActive dCoeff block
          offsetCoefficient r) =
      ∑ j ∈ Finset.Ico r (Sum.elim dActive dCoeff block + 1),
        (c offsetCoefficient) ^ (j - r) *
          c (algebraMap ℝ R (((j - r).factorial : ℝ)⁻¹)) *
          splitClusterHermiteCoefficientValueNat dActive dCoeff coefficient
            block j := by
  classical
  rw [eval₂Hom_splitClusterHermiteJetPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).2
  rw [eval₂Hom_splitClusterHermiteCoefficientVariableNat_of_lt
    dActive dCoeff argument coefficient c block hj']
  rw [splitClusterHermiteCoefficientValueNat_of_lt
    dActive dCoeff coefficient block hj']

/-! ## Exact real-axis Hermite evaluation -/

/-- The shifted complex branch has the real Abel jet at every real offset in
the closed node range.  This follows from the analytic and real-agreement
fields already present in `AbelHermiteFamilySpec`. -/
theorem AbelHermiteFamilySpec.shifted_iteratedDeriv_realAgreement
    {Node : Type*} [Fintype Node]
    {A : ℝ → ℝ} {B : ℝ} {multiplicity : Node → ℕ}
    {X0 K K0 : ℝ} {branch : ℝ → ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B multiplicity X0 K K0 branch)
    {x t : ℝ} (hx : X0 < x) (ht : |t| ≤ B) (r : ℕ) :
    iteratedDeriv r (shiftedAbelExtension branch x) (t : ℂ) =
      ((iteratedDeriv r A (x + t) : ℝ) : ℂ) := by
  have htBall : (t : ℂ) ∈ ball (0 : ℂ) (B + 1) := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs] using (lt_of_le_of_lt ht (by linarith : B < B + 1))
  have hF : AnalyticAt ℂ (shiftedAbelExtension branch x) (t : ℂ) :=
    H.shifted_analytic x hx (t : ℂ) (Metric.ball_subset_closedBall htBall)
  have hnear : ∀ᶠ y : ℝ in 𝓝 t, (y : ℂ) ∈ ball (0 : ℂ) (B + 1) :=
    Complex.continuous_ofReal.continuousAt.tendsto.eventually
      (isOpen_ball.mem_nhds htBall)
  have he : (fun y : ℝ => shiftedAbelExtension branch x (y : ℂ)) =ᶠ[𝓝 t]
      fun y => (A (x + y) : ℂ) := by
    filter_upwards [hnear] with y hy
    apply H.shifted_realAgreement x hx y
    have hy' : ‖(y : ℂ)‖ < B + 1 := by
      simpa only [mem_ball, dist_zero_right] using hy
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hy'.le
  have hfRe : AnalyticAt ℝ
      (fun y : ℝ => (shiftedAbelExtension branch x (y : ℂ)).re) t :=
    hF.re_ofReal
  have heRe : (fun y : ℝ => (shiftedAbelExtension branch x (y : ℂ)).re) =ᶠ[𝓝 t]
      fun y => A (x + y) := by
    filter_upwards [he] with y hy
    rw [hy]
    simp
  have hf : AnalyticAt ℝ (fun y : ℝ => A (x + y)) t :=
    hfRe.congr heRe
  calc
    iteratedDeriv r (shiftedAbelExtension branch x) (t : ℂ) =
        ((iteratedDeriv r (fun y : ℝ => A (x + y)) t : ℝ) : ℂ) :=
      iteratedDeriv_complex_extension hf hF he r
    _ = ((iteratedDeriv r A (x + t) : ℝ) : ℂ) := by
      rw [congrFun (iteratedDeriv_comp_const_add r A x) t]

/-! ## The finite retained-rank jet family -/

/-- Every block is padded to the same positive-derivative count. -/
abbrev paperRankHermiteBlockDerivativeCount
    (S : Finset (ι × ℕ)) (Block : Type*) : Block → ℕ :=
  fun _ => paperRankHermitePositiveDerivativeCount S

@[simp]
theorem sum_elim_paperRankHermiteBlockDerivativeCount
    (S : Finset (ι × ℕ)) (Active : Type v) (Coeff : Type w)
    (block : Active ⊕ Coeff) :
    Sum.elim (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff) block =
      paperRankHermitePositiveDerivativeCount S := by
  rcases block with a | c <;> rfl

/-- The explicit Hermite polynomial for one coordinate of the canonical
selected jet enumeration, with analytic-near-box coefficients. -/
def paperRankHermiteJetPolynomial
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (j : Fin S.card) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff))
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) :=
  splitClusterHermiteJetPolynomial
    (RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    (blockEquiv
      (representative (restrictedJetEnumeration S j).1))
    (offset (restrictedJetEnumeration S j).1)
    (restrictedJetEnumeration S j).2

/-- The same canonical Hermite jet polynomial over the coefficient-germ
ring used by rank elimination. -/
def paperRankHermiteGermJetPolynomial
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (j : Fin S.card) :
    MvPolynomial
      (SplitClusterBlockSymbol Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff))
      (RealAnalyticGerm p) :=
  MvPolynomial.map (restrictedAnalyticCoefficientGermHom D h0D)
    (paperRankHermiteJetPolynomial D representative offset S
      Active Coeff blockEquiv j)

@[simp]
theorem restrictedAnalyticCoefficientGermHom_algebraMap
    {p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox) (r : ℝ) :
    restrictedAnalyticCoefficientGermHom D h0D
        (algebraMap ℝ (RestrictedBox.analyticNearClosedBoxSubalgebra D) r) =
      algebraMap ℝ (RealAnalyticGerm p) r := by
  apply Subtype.ext
  rfl

/-- Mapping the analytic representative polynomial to germs changes only its
offset coefficient; its block variables and Hermite normalization are
unchanged. -/
theorem paperRankHermiteGermJetPolynomial_eq
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (j : Fin S.card) :
    paperRankHermiteGermJetPolynomial D h0D representative offset S
        Active Coeff blockEquiv j =
      splitClusterHermiteJetPolynomial (RealAnalyticGerm p)
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)
        (blockEquiv
          (representative (restrictedJetEnumeration S j).1))
        (restrictedAnalyticCoefficientGermHom D h0D
          (offset (restrictedJetEnumeration S j).1))
        (restrictedJetEnumeration S j).2 := by
  classical
  unfold paperRankHermiteGermJetPolynomial paperRankHermiteJetPolynomial
    splitClusterHermiteJetPolynomial
  simp only [map_sum, map_mul, map_pow, MvPolynomial.map_C,
    map_splitClusterHermiteCoefficientVariableNat,
    restrictedAnalyticCoefficientGermHom_algebraMap]

/-- The actual Hermite coefficient list at one real paper-rank parameter. -/
def paperRankHermiteCoefficientValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (B : ℝ) (branch : ℝ → ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (block : Active ⊕ Coeff) :
    Fin (Sum.elim
      (paperRankHermiteBlockDerivativeCount S Active)
      (paperRankHermiteBlockDerivativeCount S Coeff) block + 1) → ℝ :=
  fun j =>
    (abelHermiteCoeff branch B (paperRankHermiteNodeMultiplicity S)
      (sw.1 (blockEquiv.symm block))
      (fun node =>
        (paperRankHermiteNodes D representative offset S
          (blockEquiv.symm block) sw.2 node : ℂ)) j).re

/-- The flat evaluation of all representative, time, and positive Hermite
coefficient variables before cluster currying. -/
def paperRankHermiteSplitValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (B : ℝ) (branch : ℝ → ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) :
    SplitClusterBlockSymbol Active Coeff
      (paperRankHermiteBlockDerivativeCount S Active)
      (paperRankHermiteBlockDerivativeCount S Coeff) → ℝ :=
  splitClusterHermiteBlockValue
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    (fun block => sw.1 (blockEquiv.symm block))
    (paperRankHermiteCoefficientValue D representative offset S
      Active Coeff blockEquiv B branch sw)

/-- Each canonical selected Abel jet is exactly the evaluation of its
explicit Hermite block polynomial. -/
theorem eval₂Hom_paperRankHermiteJetPolynomial
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    {A : ℝ → ℝ} {B X0 K K0 : ℝ} {branch : ℝ → ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B
      (paperRankHermiteNodeMultiplicity S) X0 K K0 branch)
    (hB : 0 < B) (sw : PaperRankParameterSpace m p)
    (hs : ∀ i, X0 < sw.1 i)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) sw.2| ≤ B)
    (j : Fin S.card) :
    MvPolynomial.eval₂Hom
        (subalgebraPointEval
          (RestrictedBox.analyticNearClosedBoxSubalgebra D) sw.2)
        (paperRankHermiteSplitValue D representative offset S
          Active Coeff blockEquiv B branch sw)
        (paperRankHermiteJetPolynomial D representative offset S
          Active Coeff blockEquiv j) =
      restrictedSelectedAbelJets A representative offset
        (restrictedJetEnumeration S) sw j := by
  classical
  let q := restrictedJetEnumeration S j
  let block : Active ⊕ Coeff := blockEquiv (representative q.1)
  let nodes : Option (Fin S.card) → ℝ :=
    paperRankHermiteNodes D representative offset S
      (representative q.1) sw.2
  let nodesC : Option (Fin S.card) → ℂ := fun i => (nodes i : ℂ)
  have hnodesBound : ∀ i, ‖nodesC i‖ ≤ B := by
    intro i
    rcases i with _ | k
    · simpa [nodes, nodesC, paperRankHermiteNodes] using hB.le
    · simp only [nodesC, Complex.norm_real, Real.norm_eq_abs]
      dsimp [nodes, paperRankHermiteNodes]
      split_ifs
      · exact hoffset k
      · simpa using hB.le
  have hnodes : nodesC ∈ hermiteNodeNeighborhood B :=
    H.neighborhood_contains hnodesBound
  have htargetNode : nodes (some j) =
      (offset q.1 : RestrictedBoxSpace p → ℝ) sw.2 := by
    simp [nodes, q, paperRankHermiteNodes]
  have hrMultiplicity : q.2 <
      nodeMultiplicity nodesC (paperRankHermiteNodeMultiplicity S)
        (nodesC (some j)) :=
    (restrictedJetEnumeration_order_lt_paperRankHermiteNodeMultiplicity S j).trans_le
      (multiplicity_le_nodeMultiplicity nodesC
        (paperRankHermiteNodeMultiplicity S) (some j))
  have hHermite := H.combined_jets_explicit
    (sw.1 (representative q.1)) (hs (representative q.1))
    nodesC hnodes (nodesC (some j)) q.2 hrMultiplicity
  have hReal := H.shifted_iteratedDeriv_realAgreement
    (hs (representative q.1)) (hoffset j) q.2
  have hComplex :
      ((iteratedDeriv q.2 A
          (sw.1 (representative q.1) +
            (offset q.1 : RestrictedBoxSpace p → ℝ) sw.2) : ℝ) : ℂ) =
        ∑ k ∈ Finset.Ico q.2 (paperRankHermiteCoefficientCount S),
          abelHermiteCoeff branch B (paperRankHermiteNodeMultiplicity S)
              (sw.1 (representative q.1)) nodesC k *
            ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2 : ℂ) ^
              (k - q.2) /
            ((k - q.2).factorial : ℂ) := by
    calc
      _ = iteratedDeriv q.2 (shiftedAbelExtension branch
            (sw.1 (representative q.1)))
          ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2 : ℂ) := hReal.symm
      _ = iteratedDeriv q.2 (shiftedAbelExtension branch
            (sw.1 (representative q.1))) (nodesC (some j)) := by
          rw [show nodesC (some j) =
            ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2 : ℂ) by
              exact congrArg Complex.ofReal htargetNode]
      _ = _ := by
        simpa [nodesC, htargetNode] using hHermite
  have hSumCast :
      (((∑ k ∈ Finset.Ico q.2 (paperRankHermiteCoefficientCount S),
          ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2) ^ (k - q.2) *
            (((k - q.2).factorial : ℝ)⁻¹) *
            (abelHermiteCoeff branch B (paperRankHermiteNodeMultiplicity S)
              (sw.1 (representative q.1)) nodesC k).re) : ℝ) : ℂ) =
        ∑ k ∈ Finset.Ico q.2 (paperRankHermiteCoefficientCount S),
          abelHermiteCoeff branch B (paperRankHermiteNodeMultiplicity S)
              (sw.1 (representative q.1)) nodesC k *
            ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2 : ℂ) ^
              (k - q.2) /
            ((k - q.2).factorial : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    have hkTotal : k < paperRankHermiteCoefficientCount S :=
      (Finset.mem_Ico.mp hk).2
    rw [H.ofReal_re_abelHermiteCoeff_eq_of_real_nodes hB
      (hs (representative q.1)) nodes hnodes hkTotal]
    push_cast
    field_simp
    <;> ring
  have hRealSum :
      iteratedDeriv q.2 A
          (sw.1 (representative q.1) +
            (offset q.1 : RestrictedBoxSpace p → ℝ) sw.2) =
        ∑ k ∈ Finset.Ico q.2 (paperRankHermiteCoefficientCount S),
          ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2) ^ (k - q.2) *
            (((k - q.2).factorial : ℝ)⁻¹) *
            (abelHermiteCoeff branch B (paperRankHermiteNodeMultiplicity S)
              (sw.1 (representative q.1)) nodesC k).re := by
    exact Complex.ofReal_injective (hComplex.trans hSumCast.symm)
  unfold paperRankHermiteJetPolynomial paperRankHermiteSplitValue
  rw [eval₂Hom_splitClusterHermiteJetPolynomial_blockValue]
  rw [sum_elim_paperRankHermiteBlockDerivativeCount]
  rw [paperRankHermitePositiveDerivativeCount_add_one]
  trans (∑ k ∈ Finset.Ico q.2 (paperRankHermiteCoefficientCount S),
      ((offset q.1 : RestrictedBoxSpace p → ℝ) sw.2) ^ (k - q.2) *
        (((k - q.2).factorial : ℝ)⁻¹) *
        (abelHermiteCoeff branch B (paperRankHermiteNodeMultiplicity S)
          (sw.1 (representative q.1)) nodesC k).re)
  · apply Finset.sum_congr rfl
    intro k hk
    have hkTotal : k < paperRankHermiteCoefficientCount S :=
      (Finset.mem_Ico.mp hk).2
    have hkRange : k < paperRankHermitePositiveDerivativeCount S + 1 := by
      rw [paperRankHermitePositiveDerivativeCount_add_one]
      exact hkTotal
    have hkBlock : k <
        Sum.elim (paperRankHermiteBlockDerivativeCount S Active)
            (paperRankHermiteBlockDerivativeCount S Coeff)
            (blockEquiv
              (representative (restrictedJetEnumeration S j).1)) + 1 := by
      simpa using hkRange
    rw [splitClusterHermiteCoefficientValueNat_of_lt
      (paperRankHermiteBlockDerivativeCount S Active)
      (paperRankHermiteBlockDerivativeCount S Coeff)
      (paperRankHermiteCoefficientValue D representative offset S
        Active Coeff blockEquiv B branch sw)
      (blockEquiv (representative (restrictedJetEnumeration S j).1))
      hkBlock]
    simp [paperRankHermiteCoefficientValue, subalgebraPointEval,
      q, nodesC, nodes]
  · simpa [restrictedSelectedAbelJets, q] using hRealSum.symm

/-! ## Exact compatibility with active/coefficient currying -/

/-- Active-cluster values obtained by restricting the flat Hermite-block
evaluation along the canonical split equivalence. -/
def paperRankHermiteActiveValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (B : ℝ) (branch : ℝ → ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) :
    ClusterOperationSymbol Active
      (paperRankHermiteBlockDerivativeCount S Active) → ℝ :=
  fun z =>
    paperRankHermiteSplitValue D representative offset S Active Coeff
      blockEquiv B branch sw
      ((splitClusterBlockSymbolEquiv Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)).symm (Sum.inl z))

/-- Retained-block values obtained by restricting the same flat evaluation. -/
def paperRankHermiteCoefficientBlockValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (B : ℝ) (branch : ℝ → ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) :
    ClusterOperationSymbol Coeff
      (paperRankHermiteBlockDerivativeCount S Coeff) → ℝ :=
  fun z =>
    paperRankHermiteSplitValue D representative offset S Active Coeff
      blockEquiv B branch sw
      ((splitClusterBlockSymbolEquiv Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)).symm (Sum.inr z))

theorem paperRankHermiteSplitValue_eq_sum_elim
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    (B : ℝ) (branch : ℝ → ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (z : SplitClusterBlockSymbol Active Coeff
      (paperRankHermiteBlockDerivativeCount S Active)
      (paperRankHermiteBlockDerivativeCount S Coeff)) :
    Sum.elim
        (paperRankHermiteActiveValue D representative offset S Active Coeff
          blockEquiv B branch sw)
        (paperRankHermiteCoefficientBlockValue D representative offset S
          Active Coeff blockEquiv B branch sw)
        (splitClusterBlockSymbolEquiv Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff) z) =
      paperRankHermiteSplitValue D representative offset S Active Coeff
        blockEquiv B branch sw z := by
  let e := splitClusterBlockSymbolEquiv Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
  generalize hz : e z = y
  rcases y with a | c
  · change paperRankHermiteSplitValue D representative offset S Active Coeff
      blockEquiv B branch sw (e.symm (Sum.inl a)) = _
    rw [← hz, e.symm_apply_apply]
  · change paperRankHermiteSplitValue D representative offset S Active Coeff
      blockEquiv B branch sw (e.symm (Sum.inr c)) = _
    rw [← hz, e.symm_apply_apply]

/-- Currying the explicit Hermite blockification preserves evaluation of every
retained rank polynomial, with the raw jet coordinates replaced by the actual
`restrictedSelectedAbelJets`. -/
theorem eval₂Hom_paperRankHermiteClusterCurryHom
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    {A : ℝ → ℝ} {B X0 K K0 : ℝ} {branch : ℝ → ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B
      (paperRankHermiteNodeMultiplicity S) X0 K K0 branch)
    (hB : 0 < B) (sw : PaperRankParameterSpace m p)
    (hs : ∀ i, X0 < sw.1 i)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) sw.2| ≤ B)
    (P : MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    MvPolynomial.eval₂Hom
        (subalgebraPointEval
          (RestrictedBox.analyticNearClosedBoxSubalgebra D) sw.2)
        (Sum.elim sw.1
          (restrictedSelectedAbelJets A representative offset
            (restrictedJetEnumeration S) sw)) P =
      MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom
          (subalgebraPointEval
            (RestrictedBox.analyticNearClosedBoxSubalgebra D) sw.2)
          (paperRankHermiteCoefficientBlockValue D representative offset S
            Active Coeff blockEquiv B branch sw))
        (paperRankHermiteActiveValue D representative offset S Active Coeff
          blockEquiv B branch sw)
        (paperRankClusterCurryHom
          (RestrictedBox.analyticNearClosedBoxSubalgebra D)
          Active Coeff
          (paperRankHermiteBlockDerivativeCount S Active)
          (paperRankHermiteBlockDerivativeCount S Coeff)
          blockEquiv
          (paperRankHermiteJetPolynomial D representative offset S
            Active Coeff blockEquiv) P) := by
  let c := subalgebraPointEval
    (RestrictedBox.analyticNearClosedBoxSubalgebra D) sw.2
  let activeValue := paperRankHermiteActiveValue D representative offset S
    Active Coeff blockEquiv B branch sw
  let coefficientValue := paperRankHermiteCoefficientBlockValue D
    representative offset S Active Coeff blockEquiv B branch sw
  let splitValue := paperRankHermiteSplitValue D representative offset S
    Active Coeff blockEquiv B branch sw
  let e := splitClusterBlockSymbolEquiv Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
  have hflat : (fun z => Sum.elim activeValue coefficientValue (e z)) =
      splitValue := by
    funext z
    exact paperRankHermiteSplitValue_eq_sum_elim D representative offset S
      Active Coeff blockEquiv B branch sw z
  have hretained :
      (Sum.elim
        (fun i => Sum.elim activeValue coefficientValue
          (e (Sum.inl (blockEquiv i))))
        (fun j => MvPolynomial.eval₂Hom c
          (fun z => Sum.elim activeValue coefficientValue (e z))
          (paperRankHermiteJetPolynomial D representative offset S
            Active Coeff blockEquiv j))) =
      Sum.elim sw.1
        (restrictedSelectedAbelJets A representative offset
          (restrictedJetEnumeration S) sw) := by
    funext z
    rcases z with i | j
    · calc
        Sum.elim activeValue coefficientValue
            (e (Sum.inl (blockEquiv i))) =
            splitValue (Sum.inl (blockEquiv i)) :=
          congrFun hflat (Sum.inl (blockEquiv i))
        _ = sw.1 i := by
          simp [splitValue, paperRankHermiteSplitValue,
            splitClusterHermiteBlockValue]
    · rw [hflat]
      exact eval₂Hom_paperRankHermiteJetPolynomial D representative offset S
        Active Coeff blockEquiv H hB sw hs hoffset j
  have hCurry := eval₂Hom_paperRankClusterCurryHom c Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    blockEquiv
    (paperRankHermiteJetPolynomial D representative offset S
      Active Coeff blockEquiv)
    activeValue coefficientValue P
  rw [hretained] at hCurry
  exact hCurry

/-! ## Germ-valued currying and generator spans -/

/-- The exact currying homomorphism applied to the coefficient-germ Hermite
polynomials. -/
def paperRankHermiteGermClusterCurryHom
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff) :
    MvPolynomial (PaperRankRetainedSymbols m S.card)
        (RealAnalyticGerm p) →ₐ[RealAnalyticGerm p]
      MvPolynomial
        (ClusterOperationSymbol Active
          (paperRankHermiteBlockDerivativeCount S Active))
        (MvPolynomial
          (ClusterOperationSymbol Coeff
            (paperRankHermiteBlockDerivativeCount S Coeff))
          (RealAnalyticGerm p)) :=
  paperRankClusterCurryHom (RealAnalyticGerm p) Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    blockEquiv
    (paperRankHermiteGermJetPolynomial D h0D representative offset S
      Active Coeff blockEquiv)

/-- A displayed generating family from rank elimination remains a displayed
generating family after the explicit germ-valued Hermite blockification and
cluster currying. -/
theorem span_paperRankHermiteGermClusterCurryHom_eq
    {m p : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff)
    {J : Type*}
    (g : J → MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RealAnalyticGerm p))
    (I : Ideal (MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RealAnalyticGerm p)))
    (hspan : Ideal.span (Set.range g) = I) :
    Ideal.span (Set.range (fun j =>
        paperRankHermiteGermClusterCurryHom D h0D representative offset S
          Active Coeff blockEquiv (g j))) =
      paperRankClusterCurriedIdeal (RealAnalyticGerm p) Active Coeff
        (paperRankHermiteBlockDerivativeCount S Active)
        (paperRankHermiteBlockDerivativeCount S Coeff)
        blockEquiv
        (paperRankHermiteGermJetPolynomial D h0D representative offset S
          Active Coeff blockEquiv) I := by
  exact span_paperRankClusterCurryHom_eq_curriedIdeal
    (RealAnalyticGerm p) Active Coeff
    (paperRankHermiteBlockDerivativeCount S Active)
    (paperRankHermiteBlockDerivativeCount S Coeff)
    blockEquiv
    (paperRankHermiteGermJetPolynomial D h0D representative offset S
      Active Coeff blockEquiv) g I hspan

/-! ## Construction from compactness and the Abel hypotheses -/

/-- The finitely many selected analytic offsets have one positive uniform
absolute-value bound on the closed coefficient box. -/
theorem exists_paperRankHermiteOffsetBound
    {p : ℕ} (D : RestrictedBox p)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) :
    ∃ B : ℝ, 0 < B ∧
      ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
        |(offset (restrictedJetEnumeration S j).1 :
          RestrictedBoxSpace p → ℝ) w| ≤ B := by
  classical
  have hbound : ∀ j : Fin S.card, ∃ C : ℝ,
      ∀ w ∈ D.closedBox,
        |(offset (restrictedJetEnumeration S j).1 :
          RestrictedBoxSpace p → ℝ) w| ≤ C := by
    intro j
    have hcont : ContinuousOn
        (fun w => |(offset (restrictedJetEnumeration S j).1 :
          RestrictedBoxSpace p → ℝ) w|) D.closedBox :=
      (D.analyticNearClosedBox_iff.mp
        (offset (restrictedJetEnumeration S j).1).property).continuousOn.abs
    obtain ⟨C, hC⟩ := D.isCompact_closedBox.bddAbove_image hcont
    refine ⟨C, ?_⟩
    intro w hw
    exact hC ⟨w, hw, rfl⟩
  choose C hC using hbound
  let B : ℝ := 1 + ∑ j : Fin S.card, max (C j) 0
  have hsum : 0 ≤ ∑ j : Fin S.card, max (C j) 0 :=
    Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro w hw j
  have hterm : C j ≤ ∑ k : Fin S.card, max (C k) 0 := by
    calc
      C j ≤ max (C j) 0 := le_max_left _ _
      _ ≤ ∑ k : Fin S.card, max (C k) 0 :=
        Finset.single_le_sum (fun k _ => le_max_right (C k) 0)
          (Finset.mem_univ j)
  exact (hC j w hw).trans (hterm.trans (by dsimp [B]; linarith))

/-- The complete common Hermite family needed for every selected retained
jet exists from `IsAbel`.  The radius is chosen after the finite jet list and
before the representative parameters, as in the manuscript. -/
theorem IsAbel.exists_paperRankHermiteFamily
    {A : ℝ → ℝ} (hA : IsAbel A)
    {p : ℕ} (D : RestrictedBox p)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) :
    ∃ B X0 K K0 : ℝ, ∃ branch : ℝ → ℂ → ℂ,
      0 < B ∧
      (∀ w ∈ D.closedBox, ∀ j : Fin S.card,
        |(offset (restrictedJetEnumeration S j).1 :
          RestrictedBoxSpace p → ℝ) w| ≤ B) ∧
      AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
        X0 K K0 branch := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_paperRankHermiteOffsetBound D offset S
  obtain ⟨X0, K, K0, branch, H⟩ :=
    hA.exists_abelHermiteFamily hB
      (paperRankHermiteNodeMultiplicity S)
      (paperRankHermiteCoefficientCount_pos S)
  exact ⟨B, X0, K, K0, branch, hB, hbound, H⟩

/-- End-to-end construction form of the finite Hermite blockification: the
radius, threshold, complex branch, and coefficient family are constructed,
and every selected coordinate has the explicit polynomial evaluation on the
whole closed coefficient box once its representative arguments exceed the
common threshold. -/
theorem IsAbel.exists_paperRankHermiteJetBlockification
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Active : Type v) (Coeff : Type w)
    (blockEquiv : Fin m ≃ Active ⊕ Coeff) :
    ∃ B X0 K K0 : ℝ, ∃ branch : ℝ → ℂ → ℂ,
      0 < B ∧
      AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
        X0 K K0 branch ∧
      ∀ sw : PaperRankParameterSpace m p,
        sw.2 ∈ D.closedBox →
        (∀ i, X0 < sw.1 i) →
        ∀ j : Fin S.card,
          MvPolynomial.eval₂Hom
              (subalgebraPointEval
                (RestrictedBox.analyticNearClosedBoxSubalgebra D) sw.2)
              (paperRankHermiteSplitValue D representative offset S
                Active Coeff blockEquiv B branch sw)
              (paperRankHermiteJetPolynomial D representative offset S
                Active Coeff blockEquiv j) =
            restrictedSelectedAbelJets A representative offset
              (restrictedJetEnumeration S) sw j := by
  obtain ⟨B, X0, K, K0, branch, hB, hbound, H⟩ :=
    hA.exists_paperRankHermiteFamily D offset S
  refine ⟨B, X0, K, K0, branch, hB, H, ?_⟩
  intro sw hw hs j
  exact eval₂Hom_paperRankHermiteJetPolynomial D representative offset S
    Active Coeff blockEquiv H hB sw hs (hbound sw.2 hw) j

end AbelFormalization
