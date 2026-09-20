import AbelFormalization.CharbonnelSardianRankConstructorReduction

/-!
# A geometric-family-safe radial constituent for Wilkie's literal-zero base

Wilkie's Lemma 3.8 uses a radial escape equation and the positive level
equation `f(x)^2 = ε₂`.  Its displayed radial equation uses a square root,
which need not belong to an arbitrary geometric function family.  The
reciprocal of `1 + ∑ xᵢ² + y²` has the same escape role and belongs to every
geometric family: its denominator is strictly positive and polynomial.

This module constructs the single smooth Sardian constituent and proves its
exact carrier equations, including the elementary hidden-coordinate escape
step.  The two remaining level-control clauses are explicit: small positive
levels of `f²` near the radial bounded region approach `Z(f)`, and every
bounded frontier point admits a nearby such level inside the radial region.
For a continuous `f` these are the finite-cover choices in Lemma 3.8.  Their
existence is not asserted here.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The visible part of the reciprocal radial denominator. -/
def literalZeroVisibleRadialDenominator {n : ℕ}
    (x : RealEuclidean n) : ℝ :=
  1 + ∑ i : Fin n, x i ^ 2

/-- An everywhere-positive polynomial denominator on visible and one hidden
coordinate. -/
def literalZeroRadialDenominator (n : ℕ)
    (v : RealEuclidean (n + 1)) : ℝ :=
  literalZeroVisibleRadialDenominator (realEuclideanTakeLeft v) +
    (realEuclideanTakeRight v 0) ^ 2

def literalZeroRadialReciprocal (n : ℕ) :
    RealEuclideanFunction (n + 1) :=
  fun v ↦ (literalZeroRadialDenominator n v)⁻¹

def literalZeroSquaredLift {n : ℕ} (f : RealEuclideanFunction n) :
    RealEuclideanFunction (n + 1) :=
  fun v ↦ f (realEuclideanTakeLeft v) ^ 2

theorem literalZeroVisibleRadialDenominator_pos {n : ℕ}
    (x : RealEuclidean n) :
    0 < literalZeroVisibleRadialDenominator x := by
  have hsum : 0 ≤ ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i))
  unfold literalZeroVisibleRadialDenominator
  linarith

theorem literalZeroRadialDenominator_pos (n : ℕ)
    (v : RealEuclidean (n + 1)) :
    0 < literalZeroRadialDenominator n v := by
  unfold literalZeroRadialDenominator
  nlinarith [literalZeroVisibleRadialDenominator_pos
    (realEuclideanTakeLeft v), sq_nonneg (realEuclideanTakeRight v 0)]

theorem literalZeroRadialReciprocal_pos (n : ℕ)
    (v : RealEuclidean (n + 1)) :
    0 < literalZeroRadialReciprocal n v := by
  exact inv_pos.mpr (literalZeroRadialDenominator_pos n v)

theorem literalZeroRadialDenominator_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    literalZeroRadialDenominator n ∈ G (n + 1) := by
  let visibleSquare : Fin n → RealEuclideanFunction (n + 1) :=
    fun i v ↦ v (Fin.castAdd 1 i) ^ 2
  have hvisibleSquare : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      visibleSquare i ∈ G (n + 1) := by
    intro i _
    apply hG.sq_mem
    simpa [visibleSquare] using
      (hG.polynomial (MvPolynomial.X (Fin.castAdd 1 i)))
  have hsum := hG.finset_sum_mem Finset.univ visibleSquare hvisibleSquare
  have hhidden :
      (fun v : RealEuclidean (n + 1) ↦
        v (Fin.natAdd n (0 : Fin 1)) ^ 2) ∈ G (n + 1) := by
    apply hG.sq_mem
    simpa using
      (hG.polynomial (MvPolynomial.X (Fin.natAdd n (0 : Fin 1))))
  have htotal := hG.add (hG.add (hG.const_mem (n := n + 1) 1) hsum)
    hhidden
  convert htotal using 1
  funext v
  simp only [literalZeroRadialDenominator,
    literalZeroVisibleRadialDenominator, realEuclideanTakeLeft,
    realEuclideanTakeRight, Finset.sum_apply, visibleSquare,
    Pi.add_apply]

theorem literalZeroRadialReciprocal_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    literalZeroRadialReciprocal n ∈ G (n + 1) := by
  exact hG.inv (literalZeroRadialDenominator_mem hG n)
    (fun v ↦ ne_of_gt (literalZeroRadialDenominator_pos n v))

theorem literalZeroSquaredLift_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {f : RealEuclideanFunction n} (hf : f ∈ G n) :
    literalZeroSquaredLift f ∈ G (n + 1) := by
  have hpull := hG.affine_comp hf
    (realEuclideanTakeLeftLinearMap n 1).toAffineMap
  have hpull' :
      (fun v : RealEuclidean (n + 1) ↦
        f (realEuclideanTakeLeft v)) ∈ G (n + 1) := by
    change (fun v : RealEuclidean (n + 1) ↦
      f (realEuclideanTakeLeft v)) ∈ G (n + 1) at hpull
    exact hpull
  exact hG.sq_mem hpull'

/-- The fixed one-hidden-variable, two-positive-parameter base constituent.
Its two equations are family members and have every finite smoothness order
when the family is globally smooth. -/
def literalZeroRadialConstituent
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (hn : 0 < n)
    (f : RealEuclideanFunction n) (hf : f ∈ G n)
    (order : ℕ) :
    CharbonnelSardianConstituent G order n 1 where
  visible_pos := hn
  equation := Fin.cases (literalZeroRadialReciprocal n)
    (fun _ ↦ literalZeroSquaredLift f)
  equation_mem := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact literalZeroRadialReciprocal_mem hG n
    · exact literalZeroSquaredLift_mem hG hf
  equation_contDiff := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact (hsmooth (n + 1) (literalZeroRadialReciprocal n)
        (literalZeroRadialReciprocal_mem hG n)).of_le (by simp)
    · exact (hsmooth (n + 1) (literalZeroSquaredLift f)
        (literalZeroSquaredLift_mem hG hf)).of_le (by simp)

/-- The radial equation forces the visible point into the corresponding
bounded sum-of-squares region. -/
theorem literalZeroRadialReciprocal_visible_bound {n : ℕ}
    (x : RealEuclidean n) (y : RealEuclidean 1) (ε : ℝ)
    (hrad : literalZeroRadialReciprocal n
      (realEuclideanAppend x y) = ε) :
    literalZeroVisibleRadialDenominator x ≤ ε⁻¹ := by
  have hden : literalZeroRadialDenominator n
      (realEuclideanAppend x y) = ε⁻¹ := by
    have := congrArg (fun t : ℝ ↦ t⁻¹) hrad
    simpa only [literalZeroRadialReciprocal, inv_inv] using this
  simp only [literalZeroRadialDenominator,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append] at hden
  nlinarith [sq_nonneg (y 0)]

/-- If the visible denominator is below a positive reciprocal level, a
single square-root witness supplies the hidden coordinate.  No square root
is included in the function family equations. -/
theorem literalZeroRadialReciprocal_escape {n : ℕ}
    (x : RealEuclidean n) {ε : ℝ} (hε : 0 < ε)
    (hvisible : literalZeroVisibleRadialDenominator x < ε⁻¹) :
    ∃ y : RealEuclidean 1,
      literalZeroRadialReciprocal n (realEuclideanAppend x y) = ε := by
  let t := ε⁻¹ - literalZeroVisibleRadialDenominator x
  have ht : 0 ≤ t := by dsimp [t]; linarith
  let y : RealEuclidean 1 := fun _ ↦ Real.sqrt t
  refine ⟨y, ?_⟩
  have hden : literalZeroRadialDenominator n
      (realEuclideanAppend x y) = ε⁻¹ := by
    simp only [literalZeroRadialDenominator,
      realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
    change literalZeroVisibleRadialDenominator x + (Real.sqrt t) ^ 2 = ε⁻¹
    rw [Real.sq_sqrt ht]
    dsimp [t]
    ring
  simp only [literalZeroRadialReciprocal, hden, inv_inv]

/-- The exact projected equations of the base constituent. -/
theorem mem_literalZeroRadialConstituent_carrier_iff
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (hn : 0 < n)
    (f : RealEuclideanFunction n) (hf : f ∈ G n)
    (order : ℕ) (x : RealEuclidean n) (ε : RealEuclidean 2) :
    realEuclideanAppend x ε ∈
        (literalZeroRadialConstituent hG hsmooth hn f hf order).carrier ↔
      (∀ i, 0 < ε i) ∧ f x ^ 2 = ε 1 ∧
        ∃ y : RealEuclidean 1,
          literalZeroRadialReciprocal n (realEuclideanAppend x y) = ε 0 := by
  let c := literalZeroRadialConstituent hG hsmooth hn f hf order
  have hcase : Fin.cases (literalZeroRadialReciprocal n)
      (fun _ : Fin 1 ↦ literalZeroSquaredLift f) (1 : Fin 2) =
        literalZeroSquaredLift f := by
    change Fin.cases (literalZeroRadialReciprocal n)
      (fun _ : Fin 1 ↦ literalZeroSquaredLift f)
      (Fin.succ (0 : Fin 1)) = literalZeroSquaredLift f
    exact Fin.cases_succ (0 : Fin 1)
  change realEuclideanAppend x ε ∈ c.carrier ↔ _
  rw [c.mem_carrier_iff]
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · rintro ⟨⟨y, hy⟩, hpos⟩
    refine ⟨hpos, ?_, ⟨y, ?_⟩⟩
    · simpa [c, literalZeroRadialConstituent,
        literalZeroSquaredLift, hcase] using hy 1
    · simpa [c, literalZeroRadialConstituent] using hy 0
  · rintro ⟨hpos, hsq, ⟨y, hrad⟩⟩
    refine ⟨⟨y, ?_⟩, hpos⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [c, literalZeroRadialConstituent] using hrad
    · have hj : j = 0 := Subsingleton.elim j 0
      subst j
      simpa [c, literalZeroRadialConstituent,
        literalZeroSquaredLift, hcase] using hsq

/-- The one-member finite family at common hidden arity one. -/
def literalZeroRadialFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (hn : 0 < n)
    (f : RealEuclideanFunction n) (hf : f ∈ G n)
    (order : ℕ) : CharbonnelFiniteSardianFamily G order n 1 where
  visible_pos := hn
  constituents := [CharbonnelPaddedSardianConstituent.ofConstituent
    (Nat.le_refl 1) (literalZeroRadialConstituent hG hsmooth hn f hf order)]

theorem literalZeroRadialFamily_carrier_eq
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (hn : 0 < n)
    (f : RealEuclideanFunction n) (hf : f ∈ G n)
    (order : ℕ) :
    (literalZeroRadialFamily hG hsmooth hn f hf order).carrier =
      (literalZeroRadialConstituent hG hsmooth hn f hf order).carrier := by
  ext v
  let c := literalZeroRadialConstituent hG hsmooth hn f hf order
  change (∃ piece ∈ [CharbonnelPaddedSardianConstituent.ofConstituent
    (Nat.le_refl 1) c], v ∈ piece.carrier) ↔ v ∈ c.carrier
  constructor
  · rintro ⟨piece, hpiece, hv⟩
    have hpiece' : piece =
        CharbonnelPaddedSardianConstituent.ofConstituent
          (Nat.le_refl 1) c := List.mem_singleton.mp hpiece
    subst piece
    simpa only [CharbonnelPaddedSardianConstituent.carrier_ofConstituent,
      charbonnelParameterPad_refl] using hv
  · intro hv
    refine ⟨CharbonnelPaddedSardianConstituent.ofConstituent
      (Nat.le_refl 1) c, by simp, ?_⟩
    simpa only [CharbonnelPaddedSardianConstituent.carrier_ofConstituent,
      charbonnelParameterPad_refl] using hv

/-- The only analytic input left by this radial construction.  The `close`
clause is the compact-cover small-level condition of Lemma 3.8(b), restricted
to the radial bounded region.  The `reach` clause combines 3.8(a) with the
visible radial margin needed to solve the hidden equation. -/
structure CharbonnelLiteralZeroRadialLevelControls
    {n : ℕ} (f : RealEuclideanFunction n)
    (μ : CharbonnelModulus 2) : Prop where
  close : ∀ ε : RealEuclidean 3, μ.IsBounded ε →
    ∀ x : RealEuclidean n,
      literalZeroVisibleRadialDenominator x ≤ (ε 1)⁻¹ →
      f x ^ 2 = ε 2 →
        ∃ z : RealEuclidean n, f z = 0 ∧ dist x z < ε 0
  reach : ∀ ε : RealEuclidean 3, μ.IsBounded ε →
    ∀ x ∈ frontier {z : RealEuclidean n | f z = 0},
      ‖x‖ < (ε 0)⁻¹ →
        ∃ y : RealEuclidean n,
          dist x y < ε 0 ∧ f y ^ 2 = ε 2 ∧
            literalZeroVisibleRadialDenominator y < (ε 1)⁻¹

/-- Once the finite-cover level controls supply a modulus, the radial
constituent is a condition-3.6 certificate at every positive smoothness
order.  No arbitrary constituent or certificate is assumed. -/
def literalZeroRadialCertificate
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (hn : 0 < n)
    (f : RealEuclideanFunction n) (hf : f ∈ G n)
    (order : ℕ) (horder : 0 < order)
    (μ : CharbonnelModulus 2)
    (hlevel : CharbonnelLiteralZeroRadialLevelControls f μ) :
    CharbonnelSardianApproximationCertificate
      G order n {x | f x = 0} := by
  let A : Set (RealEuclidean n) := {x | f x = 0}
  have hclosed : IsClosed A :=
    (show IsLiteralZeroSet G A from ⟨f, hf, rfl⟩).isClosed hsmooth
  let family := literalZeroRadialFamily hG hsmooth hn f hf order
  refine {
    order_pos := horder
    commonHiddenArity := 1
    family := family
    modulus := μ
    approximates := ?_
  }
  change CharbonnelModulus.IsClosureBoundaryApproximation μ
    family.carrier A
  rw [CharbonnelModulus.IsClosureBoundaryApproximation,
    hclosed.closure_eq]
  constructor
  · intro ε hε x hx
    rw [literalZeroRadialFamily_carrier_eq hG hsmooth hn f hf order] at hx
    rcases (mem_literalZeroRadialConstituent_carrier_iff
      hG hsmooth hn f hf order x
      (CharbonnelModulus.parameterTail ε)).mp hx with
      ⟨_, hsq, ⟨y, hrad⟩⟩
    have hvisible := literalZeroRadialReciprocal_visible_bound x y
      (ε 1) (by simpa [CharbonnelModulus.parameterTail] using hrad)
    obtain ⟨z, hz, hdist⟩ := hlevel.close ε hε x hvisible
      (by simpa [CharbonnelModulus.parameterTail] using hsq)
    exact ⟨z, hz, hdist⟩
  · intro ε hε x hx hnorm
    obtain ⟨y, hdist, hsq, hvisible⟩ :=
      hlevel.reach ε hε x hx hnorm
    have hε₁ : 0 < ε 1 :=
      CharbonnelModulus.IsBounded.coord_pos hε 1
    obtain ⟨hidden, hrad⟩ :=
      literalZeroRadialReciprocal_escape y hε₁ hvisible
    refine ⟨y, hdist, ?_⟩
    rw [literalZeroRadialFamily_carrier_eq hG hsmooth hn f hf order]
    apply (mem_literalZeroRadialConstituent_carrier_iff
      hG hsmooth hn f hf order y
      (CharbonnelModulus.parameterTail ε)).mpr
    refine ⟨?_, ?_, ⟨hidden, ?_⟩⟩
    · intro i
      exact CharbonnelModulus.IsBounded.coord_pos hε i.succ
    · simpa [CharbonnelModulus.parameterTail] using hsq
    · simpa [CharbonnelModulus.parameterTail] using hrad

/-- A source-shaped reduction of the literal-zero rank input to the one
specific radial level-control lemma, independent of smoothness order. -/
def CharbonnelSardianLiteralZeroRadialLevelInput
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ (f : RealEuclideanFunction n), f ∈ G n →
      ∃ μ : CharbonnelModulus 2,
        CharbonnelLiteralZeroRadialLevelControls f μ

theorem charbonnelSardianLiteralZeroBaseInput_of_radialLevels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hlevels : CharbonnelSardianLiteralZeroRadialLevelInput G) :
    CharbonnelSardianLiteralZeroBaseInput G := by
  intro n hn f hf order horder
  obtain ⟨μ, hlevel⟩ := hlevels hn f hf
  exact ⟨literalZeroRadialCertificate hG hsmooth hn f hf
    order horder μ hlevel⟩

end AbelFormalization
