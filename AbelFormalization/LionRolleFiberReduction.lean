import AbelFormalization.JacobianBasis
import AbelFormalization.NormalizedCofactorTrajectory
import AbelFormalization.SmoothGeometricFamily

/-!
# Lion's Rolle reduction for a leaf fiber

This file packages Lemma 5 of Lion's paper in the form consumed by the
dimension induction.  A leaf of codimension `q` in dimension
`q + (p + 1)` is intersected with the first `p` equations of a map to
`R^(p+1)`.  The resulting partial fiber is one-dimensional.  If the leaf
equations together with all `p + 1` target equations have full rank, Rolle's
argument bounds the full fiber by the connected components of the partial
fiber.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The leaf equations followed by the first `p` fiber equations. -/
def lionRolleCombinedConstraints {n q p : ℕ}
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1)) :
    Fin (q + p) → RealEuclideanFunction n :=
  Fin.addCases f (fun j x ↦ g x j.castSucc - t j.castSucc)

/-- The remaining, last fiber equation in Lion's Rolle step. -/
def lionRolleLastEquation {n p : ℕ}
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1)) :
    RealEuclideanFunction n :=
  fun x ↦ g x (Fin.last p) - t (Fin.last p)

/-- The leaf intersected with the fiber of the first `p` target coordinates. -/
def lionRollePartialFiber {n q p : ℕ}
    (U : Set (RealEuclidean n))
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1)) : Set (RealEuclidean n) :=
  {x | x ∈ U ∧ ∀ i, lionRolleCombinedConstraints f g t i x = 0}

/-- The full fiber, regarded as a subset of the partial fiber. -/
def lionRolleFullFiberInPartial {n q p : ℕ}
    (U : Set (RealEuclidean n))
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1)) :
    Set (lionRollePartialFiber U f g t) :=
  {x | g x = t}

theorem mem_lionRollePartialFiber_iff {n q p : ℕ}
    {U : Set (RealEuclidean n)}
    {f : Fin q → RealEuclideanFunction n}
    {g : RealEuclidean n → RealEuclidean (p + 1)}
    {t : RealEuclidean (p + 1)} {x : RealEuclidean n} :
    x ∈ lionRollePartialFiber U f g t ↔
      x ∈ U ∧ (∀ i, f i x = 0) ∧
        ∀ j : Fin p, g x j.castSucc = t j.castSucc := by
  constructor
  · rintro ⟨hxU, hx⟩
    refine ⟨hxU, ?_, ?_⟩
    · intro i
      have hi := hx (Fin.castAdd p i)
      simpa [lionRolleCombinedConstraints] using hi
    · intro j
      have hj := hx (Fin.natAdd q j)
      exact sub_eq_zero.mp (by
        simpa [lionRolleCombinedConstraints] using hj)
  · rintro ⟨hxU, hf, hg⟩
    refine ⟨hxU, ?_⟩
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [lionRolleCombinedConstraints] using hf j
    · simpa [lionRolleCombinedConstraints] using sub_eq_zero.mpr (hg j)

private theorem continuousLinearMap_prod_range_eq_top_of_left_and_kernel_right
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hA : A.range = ⊤)
    (hB : (B.comp A.ker.subtypeL).range = ⊤) :
    (A.prod B).range = ⊤ := by
  rw [LinearMap.range_eq_top] at hA hB ⊢
  rintro ⟨y, z⟩
  obtain ⟨v, hv⟩ := hA y
  obtain ⟨w, hw⟩ := hB (z - B v)
  refine ⟨v + (w : E), ?_⟩
  change (A (v + (w : E)), B (v + (w : E))) = (y, z)
  apply Prod.ext
  · change A (v + (w : E)) = y
    rw [map_add]
    have hwA : A (w : E) = 0 := w.property
    rw [hwA, add_zero]
    exact hv
  · change B (v + (w : E)) = z
    rw [map_add]
    have hwB : B (w : E) = z - B v := by
      simpa [ContinuousLinearMap.comp_apply] using hw
    rw [hwB]
    abel

/-- The differential of `g` restricted to the tangent space `ker df` of the
leaf cut out by `f`.  Surjectivity of this map is Lion's full-rank condition
for `g` restricted to the leaf. -/
def lionLeafRestrictedFDeriv {n q p : ℕ}
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (x : RealEuclidean n) :
    (constraintFDeriv f x).ker →L[ℝ] RealEuclidean (p + 1) :=
  (constraintFDeriv (fun j y ↦ g y j) x).comp
    (constraintFDeriv f x).ker.subtypeL

/-- The coordinate-family definition of the derivative along a leaf is the
ordinary Fréchet derivative of `g` restricted to the leaf tangent space. -/
theorem lionLeafRestrictedFDeriv_eq_fderiv_comp {n q p : ℕ}
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (x : RealEuclidean n)
    (hg : DifferentiableAt ℝ g x) :
    lionLeafRestrictedFDeriv f g x =
      (fderiv ℝ g x).comp (constraintFDeriv f x).ker.subtypeL := by
  unfold lionLeafRestrictedFDeriv
  have hcoordinates : ∀ j, DifferentiableAt ℝ (fun y ↦ g y j) x :=
    differentiableAt_pi.mp hg
  have hderiv : constraintFDeriv (fun j y ↦ g y j) x =
      fderiv ℝ g x := by
    symm
    simpa only [constraintFDeriv] using fderiv_pi hcoordinates
  rw [hderiv]

/-- A submersive leaf presentation and full rank of `g` on the leaf imply
full rank of the joint system consisting of all leaf and target equations.
This is the rank bridge used in Lion's Lemma 5. -/
theorem lionRolleFullConstraint_surjective_of_leafFullRank
    {n q p : ℕ}
    {U : Set (RealEuclidean n)}
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1))
    (hfSubmersion : ∀ x ∈ U, (constraintFDeriv f x).range = ⊤)
    (hgLeafFullRank : ∀ x ∈ U,
      (lionLeafRestrictedFDeriv f g x).range = ⊤) :
    ∀ x : lionRollePartialFiber U f g t,
      (constraintFDeriv
        (functionTupleSnoc (lionRolleCombinedConstraints f g t)
          (lionRolleLastEquation g t)) x).range = ⊤ := by
  intro x
  let Df := constraintFDeriv f (x : RealEuclidean n)
  let Dg := constraintFDeriv (fun j y ↦ g y j)
    (x : RealEuclidean n)
  have hprod : (Df.prod Dg).range = ⊤ := by
    apply continuousLinearMap_prod_range_eq_top_of_left_and_kernel_right
    · simpa only [Df] using hfSubmersion x x.property.1
    · simpa only [Df, Dg, lionLeafRestrictedFDeriv] using
        hgLeafFullRank x x.property.1
  rw [LinearMap.range_eq_top] at hprod ⊢
  intro y
  let yf : RealEuclidean q := fun i ↦
    y (Fin.castSucc (Fin.castAdd p i))
  let yg : RealEuclidean (p + 1) :=
    Fin.lastCases (y (Fin.last (q + p)))
      (fun j ↦ y (Fin.castSucc (Fin.natAdd q j)))
  obtain ⟨v, hv⟩ := hprod (yf, yg)
  refine ⟨v, ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · have hvg : Dg v = yg := congrArg Prod.snd hv
    have hlast := congrFun hvg (Fin.last p)
    change (ContinuousLinearMap.pi
      (fun i ↦ fderiv ℝ (fun y ↦ g y i) x) v) (Fin.last p) =
        yg (Fin.last p) at hlast
    rw [ContinuousLinearMap.pi_apply] at hlast
    change (ContinuousLinearMap.pi (fun i ↦ fderiv ℝ
      (functionTupleSnoc (lionRolleCombinedConstraints f g t)
        (lionRolleLastEquation g t) i) x) v) (Fin.last (q + p)) = _
    rw [ContinuousLinearMap.pi_apply, functionTupleSnoc_last]
    rw [show lionRolleLastEquation g t =
      (fun y ↦ g y (Fin.last p) - t (Fin.last p)) from rfl,
      fderiv_sub_const]
    change fderiv ℝ (fun y ↦ g y (Fin.last p)) x v = _
    simpa only [yg, Fin.lastCases_last] using hlast
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) k
    · have hvf : Df v = yf := congrArg Prod.fst hv
      have hj := congrFun hvf j
      change (ContinuousLinearMap.pi
        (fun i ↦ fderiv ℝ (f i) x) v) j = yf j at hj
      rw [ContinuousLinearMap.pi_apply] at hj
      change (ContinuousLinearMap.pi (fun i ↦ fderiv ℝ
        (functionTupleSnoc (lionRolleCombinedConstraints f g t)
          (lionRolleLastEquation g t) i) x) v)
          (Fin.castAdd p j).castSucc = _
      rw [ContinuousLinearMap.pi_apply, functionTupleSnoc_castSucc]
      rw [lionRolleCombinedConstraints, Fin.addCases_left]
      simpa only [yf] using hj
    · have hvg : Dg v = yg := congrArg Prod.snd hv
      have hj := congrFun hvg j.castSucc
      change (ContinuousLinearMap.pi
        (fun i ↦ fderiv ℝ (fun y ↦ g y i) x) v) j.castSucc =
          yg j.castSucc at hj
      rw [ContinuousLinearMap.pi_apply] at hj
      change (ContinuousLinearMap.pi (fun i ↦ fderiv ℝ
        (functionTupleSnoc (lionRolleCombinedConstraints f g t)
          (lionRolleLastEquation g t) i) x) v)
          (Fin.natAdd q j).castSucc = _
      rw [ContinuousLinearMap.pi_apply, functionTupleSnoc_castSucc]
      rw [lionRolleCombinedConstraints, Fin.addCases_right, fderiv_sub_const]
      change fderiv ℝ (fun y ↦ g y j.castSucc) x v = _
      simpa only [yg, Fin.lastCases_castSucc] using hj

/-- Quantitative form of Lion's Lemma 5.  On a leaf whose dimension equals
the target dimension, the full fiber has at most one point in each connected
component of the fiber of the first target coordinates.

The hypothesis `hfullRank` is the source condition that the leaf equations
and all target equations have independent differentials. -/
theorem enatCard_lionRolleFullFiber_le_partialFiber_components
    {n q p : ℕ}
    {U : Set (RealEuclidean n)}
    (hdim : n = (q + p) + 1)
    (hU : IsOpen U)
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1))
    (hf : ∀ x ∈ U, ∀ i, ContDiffAt ℝ 2 (f i) x)
    (hg : ∀ x ∈ U, ∀ j, ContDiffAt ℝ 2 (fun y ↦ g y j) x)
    (hfullRank : ∀ x : lionRollePartialFiber U f g t,
      (constraintFDeriv
        (functionTupleSnoc (lionRolleCombinedConstraints f g t)
          (lionRolleLastEquation g t)) x).range = ⊤) :
    ENat.card (lionRolleFullFiberInPartial U f g t) ≤
      ENat.card (ConnectedComponents (lionRollePartialFiber U f g t)) := by
  let H := lionRolleCombinedConstraints f g t
  let h := lionRolleLastEquation g t
  let M := lionRollePartialFiber U f g t
  let B : Module.Basis (Fin ((q + p) + 1)) ℝ
      (RealEuclidean n) :=
    (Pi.basisFun ℝ (Fin n)).reindex (finCongr hdim)
  have hHtwo : ∀ x ∈ U, ∀ i, ContDiffAt ℝ 2 (H i) x := by
    intro x hx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_)
    · simpa only [H, lionRolleCombinedConstraints, Fin.addCases_left] using
        hf x hx i
    · simpa only [H, lionRolleCombinedConstraints, Fin.addCases_right] using
        (hg x hx j.castSucc).sub contDiffAt_const
  have hhtwo : ∀ x ∈ U, ContDiffAt ℝ 2 h x := by
    intro x hx
    change ContDiffAt ℝ 2
      (fun y ↦ g y (Fin.last p) - t (Fin.last p)) x
    exact (hg x hx (Fin.last p)).sub contDiffAt_const
  have hMzero : ∀ x : M, ∀ i, H i x = 0 := by
    intro x i
    exact x.property.2 i
  have hlocalConstraint : ∀ x : M, ∃ V ∈ 𝓝 (x : RealEuclidean n),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M := by
    intro x
    refine ⟨U, hU.mem_nhds x.property.1, ?_⟩
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro i
    exact (hy.2 i).trans (x.property.2 i)
  have hdet : ∀ x : M, criticalDeterminant H h B x ≠ 0 := by
    intro x
    change (constraintJacobianInBasis (functionTupleSnoc H h) B x).det ≠ 0
    exact (constraintJacobianInBasis_det_ne_zero_iff_surjective
      (functionTupleSnoc H h) B x).mpr (by
        simpa only [H, h, M] using hfullRank x)
  have hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y := by
    intro x y hy hxy
    exact regularArcIn_of_mem_connectedComponent_normalizedCofactor
      H h B
      (fun z hz ↦ hU.mem_nhds hz.1)
      hHtwo hhtwo
      (fun z hz ↦ hdet ⟨z, hz⟩)
      (fun z hz i ↦ hMzero ⟨z, hz⟩ i)
      hlocalConstraint x y hy hxy
  have hHstrict : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x := by
    intro x i
    exact (hHtwo x x.property.1 i).hasStrictFDerivAt (by norm_num)
  have hhstrict : ∀ x : M,
      HasStrictFDerivAt h (fderiv ℝ h x) x := by
    intro x
    exact (hhtwo x x.property.1).hasStrictFDerivAt (by norm_num)
  let tau : M → RealEuclidean n :=
    fun x ↦ criticalCofactorTangent H h B x
  have hbound : ENat.card {x : M | h x = 0} ≤
      ENat.card (ConnectedComponents M) := by
    apply enatCard_zeroSet_le_connectedComponents_of_regularArcs
      H h tau hMzero hArc hHstrict hhstrict
    · intro x
      exact constraintFDeriv_ker_eq_span_criticalCofactorTangent_of_det_ne_zero
        H h h B x (by
          simpa only [Module.finrank_fin_fun] using hdim)
          (constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
            H h B x (hdet x))
          (hdet x)
    · intro x
      rw [← criticalDeterminant_eq_fderiv_criticalCofactorTangent
        H h B x]
      exact hdet x
  have hzeroSet : {x : M | h x = 0} =
      lionRolleFullFiberInPartial U f g t := by
    ext x
    change g x (Fin.last p) - t (Fin.last p) = 0 ↔ g x = t
    constructor
    · intro hxlast
      have hxpartial :=
        (mem_lionRollePartialFiber_iff (U := U) (f := f)
          (g := g) (t := t)).mp x.property
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact sub_eq_zero.mp hxlast
      · exact hxpartial.2.2 j
    · intro hx
      exact sub_eq_zero.mpr (congrFun hx (Fin.last p))
  simpa only [hzeroSet, M] using hbound

/-- Source-facing form of Lion's Lemma 5.  The leaf equations are a
submersion, and `g` has full rank on the leaf tangent space; the augmented
rank premise needed by the cofactor/Rolle argument is then automatic. -/
theorem enatCard_lionRolleFullFiber_le_partialFiber_components_of_leafFullRank
    {n q p : ℕ}
    {U : Set (RealEuclidean n)}
    (hdim : n = (q + p) + 1)
    (hU : IsOpen U)
    (f : Fin q → RealEuclideanFunction n)
    (g : RealEuclidean n → RealEuclidean (p + 1))
    (t : RealEuclidean (p + 1))
    (hf : ∀ x ∈ U, ∀ i, ContDiffAt ℝ 2 (f i) x)
    (hg : ∀ x ∈ U, ∀ j, ContDiffAt ℝ 2 (fun y ↦ g y j) x)
    (hfSubmersion : ∀ x ∈ U, (constraintFDeriv f x).range = ⊤)
    (hgLeafFullRank : ∀ x ∈ U,
      (lionLeafRestrictedFDeriv f g x).range = ⊤) :
    ENat.card (lionRolleFullFiberInPartial U f g t) ≤
      ENat.card (ConnectedComponents (lionRollePartialFiber U f g t)) := by
  apply enatCard_lionRolleFullFiber_le_partialFiber_components
    hdim hU f g t hf hg
  exact lionRolleFullConstraint_surjective_of_leafFullRank
    f g t hfSubmersion hgLeafFullRank

end AbelFormalization
