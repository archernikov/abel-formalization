import AbelFormalization.GeneralCodimensionRegularComponents
import AbelFormalization.RestrictedAdjunctionConstraintSurjectivity

/-!
# Flat reciprocal constraint graphs

This file packages the one-variable reciprocal graph used to replace an open
nonvanishing condition `q x ≠ 0` by the closed equation `u * q x - 1 = 0`.
The graph is written in flat finite coordinates so it can be fed directly to
the arbitrary-codimension regular-fiber theorem.

It supplies three independent ingredients: the homeomorphism with the open
constraint patch, surjectivity of the augmented constraint derivative, and
closure of all augmented equations in a geometric function family.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Splitting one scalar from flat coordinates -/

/-- Append one real scalar as the final coordinate of a finite coordinate
vector. -/
def realEuclideanAppendScalar {a : ℕ}
    (x : RealEuclidean a) (u : ℝ) : RealEuclidean (a + 1) :=
  realEuclideanAppend x (fun _ : Fin 1 ↦ u)

@[simp]
theorem realEuclideanAppendScalar_castAdd {a : ℕ}
    (x : RealEuclidean a) (u : ℝ) (i : Fin a) :
    realEuclideanAppendScalar x u (Fin.castAdd 1 i) = x i := by
  simp [realEuclideanAppendScalar]

@[simp]
theorem realEuclideanAppendScalar_last {a : ℕ}
    (x : RealEuclidean a) (u : ℝ) :
    realEuclideanAppendScalar x u (Fin.natAdd a (0 : Fin 1)) = u := by
  simp [realEuclideanAppendScalar]

/-- Splitting and appending the final scalar is a linear equivalence. -/
def realEuclideanAppendScalarLinearEquiv (a : ℕ) :
    (RealEuclidean a × ℝ) ≃ₗ[ℝ] RealEuclidean (a + 1) where
  toFun p := realEuclideanAppendScalar p.1 p.2
  invFun z :=
    (lagrangePrimalProjection a 1 z, z (Fin.natAdd a (0 : Fin 1)))
  left_inv := by
    intro p
    apply Prod.ext
    · exact lagrangePrimalProjection_append p.1 (fun _ : Fin 1 ↦ p.2)
    · simp [realEuclideanAppendScalar]
  right_inv := by
    intro z
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
    · simp [realEuclideanAppendScalar]
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [realEuclideanAppendScalar]
  map_add' := by
    intro p q
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
    · simp [realEuclideanAppendScalar]
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [realEuclideanAppendScalar]
  map_smul' := by
    intro c p
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
    · simp [realEuclideanAppendScalar]
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [realEuclideanAppendScalar]

/-- Continuous-linear form of the flat scalar split. -/
def realEuclideanAppendScalarContinuousLinearEquiv (a : ℕ) :
    (RealEuclidean a × ℝ) ≃L[ℝ] RealEuclidean (a + 1) :=
  (realEuclideanAppendScalarLinearEquiv a).toContinuousLinearEquiv

@[simp]
theorem realEuclideanAppendScalarContinuousLinearEquiv_apply
    {a : ℕ} (p : RealEuclidean a × ℝ) :
    realEuclideanAppendScalarContinuousLinearEquiv a p =
      realEuclideanAppendScalar p.1 p.2 :=
  rfl

@[simp]
theorem realEuclideanAppendScalarContinuousLinearEquiv_symm_apply
    {a : ℕ} (z : RealEuclidean (a + 1)) :
    (realEuclideanAppendScalarContinuousLinearEquiv a).symm z =
      (lagrangePrimalProjection a 1 z,
        z (Fin.natAdd a (0 : Fin 1))) :=
  rfl

/-! ## Reciprocal constraint systems -/

/-- Append the reciprocal graph equation to a constraint tuple, in flat
`a+1` source coordinates. -/
def reciprocalGraphConstraintSystem {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (q : RealEuclideanFunction a) :
    Fin (k + 1) → RealEuclideanFunction (a + 1) :=
  functionTupleSnoc
    (fun i z ↦ H i (lagrangePrimalProjection a 1 z))
    (fun z ↦ z (Fin.natAdd a (0 : Fin 1)) *
      q (lagrangePrimalProjection a 1 z) - 1)

@[simp]
theorem reciprocalGraphConstraintSystem_castSucc {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (q : RealEuclideanFunction a)
    (i : Fin k) (z : RealEuclidean (a + 1)) :
    reciprocalGraphConstraintSystem H q i.castSucc z =
      H i (lagrangePrimalProjection a 1 z) := by
  simp [reciprocalGraphConstraintSystem]

@[simp]
theorem reciprocalGraphConstraintSystem_last {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (q : RealEuclideanFunction a)
    (z : RealEuclidean (a + 1)) :
    reciprocalGraphConstraintSystem H q (Fin.last k) z =
      z (Fin.natAdd a (0 : Fin 1)) *
        q (lagrangePrimalProjection a 1 z) - 1 := by
  simp [reciprocalGraphConstraintSystem]

/-- The open base patch represented by the reciprocal graph. -/
def reciprocalConstraintPatch {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (q : RealEuclideanFunction a) :
    Set (RealEuclidean a) :=
  {x | (∀ i, H i x = 0) ∧ q x ≠ 0}

@[simp]
theorem mem_reciprocalConstraintPatch {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (q : RealEuclideanFunction a)
    (x : RealEuclidean a) :
    x ∈ reciprocalConstraintPatch H q ↔
      (∀ i, H i x = 0) ∧ q x ≠ 0 :=
  Iff.rfl

/-- The reciprocal constraint patch is homeomorphic to the zero locus of its
flat augmented system. -/
def reciprocalConstraintPatchHomeomorph {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (q : RealEuclideanFunction a)
    (hq : Continuous q) :
    reciprocalConstraintPatch H q ≃ₜ
      constraintZeroLocus (reciprocalGraphConstraintSystem H q) where
  toFun x := ⟨realEuclideanAppendScalar x (q x)⁻¹, by
    intro r
    refine Fin.lastCases ?_ (fun i ↦ ?_) r
    · simp [reciprocalGraphConstraintSystem,
        realEuclideanAppendScalar, inv_mul_cancel₀ x.property.2]
    · simp [reciprocalGraphConstraintSystem,
        realEuclideanAppendScalar, x.property.1 i]⟩
  invFun z := ⟨lagrangePrimalProjection a 1 z, by
    constructor
    · intro i
      simpa only [reciprocalGraphConstraintSystem_castSucc] using
        z.property i.castSucc
    · have hgraph := z.property (Fin.last k)
      rw [reciprocalGraphConstraintSystem_last] at hgraph
      have hmul : z.1 (Fin.natAdd a (0 : Fin 1)) *
          q (lagrangePrimalProjection a 1 z) = 1 :=
        sub_eq_zero.mp hgraph
      intro hzero
      rw [hzero, mul_zero] at hmul
      exact zero_ne_one hmul⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact lagrangePrimalProjection_append x.1
      (fun _ : Fin 1 ↦ (q x)⁻¹)
  right_inv := by
    intro z
    apply Subtype.ext
    have hgraph := z.property (Fin.last k)
    rw [reciprocalGraphConstraintSystem_last] at hgraph
    have hlast : z.1 (Fin.natAdd a (0 : Fin 1)) =
        (q (lagrangePrimalProjection a 1 z))⁻¹ :=
      eq_inv_of_mul_eq_one_left (sub_eq_zero.mp hgraph)
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
    · simp [realEuclideanAppendScalar]
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simpa [realEuclideanAppendScalar] using hlast.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hinv : Continuous
        (fun x : reciprocalConstraintPatch H q ↦ (q x)⁻¹) := by
      apply Continuous.inv₀
      · exact hq.comp continuous_subtype_val
      · intro x
        exact x.property.2
    change Continuous
      (realEuclideanAppendScalarContinuousLinearEquiv a ∘
        (fun x : reciprocalConstraintPatch H q ↦
          ((x : RealEuclidean a), (q x)⁻¹)))
    exact (realEuclideanAppendScalarContinuousLinearEquiv a).continuous.comp
      (continuous_subtype_val.prodMk hinv)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (lagrangePrimalProjectionCLM a 1).continuous.comp
      continuous_subtype_val

/-! ## Derivative and family closure -/

/-- Surjectivity of the old constraints and nonvanishing of the denominator
make the derivative of the flat reciprocal system surjective. -/
theorem reciprocalGraphConstraintSystem_constraintFDeriv_range_eq_top
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (q : RealEuclideanFunction a) (x : RealEuclidean a) (u : ℝ)
    (hH : ∀ i, DifferentiableAt ℝ (H i) x)
    (hq : DifferentiableAt ℝ q x)
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hqne : q x ≠ 0)
    (hsystem : ∀ r, DifferentiableAt ℝ
      (reciprocalGraphConstraintSystem H q r)
      (realEuclideanAppendScalar x u)) :
    (constraintFDeriv (reciprocalGraphConstraintSystem H q)
      (realEuclideanAppendScalar x u)).range = ⊤ := by
  let e : RealEuclidean (a + 1) ≃L[ℝ] (RealEuclidean a × ℝ) :=
    (realEuclideanAppendScalarContinuousLinearEquiv a).symm
  have hproduct :
      (constraintFDeriv
        (functionTupleSnoc
          (fun i (p : RealEuclidean a × ℝ) ↦ H i p.1)
          (fun p : RealEuclidean a × ℝ ↦ p.2 * q p.1 - 1))
        (x, u)).range = ⊤ :=
    constraintFDeriv_denominatorProductSystem_surjective
      H q x u hH hq hsurj hqne
  have hcomposed :
      (constraintFDeriv
        (fun r y ↦ reciprocalGraphConstraintSystem H q r (e.symm y))
        (x, u)).range = ⊤ := by
    have hfun :
        (fun r y ↦ reciprocalGraphConstraintSystem H q r (e.symm y)) =
          functionTupleSnoc
            (fun i (p : RealEuclidean a × ℝ) ↦ H i p.1)
            (fun p : RealEuclidean a × ℝ ↦ p.2 * q p.1 - 1) := by
      funext r p
      refine Fin.lastCases ?_ (fun i ↦ ?_) r
      · simp [e, reciprocalGraphConstraintSystem,
          realEuclideanAppendScalar]
      · simp [e, reciprocalGraphConstraintSystem,
          realEuclideanAppendScalar]
    rw [hfun]
    exact hproduct
  have hresult := constraintFDeriv_surjective_of_comp_continuousLinearEquiv
    e (reciprocalGraphConstraintSystem H q) (x, u)
      (by simpa [e] using hsystem) hcomposed
  simpa [e] using hresult

/-- Every equation of the flat reciprocal graph remains in a geometric
function family. -/
theorem IsGeometricFunctionFamily.reciprocalGraphConstraintSystem_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (q : RealEuclideanFunction a)
    (hH : ∀ i, H i ∈ G a) (hq : q ∈ G a) :
    ∀ r, reciprocalGraphConstraintSystem H q r ∈ G (a + 1) := by
  intro r
  refine Fin.lastCases ?_ (fun i ↦ ?_) r
  · have heq : reciprocalGraphConstraintSystem H q (Fin.last k) =
        (fun z : RealEuclidean (a + 1) ↦
          z (Fin.natAdd a (0 : Fin 1)) *
            q (lagrangePrimalProjection a 1 z) - 1) := by
      funext z
      exact reciprocalGraphConstraintSystem_last H q z
    rw [heq]
    apply hG.sub_mem
    · apply hG.mul
      · simpa using hG.polynomial
          (MvPolynomial.X (Fin.natAdd a (0 : Fin 1)))
      · change (q ∘ (lagrangePrimalProjection a 1).toAffineMap) ∈ G (a + 1)
        exact hG.affine_comp hq (lagrangePrimalProjection a 1).toAffineMap
    · exact hG.const_mem 1
  · have heq : reciprocalGraphConstraintSystem H q i.castSucc =
        (fun z : RealEuclidean (a + 1) ↦
          H i (lagrangePrimalProjection a 1 z)) := by
      funext z
      exact reciprocalGraphConstraintSystem_castSucc H q i z
    rw [heq]
    change ((H i) ∘ (lagrangePrimalProjection a 1).toAffineMap) ∈ G (a + 1)
    exact hG.affine_comp (hH i) (lagrangePrimalProjection a 1).toAffineMap

end AbelFormalization
