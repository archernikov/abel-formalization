import AbelFormalization.RestrictedPairMergeExceptionalGraphSequence

/-!
# Flattening a finite exceptional implicit-graph system

This module concatenates a finite first block of equations with a finite
exceptional graph block.  A canonical continuous linear equivalence identifies
the product-valued system with one `Fin (n + N)` constraint map.  The final
section specializes the generic construction to the flat pair-merge graph
source while leaving the first block arbitrary, so a denominator-cleared
compressed family can be supplied later.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Generic finite-family concatenation -/

/-- Concatenate two finite equation families. -/
def finiteEquationFamilyAppend {X : Type*} {n N : ℕ}
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ) :
    Fin (n + N) → X → ℝ :=
  fun r ↦ Fin.addCases F G r

@[simp]
theorem finiteEquationFamilyAppend_castAdd {X : Type*} {n N : ℕ}
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ) (i : Fin n) :
    finiteEquationFamilyAppend F G (Fin.castAdd N i) = F i := by
  simp [finiteEquationFamilyAppend]

@[simp]
theorem finiteEquationFamilyAppend_natAdd {X : Type*} {n N : ℕ}
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ) (j : Fin N) :
    finiteEquationFamilyAppend F G (Fin.natAdd n j) = G j := by
  simp [finiteEquationFamilyAppend]

/-- Linear equivalence between two finite output blocks and one concatenated
finite output vector. -/
def finFunctionProductLinearEquiv (n N : ℕ) :
    ((Fin n → ℝ) × (Fin N → ℝ)) ≃ₗ[ℝ] (Fin (n + N) → ℝ) where
  toFun z := Fin.addCases z.1 z.2
  invFun v :=
    (fun i ↦ v (Fin.castAdd N i), fun j ↦ v (Fin.natAdd n j))
  left_inv := by
    intro z
    ext <;> simp
  right_inv := by
    intro v
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r <;> simp
  map_add' := by
    intro x y
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r <;> simp
  map_smul' := by
    intro c x
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r <;> simp

/-- Continuous-linear form of finite output concatenation. -/
def finFunctionProductContinuousLinearEquiv (n N : ℕ) :
    ((Fin n → ℝ) × (Fin N → ℝ)) ≃L[ℝ] (Fin (n + N) → ℝ) :=
  (finFunctionProductLinearEquiv n N).toContinuousLinearEquiv

@[simp]
theorem finFunctionProductContinuousLinearEquiv_apply
    {n N : ℕ} (z : (Fin n → ℝ) × (Fin N → ℝ)) (r : Fin (n + N)) :
    finFunctionProductContinuousLinearEquiv n N z r =
      Fin.addCases z.1 z.2 r := rfl

/-- Product-valued map associated to two equation families. -/
def finiteEquationFamilyProductMap {X : Type*} {n N : ℕ}
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ) :
    X → ((Fin n → ℝ) × (Fin N → ℝ)) :=
  fun x ↦ (constraintMap F x, constraintMap G x)

/-- The concatenated constraint map is exactly output concatenation applied
to the product-valued block system. -/
theorem constraintMap_finiteEquationFamilyAppend
    {X : Type*} {n N : ℕ}
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ) :
    constraintMap (finiteEquationFamilyAppend F G) =
      finFunctionProductContinuousLinearEquiv n N ∘
        finiteEquationFamilyProductMap F G := by
  funext x r
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r <;>
    simp [finiteEquationFamilyAppend, finiteEquationFamilyProductMap,
      constraintMap]

/-- Output concatenation preserves regular-zero membership. -/
theorem mem_regularZeroSet_finiteEquationFamilyAppend_iff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n N : ℕ} (Omega : Set X)
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ) (x : X) :
    x ∈ regularZeroSet Omega
        (constraintMap (finiteEquationFamilyAppend F G)) ↔
      x ∈ regularZeroSet Omega (finiteEquationFamilyProductMap F G) := by
  let e := ContinuousLinearEquiv.refl ℝ X
  let q := finFunctionProductContinuousLinearEquiv n N
  let H := finiteEquationFamilyProductMap F G
  have hset := regularZeroSet_preimage_continuousLinearEquiv
    e q Omega H
  have hmem := Set.ext_iff.mp hset x
  have hfun : q ∘ H ∘ e =
      constraintMap (finiteEquationFamilyAppend F G) := by
    rw [constraintMap_finiteEquationFamilyAppend]
    funext y
    rfl
  rw [hfun] at hmem
  have hepre : e ⁻¹' Omega = Omega := by
    ext y
    rfl
  rw [hepre] at hmem
  exact hmem

/-- Componentwise membership in a function subalgebra is preserved by finite
family concatenation. -/
theorem finiteEquationFamilyAppend_mem_subalgebra
    {X : Type*} {n N : ℕ} (B : Subalgebra ℝ (X → ℝ))
    (F : Fin n → X → ℝ) (G : Fin N → X → ℝ)
    (hF : ∀ i, F i ∈ B) (hG : ∀ j, G j ∈ B) :
    ∀ r, finiteEquationFamilyAppend F G r ∈ B := by
  intro r
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
  · simpa using hF i
  · simpa using hG j

/-! ## Exceptional pair-merge specialization -/

variable {ι : Type*}

/-- The flattened equation family formed from arbitrary first-block rows and
the maintained exceptional graph equations. -/
def restrictedPairMergeExceptionalFlattenedEquationFamily
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (P : Fin n → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ) :
    Fin (n +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) →
      RestrictedSource (m + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card) a → ℝ :=
  finiteEquationFamilyAppend P
    (restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S)

/-- Product-valued flat system before the output blocks are concatenated. -/
def restrictedPairMergeExceptionalFlatBlockSystem
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (P : Fin n → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ) :
    RestrictedSource (m + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card) a →
      ((Fin n → ℝ) ×
        (Fin (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card → ℝ)) :=
  finiteEquationFamilyProductMap P
    (restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S)

/-- The maintained vector graph system, precomposed with the flat/product
source equivalence, is exactly the vector of maintained restricted graph
equations. -/
theorem restrictedPairMergeExceptionalVectorGraphEquation_graphProduct
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (z : RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a) :
    restrictedPairMergeExceptionalVectorGraphEquation
        D representative offset K k i j S
        (restrictedPairMergeExceptionalGraphProduct z) =
      constraintMap
        (restrictedPairMergeExceptionalRestrictedGraphEquation
          D representative offset K k i j S) z := by
  funext t
  simp only [restrictedPairMergeExceptionalVectorGraphEquation,
    restrictedFixedIterateShiftGraphEquation,
    restrictedPairMergeExceptionalGraphProduct,
    restrictedPairMergeExceptionalGraphDrop,
    restrictedPairMergeExceptionalRestrictedGraphEquation,
    restrictedPairMergeExceptionalGraphBaseArgument,
    restrictedPairMergeExceptionalBaseArgument,
    constraintMap]
  congr 1

/-- The flat block system is the finite implicit graph system with the first
block transported back through the source equivalence. -/
theorem restrictedPairMergeExceptionalFlatBlockSystem_eq_implicit
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (P : Fin n → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ) :
    restrictedPairMergeExceptionalFlatBlockSystem
        D representative offset K k i j S P =
      finiteImplicitGraphLiftSystem
          (constraintMap P ∘
            (restrictedPairMergeExceptionalGraphContinuousLinearEquiv
              (m := m) (p := p) (a := a)
              (N := (restrictedPairMergeExceptionalOffsetSupport
                representative i j S).card)).symm)
          (restrictedPairMergeExceptionalVectorGraphEquation
            D representative offset K k i j S) ∘
        restrictedPairMergeExceptionalGraphContinuousLinearEquiv := by
  funext z
  apply Prod.ext
  · change constraintMap P z = constraintMap P
      (restrictedPairMergeExceptionalGraphContinuousLinearEquiv.symm
        (restrictedPairMergeExceptionalGraphProduct z))
    rw [← restrictedPairMergeExceptionalGraphContinuousLinearEquiv_apply]
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · exact restrictedPairMergeExceptionalVectorGraphEquation_graphProduct
      D representative offset K k i j S z |>.symm

/-- The flattened constraint map is the output equivalence applied to the
product-valued finite implicit graph system in flat source coordinates. -/
theorem constraintMap_restrictedPairMergeExceptionalFlattenedEquationFamily
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (P : Fin n → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ) :
    constraintMap
        (restrictedPairMergeExceptionalFlattenedEquationFamily
          D representative offset K k i j S P) =
      finFunctionProductContinuousLinearEquiv n
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card ∘
        finiteImplicitGraphLiftSystem
            (constraintMap P ∘
              (restrictedPairMergeExceptionalGraphContinuousLinearEquiv
                (m := m) (p := p) (a := a)
                (N := (restrictedPairMergeExceptionalOffsetSupport
                  representative i j S).card)).symm)
            (restrictedPairMergeExceptionalVectorGraphEquation
              D representative offset K k i j S) ∘
          restrictedPairMergeExceptionalGraphContinuousLinearEquiv := by
  calc
    constraintMap
        (restrictedPairMergeExceptionalFlattenedEquationFamily
          D representative offset K k i j S P) =
        finFunctionProductContinuousLinearEquiv n
            (restrictedPairMergeExceptionalOffsetSupport
              representative i j S).card ∘
          restrictedPairMergeExceptionalFlatBlockSystem
            D representative offset K k i j S P :=
      constraintMap_finiteEquationFamilyAppend P
        (restrictedPairMergeExceptionalRestrictedGraphEquation
          D representative offset K k i j S)
    _ = _ := congrArg
      (fun H ↦ finFunctionProductContinuousLinearEquiv n
          (restrictedPairMergeExceptionalOffsetSupport
            representative i j S).card ∘ H)
      (restrictedPairMergeExceptionalFlatBlockSystem_eq_implicit
        D representative offset K k i j S P)

/-- Flattening the two output blocks preserves regular-zero membership for
an arbitrary flat source domain. -/
theorem mem_regularZeroSet_restrictedPairMergeExceptionalFlattenedEquationFamily_iff
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (P : Fin n → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ)
    (Omega : Set (RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a))
    (z : RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a) :
    z ∈ regularZeroSet Omega
        (constraintMap
          (restrictedPairMergeExceptionalFlattenedEquationFamily
            D representative offset K k i j S P)) ↔
      z ∈ regularZeroSet Omega
        (finiteImplicitGraphLiftSystem
            (constraintMap P ∘
              (restrictedPairMergeExceptionalGraphContinuousLinearEquiv
                (m := m) (p := p) (a := a)
                (N := (restrictedPairMergeExceptionalOffsetSupport
                  representative i j S).card)).symm)
            (restrictedPairMergeExceptionalVectorGraphEquation
              D representative offset K k i j S) ∘
          restrictedPairMergeExceptionalGraphContinuousLinearEquiv) := by
  rw [← restrictedPairMergeExceptionalFlatBlockSystem_eq_implicit
    D representative offset K k i j S P]
  exact mem_regularZeroSet_finiteEquationFamilyAppend_iff Omega P
    (restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S) z

/-- A common tower level containing every cleared first-block row and every
exceptional graph row contains the whole flattened family. -/
theorem restrictedPairMergeExceptionalFlattenedEquationFamily_mem_level
    {m p a n ell : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (specialGenerators : Set (RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ))
    (T : RestrictedExpressionTower
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card)
      specialGenerators (ell := ell))
    (P : Fin n → RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport
          representative i j S).card) a → ℝ)
    (hP : ∀ r, P r ∈ T.level ell)
    (hgraph : ∀ t,
      restrictedPairMergeExceptionalRestrictedGraphEquation
        D representative offset K k i j S t ∈ T.level ell) :
    ∀ r, restrictedPairMergeExceptionalFlattenedEquationFamily
      D representative offset K k i j S P r ∈ T.level ell :=
  finiteEquationFamilyAppend_mem_subalgebra (T.level ell) P
    (restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S) hP hgraph

end AbelFormalization
