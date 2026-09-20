import AbelFormalization.LionCompactificationFiber
import AbelFormalization.ClosedZeroSetCharbonnelBridge

/-!
# Lion's compactification in flat Euclidean coordinates

Lion's compactification adjoins two scalar variables and a copy of the
target.  This file writes that map on one `RealEuclidean` source and proves
that all of its coordinates remain in a geometric function family.  The
target-distance equation is written as the Euclidean sum of coordinate
squares, the algebraic form used in the paper.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The original source coordinate in the flat block `(x,u,v,t)`. -/
def lionFlatCompactificationBase {a b : ℕ}
    (z : RealEuclidean (a + (1 + (1 + b)))) : RealEuclidean a :=
  realEuclideanTakeLeft z

/-- The first scalar auxiliary coordinate in the flat block `(x,u,v,t)`. -/
def lionFlatCompactificationFirstAux {a b : ℕ}
    (z : RealEuclidean (a + (1 + (1 + b)))) : ℝ :=
  realEuclideanTakeLeft (realEuclideanTakeRight z) 0

/-- The second scalar auxiliary coordinate in the flat block `(x,u,v,t)`. -/
def lionFlatCompactificationSecondAux {a b : ℕ}
    (z : RealEuclidean (a + (1 + (1 + b)))) : ℝ :=
  realEuclideanTakeLeft
    (realEuclideanTakeRight (realEuclideanTakeRight z)) 0

/-- The recorded target coordinate in the flat block `(x,u,v,t)`. -/
def lionFlatCompactificationTarget {a b : ℕ}
    (z : RealEuclidean (a + (1 + (1 + b)))) : RealEuclidean b :=
  realEuclideanTakeRight
    (realEuclideanTakeRight (realEuclideanTakeRight z))

/-- The algebraic squared distance between `g(x)` and the recorded target. -/
def lionFlatCompactificationTargetDistanceSq {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (z : RealEuclidean (a + (1 + (1 + b)))) : ℝ :=
  ∑ j : Fin b,
    (g (lionFlatCompactificationBase z) j -
      lionFlatCompactificationTarget z j) ^ 2

/-- Regard a coordinate vector as a point of the standard Euclidean
`L²` realization. -/
def lionEuclideanTarget {b : ℕ}
    (t : RealEuclidean b) : EuclideanSpace ℝ (Fin b) :=
  euclideanCenter t

/-- Unflatten `(x,u,v,t)` into the product source of
`lionCompactificationMap`, using the standard Euclidean metric on `t`. -/
def lionFlatCompactificationUnflattenSource {a b : ℕ}
    (z : RealEuclidean (a + (1 + (1 + b)))) :
    LionCompactificationSource
      (RealEuclidean a) (EuclideanSpace ℝ (Fin b)) :=
  (lionFlatCompactificationBase z,
    (lionFlatCompactificationFirstAux z,
      (lionFlatCompactificationSecondAux z,
        lionEuclideanTarget (lionFlatCompactificationTarget z))))

/-- Flatten the product target `(eta,epsilon,t)` back into one coordinate
vector. -/
def lionFlatCompactificationFlattenTarget {b : ℕ}
    (w : LionCompactificationTarget (EuclideanSpace ℝ (Fin b))) :
    RealEuclidean (1 + (1 + b)) :=
  realEuclideanAppend (fun _ ↦ w.1)
    (realEuclideanAppend (fun _ ↦ w.2.1)
      (fun j ↦ w.2.2.ofLp j))

/-- Lion's map in flat coordinates:
`(x,u,v,t) ↦ (delta(x)-u², ∑ᵢ(gᵢ(x)-tᵢ)²+v², t)`. -/
def lionFlatCompactificationMap {a b : ℕ}
    (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean b) :
    RealEuclidean (a + (1 + (1 + b))) →
      RealEuclidean (1 + (1 + b)) :=
  fun z ↦
    realEuclideanAppend
      (fun _ ↦ delta (lionFlatCompactificationBase z) -
        lionFlatCompactificationFirstAux z ^ 2)
      (realEuclideanAppend
        (fun _ ↦ lionFlatCompactificationTargetDistanceSq g z +
          lionFlatCompactificationSecondAux z ^ 2)
        (lionFlatCompactificationTarget z))

@[simp]
theorem lionFlatCompactificationBase_append {a b : ℕ}
    (x : RealEuclidean a) (u v : RealEuclidean 1)
    (t : RealEuclidean b) :
    lionFlatCompactificationBase
        (realEuclideanAppend x
          (realEuclideanAppend u (realEuclideanAppend v t))) = x := by
  simp [lionFlatCompactificationBase]

@[simp]
theorem lionFlatCompactificationFirstAux_append {a b : ℕ}
    (x : RealEuclidean a) (u v : RealEuclidean 1)
    (t : RealEuclidean b) :
    lionFlatCompactificationFirstAux
        (realEuclideanAppend x
          (realEuclideanAppend u (realEuclideanAppend v t))) = u 0 := by
  simp [lionFlatCompactificationFirstAux]

@[simp]
theorem lionFlatCompactificationSecondAux_append {a b : ℕ}
    (x : RealEuclidean a) (u v : RealEuclidean 1)
    (t : RealEuclidean b) :
    lionFlatCompactificationSecondAux
        (realEuclideanAppend x
          (realEuclideanAppend u (realEuclideanAppend v t))) = v 0 := by
  simp [lionFlatCompactificationSecondAux]

@[simp]
theorem lionFlatCompactificationTarget_append {a b : ℕ}
    (x : RealEuclidean a) (u v : RealEuclidean 1)
    (t : RealEuclidean b) :
    lionFlatCompactificationTarget
        (realEuclideanAppend x
          (realEuclideanAppend u (realEuclideanAppend v t))) = t := by
  simp [lionFlatCompactificationTarget]

@[simp]
theorem lionFlatCompactificationMap_append {a b : ℕ}
    (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean b)
    (x : RealEuclidean a) (u v : RealEuclidean 1)
    (t : RealEuclidean b) :
    lionFlatCompactificationMap delta g
        (realEuclideanAppend x
          (realEuclideanAppend u (realEuclideanAppend v t))) =
      realEuclideanAppend
        (fun _ ↦ delta x - u 0 ^ 2)
        (realEuclideanAppend
          (fun _ ↦ ∑ j : Fin b, (g x j - t j) ^ 2 + v 0 ^ 2)
          t) := by
  simp [lionFlatCompactificationMap,
    lionFlatCompactificationTargetDistanceSq]

/-- The flat algebraic map is exactly the previously defined product
compactification after realizing the target with its standard Euclidean
metric and flattening the output. -/
theorem lionFlatCompactificationMap_eq_flatten_lionCompactificationMap
    {a b : ℕ} (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean b)
    (z : RealEuclidean (a + (1 + (1 + b)))) :
    lionFlatCompactificationMap delta g z =
      lionFlatCompactificationFlattenTarget
        (lionCompactificationMap delta
          (fun x ↦ lionEuclideanTarget (g x))
          (lionFlatCompactificationUnflattenSource z)) := by
  funext q
  refine Fin.addCases (fun i ↦ ?_) (fun q' ↦ ?_) q
  ·
    simp [lionFlatCompactificationMap,
      lionFlatCompactificationFlattenTarget,
      lionFlatCompactificationUnflattenSource,
      lionCompactificationMap]
  · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) q'
    ·
      simp [lionFlatCompactificationMap,
        lionFlatCompactificationFlattenTarget,
        lionFlatCompactificationUnflattenSource,
        lionCompactificationMap,
        lionFlatCompactificationTargetDistanceSq,
        lionEuclideanTarget, EuclideanSpace.dist_sq_eq,
        Real.dist_eq, sq_abs]
    ·
      simp [lionFlatCompactificationMap,
        lionFlatCompactificationFlattenTarget,
        lionFlatCompactificationUnflattenSource,
        lionCompactificationMap, lionEuclideanTarget]

/-- Every coordinate of Lion's flat compactification belongs to the same
geometric family as `delta` and `g`.  No differentiation is used here. -/
theorem IsGeometricFunctionFamily.lionFlatCompactificationMap_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {a b : ℕ} (delta : RealEuclideanFunction a)
    (g : RealEuclidean a → RealEuclidean b)
    (hdelta : delta ∈ G a) (hg : FunctionTupleInFamily G g) :
    FunctionTupleInFamily G (lionFlatCompactificationMap delta g) := by
  classical
  let L := realEuclideanTakeLeftLinearMap a (1 + (1 + b))
  have hdeltaPull :
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        delta (lionFlatCompactificationBase z)) ∈
          G (a + (1 + (1 + b))) := by
    have hpull := hG.affine_comp hdelta L.toAffineMap
    simpa [L, lionFlatCompactificationBase, Function.comp_def] using hpull
  have hgPull : ∀ j : Fin b,
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        g (lionFlatCompactificationBase z) j) ∈
          G (a + (1 + (1 + b))) := by
    intro j
    have hpull := hG.affine_comp (hg j) L.toAffineMap
    simpa [L, lionFlatCompactificationBase, Function.comp_def] using hpull
  let uIndex : Fin (a + (1 + (1 + b))) :=
    Fin.natAdd a (Fin.castAdd (1 + b) (0 : Fin 1))
  let vIndex : Fin (a + (1 + (1 + b))) :=
    Fin.natAdd a (Fin.natAdd 1 (Fin.castAdd b (0 : Fin 1)))
  let tIndex : Fin b → Fin (a + (1 + (1 + b))) := fun j ↦
    Fin.natAdd a (Fin.natAdd 1 (Fin.natAdd 1 j))
  have hu :
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        lionFlatCompactificationFirstAux z) ∈
          G (a + (1 + (1 + b))) := by
    have hcoord := hG.polynomial (MvPolynomial.X uIndex)
    simpa [uIndex, lionFlatCompactificationFirstAux,
      realEuclideanTakeLeft, realEuclideanTakeRight] using hcoord
  have hv :
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        lionFlatCompactificationSecondAux z) ∈
          G (a + (1 + (1 + b))) := by
    have hcoord := hG.polynomial (MvPolynomial.X vIndex)
    simpa [vIndex, lionFlatCompactificationSecondAux,
      realEuclideanTakeLeft, realEuclideanTakeRight] using hcoord
  have ht : ∀ j : Fin b,
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        lionFlatCompactificationTarget z j) ∈
          G (a + (1 + (1 + b))) := by
    intro j
    have hcoord := hG.polynomial (MvPolynomial.X (tIndex j))
    simpa [tIndex, lionFlatCompactificationTarget,
      realEuclideanTakeRight] using hcoord
  have hfirst :
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        delta (lionFlatCompactificationBase z) -
          lionFlatCompactificationFirstAux z ^ 2) ∈
          G (a + (1 + (1 + b))) :=
    hG.sub_mem hdeltaPull (hG.sq_mem hu)
  have hdifference : ∀ j : Fin b,
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        g (lionFlatCompactificationBase z) j -
          lionFlatCompactificationTarget z j) ∈
          G (a + (1 + (1 + b))) := by
    intro j
    exact hG.sub_mem (hgPull j) (ht j)
  have hdistance :
      lionFlatCompactificationTargetDistanceSq g ∈
        G (a + (1 + (1 + b))) := by
    have hsum := hG.finset_sum_mem (Finset.univ : Finset (Fin b))
      (fun j ↦ fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        (g (lionFlatCompactificationBase z) j -
          lionFlatCompactificationTarget z j) ^ 2)
      (by intro j _; exact hG.sq_mem (hdifference j))
    convert hsum using 1
    funext z
    simp [lionFlatCompactificationTargetDistanceSq, Finset.sum_apply]
  have hsecond :
      (fun z : RealEuclidean (a + (1 + (1 + b))) ↦
        lionFlatCompactificationTargetDistanceSq g z +
          lionFlatCompactificationSecondAux z ^ 2) ∈
          G (a + (1 + (1 + b))) :=
    hG.add hdistance (hG.sq_mem hv)
  intro q
  refine Fin.addCases (fun _ ↦ ?_) (fun q' ↦ ?_) q
  · simpa [lionFlatCompactificationMap] using hfirst
  · refine Fin.addCases (fun _ ↦ ?_) (fun j ↦ ?_) q'
    · simpa [lionFlatCompactificationMap] using hsecond
    · simpa [lionFlatCompactificationMap] using ht j

/-- Specialization to the canonical positive proper carpet on `ℝᵃ`. -/
theorem IsGeometricFunctionFamily.lionStandardFlatCompactificationMap_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    FunctionTupleInFamily G
      (lionFlatCompactificationMap (lionStandardCarpet a) g) :=
  hG.lionFlatCompactificationMap_mem (lionStandardCarpet a) g
    (hG.lionStandardCarpet_mem a) hg

end AbelFormalization
