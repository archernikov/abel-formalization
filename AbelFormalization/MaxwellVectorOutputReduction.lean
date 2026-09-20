import AbelFormalization.MaxwellPseudofunctionInduction
import AbelFormalization.CharbonnelClosureNullityWitnesses

/-!
# Maxwell reduction from scalar to finite-vector outputs

Maxwell's pseudofunction induction is scalar-valued, whereas theorem 2.4 is
stated for maps between arbitrary finite Euclidean coordinate spaces.  This
file supplies the finite-output reduction.

For one output coordinate, its scalar graph is obtained from the full graph
by moving that coordinate immediately after the base block and projecting
away the remaining output coordinates.  Scalar pseudofunction smoothness can
therefore be applied to every coordinate.  The finitely many resulting
closed empty-interior exceptional sets are then joined, and `contDiffOn_pi`
reassembles the coordinatewise conclusions into smoothness of the original
vector-valued map.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Extracting one scalar coordinate graph -/

/-- Reorder `r + 1` coordinates so that `j` is first and the other
coordinates retain their order through `Fin.succAbove`.  The domain is
written as `1 + r` because it will subsequently be reassociated with the
base-coordinate block. -/
def maxwellOutputCoordinateFirstEquiv {r : ℕ} (j : Fin (r + 1)) :
    Fin (1 + r) ≃ Fin (r + 1) :=
  (finCongr (Nat.one_add r)).trans
    ((finSuccEquiv r).trans (finSuccEquiv' j).symm)

/-- Reindex a vector output by putting coordinate `j` after the base block.
The remaining `r` output coordinates form the final block. -/
def maxwellVectorCoordinateProjectionEquiv
    (p : ℕ) {r : ℕ} (j : Fin (r + 1)) :
    Fin ((p + 1) + r) ≃ Fin (p + (r + 1)) :=
  (finAddAssocCoordinateEquiv p 1 r).trans
    (finPrefixCoordinateEquiv p (maxwellOutputCoordinateFirstEquiv j))

/-- The one-dimensional Euclidean lift of output coordinate `j`. -/
def maxwellScalarCoordinateFunction {p q : ℕ}
    (Phi : RealEuclidean p → RealEuclidean q) (j : Fin q) :
    RealEuclidean p → RealEuclidean 1 :=
  fun x _ ↦ Phi x j

@[simp]
theorem realEuclideanCoordinateReindex_maxwellOutputCoordinateFirstEquiv
    {r : ℕ} (j : Fin (r + 1)) (y : RealEuclidean (r + 1)) :
    realEuclideanCoordinateReindex
        (maxwellOutputCoordinateFirstEquiv j) y =
      realEuclideanAppend (fun _ : Fin 1 ↦ y j)
        (fun k : Fin r ↦ y (j.succAbove k)) := by
  funext i
  refine Fin.addCases (fun a ↦ ?_) (fun k ↦ ?_) i
  · have ha : a = 0 := Fin.eq_zero a
    subst a
    change y (maxwellOutputCoordinateFirstEquiv j (Fin.castAdd r 0)) = y j
    congr 1
  · simp [maxwellOutputCoordinateFirstEquiv,
      realEuclideanCoordinateReindex, realEuclideanAppend]

@[simp]
theorem realEuclideanCoordinateReindex_maxwellVectorCoordinateProjectionEquiv_append
    {p r : ℕ} (j : Fin (r + 1))
    (x : RealEuclidean p) (y : RealEuclidean (r + 1)) :
    realEuclideanCoordinateReindex
        (maxwellVectorCoordinateProjectionEquiv p j)
        (realEuclideanAppend x y) =
      realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y j))
        (fun k : Fin r ↦ y (j.succAbove k)) := by
  rw [maxwellVectorCoordinateProjectionEquiv,
    realEuclideanCoordinateReindex_trans,
    realEuclideanCoordinateReindex_finPrefix_append,
    realEuclideanCoordinateReindex_maxwellOutputCoordinateFirstEquiv,
    realEuclideanCoordinateReindex_finAddAssoc_append]

/-- Projecting the reindexed full graph is exactly the ordinary scalar graph
of coordinate `j`. -/
theorem realEuclideanExistentialProjection_reindexed_maxwellFunctionGraph
    {p r : ℕ} (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean (r + 1))
    (j : Fin (r + 1)) :
    realEuclideanExistentialProjection
        (realEuclideanCoordinateReindex
            (maxwellVectorCoordinateProjectionEquiv p j) ''
          maxwellFunctionGraph U Phi) =
      maxwellFunctionGraph U (maxwellScalarCoordinateFunction Phi j) := by
  ext z
  constructor
  · rintro ⟨w, v, ⟨x, hx, rfl⟩, hv⟩
    have hz :
        z = realEuclideanAppend x (fun _ : Fin 1 ↦ Phi x j) := by
      have hleft := congrArg
        (realEuclideanTakeLeft (n := p + 1) (m := r)) hv
      simpa using hleft.symm
    exact ⟨x, hx, hz⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(fun k : Fin r ↦ Phi x (j.succAbove k)),
      realEuclideanAppend x (Phi x), ⟨x, hx, rfl⟩, ?_⟩
    exact
      realEuclideanCoordinateReindex_maxwellVectorCoordinateProjectionEquiv_append
        j x (Phi x)

/-- If a vector graph belongs to a Charbonnel closure carrying the weak-set
operations, then every scalar coordinate graph belongs to that closure.
Only coordinate reindexing and existential projection are used. -/
theorem maxwellFunctionGraph_scalarCoordinate_mem_charbonnelClosure
    {S : EuclideanSetFamily} {p r : ℕ}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean (r + 1))
    (hgraph :
      maxwellFunctionGraph U Phi ∈ charbonnelClosure S (p + (r + 1)))
    (j : Fin (r + 1)) :
    maxwellFunctionGraph U (maxwellScalarCoordinateFunction Phi j) ∈
      charbonnelClosure S (p + 1) := by
  have hReindex :
      PositiveArityDescriptionReindexBase (charbonnelClosure S) :=
    hC.toDescriptionReindexBase
  have hreindexed :
      realEuclideanCoordinateReindex
          (maxwellVectorCoordinateProjectionEquiv p j) ''
        maxwellFunctionGraph U Phi ∈
      charbonnelClosure S ((p + 1) + r) :=
    hReindex.coordinateReindex (by omega) hgraph
      (maxwellVectorCoordinateProjectionEquiv p j)
  have hprojected :=
    charbonnelClosure_projection (S := S) (n := p + 1) (k := r)
      (by omega) hreindexed
  rw [realEuclideanExistentialProjection_reindexed_maxwellFunctionGraph]
    at hprojected
  exact hprojected

/-! ## Finite exceptional-set assembly -/

/-- The common exceptional set for finitely many scalar output
coordinates. -/
def maxwellCoordinateBadSet {X : Type*} {q : ℕ}
    (A : Fin q → Set X) : Set X :=
  ⋃ j, A j

theorem isClosed_maxwellCoordinateBadSet
    {X : Type*} [TopologicalSpace X] {q : ℕ}
    {A : Fin q → Set X} (hAclosed : ∀ j, IsClosed (A j)) :
    IsClosed (maxwellCoordinateBadSet A) := by
  unfold maxwellCoordinateBadSet
  apply isClosed_iUnion_of_finite
  exact hAclosed

theorem interior_maxwellCoordinateBadSet_eq_empty
    {X : Type*} [TopologicalSpace X] {q : ℕ}
    {A : Fin q → Set X}
    (hAclosed : ∀ j, IsClosed (A j))
    (hAempty : ∀ j, interior (A j) = ∅) :
    interior (maxwellCoordinateBadSet A) = ∅ := by
  exact interior_iUnion_fin_eq_empty_of_closed A hAclosed hAempty

theorem charbonnelClosure_maxwellCoordinateBadSet_mem
    {S : EuclideanSetFamily} {p q : ℕ} (hp : 0 < p)
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {A : Fin q → Set (RealEuclidean p)}
    (hAmem : ∀ j, A j ∈ charbonnelClosure S p) :
    maxwellCoordinateBadSet A ∈ charbonnelClosure S p := by
  have hempty :
      (∅ : Set (RealEuclidean p)) ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp (polynomialSignConstructible_empty p)
  exact charbonnelClosure_iUnion_fin_mem hempty hAmem

/-- Coordinatewise smoothness off finitely many individual exceptional sets
gives vector-valued smoothness off their common union. -/
theorem contDiffOn_realEuclidean_off_maxwellCoordinateBadSet
    {p q N : ℕ} {U : Set (RealEuclidean p)}
    {Phi : RealEuclidean p → RealEuclidean q}
    {A : Fin q → Set (RealEuclidean p)}
    (hcoordinate : ∀ j,
      ContDiffOn ℝ N (fun x ↦ Phi x j) (U \ A j)) :
    ContDiffOn ℝ N Phi (U \ maxwellCoordinateBadSet A) := by
  rw [contDiffOn_pi]
  intro j
  apply (hcoordinate j).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxA
  apply hx.2
  exact Set.mem_iUnion_of_mem j hxA

/-- Finite scalar exceptional sets provide all four conclusions needed in
the vector-valued Maxwell statement: closedness, family membership, empty
interior, and coordinate-assembled smoothness. -/
theorem maxwellVectorContDiffOn_off_coordinateExceptionalSets
    {S : EuclideanSetFamily} {p q N : ℕ} (hp : 0 < p)
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {U : Set (RealEuclidean p)}
    {Phi : RealEuclidean p → RealEuclidean q}
    {A : Fin q → Set (RealEuclidean p)}
    (hAclosed : ∀ j, IsClosed (A j))
    (hAmem : ∀ j, A j ∈ charbonnelClosure S p)
    (hAempty : ∀ j, interior (A j) = ∅)
    (hcoordinate : ∀ j,
      ContDiffOn ℝ N (fun x ↦ Phi x j) (U \ A j)) :
    ∃ bad : Set (RealEuclidean p),
      IsClosed bad ∧
      bad ∈ charbonnelClosure S p ∧
      interior bad = ∅ ∧
      ContDiffOn ℝ N Phi (U \ bad) := by
  refine ⟨maxwellCoordinateBadSet A,
    isClosed_maxwellCoordinateBadSet hAclosed,
    charbonnelClosure_maxwellCoordinateBadSet_mem hp hC hAmem,
    interior_maxwellCoordinateBadSet_eq_empty hAclosed hAempty, ?_⟩
  exact contDiffOn_realEuclidean_off_maxwellCoordinateBadSet hcoordinate

/-! ## From scalar pseudofunction smoothness to vector smoothness -/

/-- Exact representation of an ordinary scalar coordinate graph identifies
the scalar representative with that coordinate, so smoothness transfers to
the original function. -/
theorem contDiffOn_coordinate_of_functionGraph_representsOn
    {p q N : ℕ} {U V : Set (RealEuclidean p)}
    {Phi : RealEuclidean p → RealEuclidean q} {j : Fin q}
    {f : RealEuclidean p → ℝ}
    (hVU : V ⊆ U)
    (hrep :
      MaxwellRelation.RepresentsOn
        (maxwellFunctionGraph U (maxwellScalarCoordinateFunction Phi j)) V
        (fun x _ ↦ f x))
    (hf : ContDiffOn ℝ N f V) :
    ContDiffOn ℝ N (fun x ↦ Phi x j) V := by
  apply hf.congr
  intro x hx
  have hmem :
      realEuclideanAppend x (fun _ : Fin 1 ↦ Phi x j) ∈
        maxwellFunctionGraph U (maxwellScalarCoordinateFunction Phi j) :=
    (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U (maxwellScalarCoordinateFunction Phi j) x
        (fun _ : Fin 1 ↦ Phi x j)).mpr ⟨hVU hx, rfl⟩
  have heq :=
    (hrep x hx (fun _ : Fin 1 ↦ Phi x j)).mp hmem
  exact congrFun heq 0

/-- Scalar pseudofunction order-smoothness, applied to the projected graph of
one output coordinate, produces the corresponding coordinate exceptional
set and smoothness conclusion. -/
theorem maxwellScalarCoordinateSmoothness_of_pseudofunctionOrderSmoothness
    {S : EuclideanSetFamily} {p r N : ℕ}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hscalar :
      MaxwellScalarPseudofunctionOrderSmoothness
        (charbonnelClosure S) N)
    (hp : 0 < p) (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean (r + 1))
    (hUopen : IsOpen U)
    (hUmem : U ∈ charbonnelClosure S p)
    (hgraph :
      maxwellFunctionGraph U Phi ∈ charbonnelClosure S (p + (r + 1)))
    (j : Fin (r + 1)) :
    ∃ A : Set (RealEuclidean p),
      IsClosed A ∧
      A ∈ charbonnelClosure S p ∧
      interior A = ∅ ∧
      ContDiffOn ℝ N (fun x ↦ Phi x j) (U \ A) := by
  let R : MaxwellRelation p 1 :=
    maxwellFunctionGraph U (maxwellScalarCoordinateFunction Phi j)
  have hRmem : R ∈ charbonnelClosure S (p + 1) :=
    maxwellFunctionGraph_scalarCoordinate_mem_charbonnelClosure
      hC U Phi hgraph j
  have hRpseudo : IsMaxwellPseudofunctionOn U R :=
    isMaxwellPseudofunctionOn_functionGraph U
      (maxwellScalarCoordinateFunction Phi j)
  obtain ⟨A, f, hAclosed, hAmem, hAempty, hrep, hfsmooth⟩ :=
    hscalar hp U R hUopen hUmem hRmem hRpseudo
  refine ⟨A, hAclosed, hAmem, hAempty, ?_⟩
  exact contDiffOn_coordinate_of_functionGraph_representsOn
    (V := U \ A) (fun _ hx ↦ hx.1) hrep hfsmooth

/-- The scalar pseudofunction theorem at every finite order implies
Maxwell's full almost-everywhere smoothness statement for all finite vector
outputs. -/
theorem maxwellAlmostEverywhereSmoothness_of_scalarPseudofunctionOrderSmoothness
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hscalar : ∀ N : ℕ,
      MaxwellScalarPseudofunctionOrderSmoothness
        (charbonnelClosure S) N) :
    MaxwellAlmostEverywhereSmoothness (charbonnelClosure S) := by
  intro N p q hp hq U Phi hUopen hUmem hgraph
  cases q with
  | zero => omega
  | succ r =>
      have hcoordinate : ∀ j : Fin (r + 1),
          ∃ A : Set (RealEuclidean p),
            IsClosed A ∧
            A ∈ charbonnelClosure S p ∧
            interior A = ∅ ∧
            ContDiffOn ℝ N (fun x ↦ Phi x j) (U \ A) := by
        intro j
        exact
          maxwellScalarCoordinateSmoothness_of_pseudofunctionOrderSmoothness
            hC (hscalar N) hp U Phi
              hUopen hUmem hgraph j
      choose A hAclosed hAmem hAempty hAsmooth using hcoordinate
      exact
        maxwellVectorContDiffOn_off_coordinateExceptionalSets hp
          hC hAclosed hAmem hAempty hAsmooth

/-- In particular, the scalar first-order pseudofunction package already
implies the vector-valued Maxwell theorem: the existing scalar induction is
followed by the finite-coordinate reduction above. -/
theorem maxwellAlmostEverywhereSmoothness_of_scalarFirstOrderPackage
    {S : EuclideanSetFamily}
    (hC :
      PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hfirst :
      MaxwellScalarFirstOrderPackage (charbonnelClosure S)) :
    MaxwellAlmostEverywhereSmoothness (charbonnelClosure S) :=
  maxwellAlmostEverywhereSmoothness_of_scalarPseudofunctionOrderSmoothness
    hC.toPositiveArityWeakSetStructure
    (maxwellScalarPseudofunctionOrderSmoothness_of_firstOrderPackage
      hC hfirst)

end AbelFormalization
