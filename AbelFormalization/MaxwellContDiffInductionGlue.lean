import AbelFormalization.MaxwellAlmostEverywhereSmoothness
import AbelFormalization.DirectionalClosureContDiff
import AbelFormalization.Wilkie28WeakSelectionCompactComponentReduction

/-!
# Calculus glue for Maxwell's smoothness induction

Maxwell's almost-everywhere smoothness proof recursively replaces the first
partial derivatives by total pseudofunctions whose graphs remain in the weak
family.  The geometric construction of those pseudofunctions is separate.
This file proves the finite-dimensional calculus step: once the surrogates
agree with all basis partial derivatives on one common open complement and
are smooth to order N there, the original vector-valued map is smooth to
order N+1.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Reconstructing the derivative from smooth scalar partial derivatives
raises the differentiability order by one. -/
theorem contDiffOn_succ_of_basis_partials
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (basis : Module.Basis κ ℝ E)
    {V : Set E} (hV : IsOpen V)
    {N : ℕ} {f : E → ℝ} {df : κ → E → ℝ}
    (hf : ∀ x ∈ V, DifferentiableAt ℝ f x)
    (hdf_eq : ∀ x ∈ V, ∀ i,
      df i x = fderiv ℝ f x (basis i))
    (hdf_smooth : ∀ i, ContDiffOn ℝ N (df i) V) :
    ContDiffOn ℝ (N + 1) f V := by
  let f' : E → E →L[ℝ] ℝ := fun x ↦
    continuousLinearMapFromBasis basis (fun i ↦ df i x)
  have hf'eq : ∀ x ∈ V, f' x = fderiv ℝ f x := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply basis.ext
    intro i
    change continuousLinearMapFromBasis basis (fun j ↦ df j x) (basis i) =
      fderiv ℝ f x (basis i)
    rw [continuousLinearMapFromBasis_apply_basis]
    exact hdf_eq x hx i
  have hf'contDiff : ContDiffOn ℝ N f' V := by
    change ContDiffOn ℝ N
      (fun x ↦ ∑ i, df i x •
        LinearMap.toContinuousLinearMap (basis.coord i)) V
    apply ContDiffOn.sum
    intro i _hi
    exact (hdf_smooth i).smul contDiffOn_const
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hV.uniqueDiffOn]
  refine ⟨by simp, f', hf'contDiff, ?_⟩
  intro x hx
  rw [hf'eq x hx]
  exact (hf x hx).hasFDerivAt.hasFDerivWithinAt

/-- Coordinatewise form for maps between the project's Euclidean spaces. -/
theorem contDiffOn_succ_realEuclidean_of_coordinatePartials
    {p q N : ℕ} {V : Set (RealEuclidean p)}
    (hV : IsOpen V)
    {Phi : RealEuclidean p → RealEuclidean q}
    {dPhi : Fin q → Fin p → RealEuclidean p → ℝ}
    (hPhiDiff : ∀ x ∈ V, DifferentiableAt ℝ Phi x)
    (hdPhi_eq : ∀ x ∈ V, ∀ j i,
      dPhi j i x =
        fderiv ℝ (fun y ↦ Phi y j) x
          ((Pi.basisFun ℝ (Fin p)) i))
    (hdPhi_smooth :
      ∀ j i, ContDiffOn ℝ N (dPhi j i) V) :
    ContDiffOn ℝ (N + 1) Phi V := by
  rw [contDiffOn_pi]
  intro j
  apply contDiffOn_succ_of_basis_partials
    (Pi.basisFun ℝ (Fin p)) hV
  · intro x hx
    exact differentiableAt_pi.mp (hPhiDiff x hx) j
  · intro x hx i
    exact hdPhi_eq x hx j i
  · intro i
    exact hdPhi_smooth j i

/-- The common exceptional set used in the finite coordinate assembly:
the first-order bad locus together with every bad locus obtained recursively
for a derivative surrogate. -/
def maxwellDerivativeBadSet {X : Type*} {p q : ℕ}
    (A0 : Set X) (A : Fin q → Fin p → Set X) : Set X :=
  A0 ∪ ⋃ j, ⋃ i, A j i

/-- A finite common union of closed exceptional sets is closed. -/
theorem isClosed_maxwellDerivativeBadSet
    {X : Type*} [TopologicalSpace X] {p q : ℕ}
    {A0 : Set X} {A : Fin q → Fin p → Set X}
    (hA0 : IsClosed A0) (hA : ∀ j i, IsClosed (A j i)) :
    IsClosed (maxwellDerivativeBadSet A0 A) := by
  apply hA0.union
  apply isClosed_iUnion_of_finite
  intro j
  apply isClosed_iUnion_of_finite
  intro i
  exact hA j i

/-- A finite common union of closed empty-interior exceptional sets still
has empty interior. -/
theorem interior_maxwellDerivativeBadSet_eq_empty
    {X : Type*} [TopologicalSpace X] {p q : ℕ}
    {A0 : Set X} {A : Fin q → Fin p → Set X}
    (hA0closed : IsClosed A0) (hA0empty : interior A0 = ∅)
    (hAclosed : ∀ j i, IsClosed (A j i))
    (hAempty : ∀ j i, interior (A j i) = ∅) :
    interior (maxwellDerivativeBadSet A0 A) = ∅ := by
  unfold maxwellDerivativeBadSet
  rw [interior_union_isClosed_of_interior_empty hA0closed]
  · exact hA0empty
  · apply interior_iUnion_fin_eq_empty_of_closed
    · intro j
      exact isClosed_iUnion_of_finite fun i ↦ hAclosed j i
    · intro j
      exact interior_iUnion_fin_eq_empty_of_closed
        (A j) (hAclosed j) (hAempty j)

/-- A finite union of members of a Charbonnel closure remains in the
closure, once the empty set in the relevant arity is available. -/
theorem charbonnelClosure_iUnion_fin_mem
    {S : EuclideanSetFamily} {d k : ℕ}
    {F : Fin k → Set (RealEuclidean d)}
    (hempty : (∅ : Set (RealEuclidean d)) ∈ charbonnelClosure S d)
    (hF : ∀ i, F i ∈ charbonnelClosure S d) :
    (⋃ i, F i) ∈ charbonnelClosure S d := by
  induction k with
  | zero => simpa using hempty
  | succ k ih =>
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
      apply charbonnelClosure_union (hF 0)
      simpa [Function.comp_def] using
        ih (fun j ↦ hF j.succ)

/-- The finite exceptional-set union used by the smoothness induction is a
member of the Charbonnel closure. -/
theorem charbonnelClosure_maxwellDerivativeBadSet_mem
    {S : EuclideanSetFamily} {p q : ℕ} (hp : 0 < p)
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {A0 : Set (RealEuclidean p)}
    {A : Fin q → Fin p → Set (RealEuclidean p)}
    (hA0 : A0 ∈ charbonnelClosure S p)
    (hA : ∀ j i, A j i ∈ charbonnelClosure S p) :
    maxwellDerivativeBadSet A0 A ∈ charbonnelClosure S p := by
  have hempty :
      (∅ : Set (RealEuclidean p)) ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp (polynomialSignConstructible_empty p)
  apply charbonnelClosure_union hA0
  apply charbonnelClosure_iUnion_fin_mem hempty
  intro j
  exact charbonnelClosure_iUnion_fin_mem hempty (hA j)

/-- Full finite-coordinate induction step on a common open complement.  Each
recursive smoothness result may initially live off its own bad set; monotonicity
restricts it to the finite common complement before derivative reconstruction. -/
theorem contDiffOn_succ_realEuclidean_off_derivativeBadSet
    {p q N : ℕ} {U : Set (RealEuclidean p)}
    (hUopen : IsOpen U)
    {Phi : RealEuclidean p → RealEuclidean q}
    {A0 : Set (RealEuclidean p)}
    {dPhi : Fin q → Fin p → RealEuclidean p → ℝ}
    {A : Fin q → Fin p → Set (RealEuclidean p)}
    (hA0closed : IsClosed A0)
    (hPhiDiff : ∀ x ∈ U \ A0, DifferentiableAt ℝ Phi x)
    (hAclosed : ∀ j i, IsClosed (A j i))
    (hdPhi_eq : ∀ x ∈ U \ maxwellDerivativeBadSet A0 A, ∀ j i,
      dPhi j i x =
        fderiv ℝ (fun y ↦ Phi y j) x
          ((Pi.basisFun ℝ (Fin p)) i))
    (hdPhi_smooth :
      ∀ j i, ContDiffOn ℝ N (dPhi j i) (U \ A j i)) :
    ContDiffOn ℝ (N + 1) Phi
      (U \ maxwellDerivativeBadSet A0 A) := by
  have hbadClosed : IsClosed (maxwellDerivativeBadSet A0 A) :=
    isClosed_maxwellDerivativeBadSet hA0closed hAclosed
  have hVopen : IsOpen (U \ maxwellDerivativeBadSet A0 A) :=
    hUopen.sdiff hbadClosed
  apply contDiffOn_succ_realEuclidean_of_coordinatePartials hVopen
  · intro x hx
    apply hPhiDiff x
    exact ⟨hx.1, fun hxA0 ↦ hx.2 (Or.inl hxA0)⟩
  · exact hdPhi_eq
  · intro j i
    apply (hdPhi_smooth j i).mono
    intro x hx
    refine ⟨hx.1, fun hxA ↦ hx.2 ?_⟩
    simp only [maxwellDerivativeBadSet, mem_union, mem_iUnion]
    exact Or.inr ⟨j, i, hxA⟩

end AbelFormalization
