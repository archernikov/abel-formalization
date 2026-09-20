import AbelFormalization.FiniteWeightInitialLength
import Mathlib.LinearAlgebra.Quotient.Pi

set_option autoImplicit false

/-!
# Finite-weight initial submodules and quotients

The full finite-weight initial operation is monotone.  More importantly, it
commutes with every coordinatewise semilinear map whose scalar homomorphism is
surjective, provided that the kernel of the map is already contained in the
source submodule.  The latter hypothesis is exactly what permits lower
components killed by a quotient map to be subtracted before taking an initial
component.

For an actually coordinatewise homogeneous denominator, the quotient of the
finite product is also identified with the product of the coordinate
quotients.  The final lemmas record the quotient correspondence in a form
that lifts equality of quotient images back upstairs.
-/

noncomputable section

namespace AbelFormalization

section Monotonicity

variable {R : Type*} [Ring R] {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Increasing the input submodule increases every possible least-weight
coordinate piece. -/
theorem finiteWeightInitialPiece_mono {U V : Submodule R (∀ i, M i)}
    (hUV : U ≤ V) (i : Fin n) :
    finiteWeightInitialPiece U i ≤ finiteWeightInitialPiece V i := by
  exact Submodule.map_mono (inf_le_inf hUV le_rfl)

/-- Full finite-weight initial formation is monotone. -/
theorem finiteWeightInitial_mono {U V : Submodule R (∀ i, M i)}
    (hUV : U ≤ V) : finiteWeightInitial U ≤ finiteWeightInitial V := by
  intro x hx
  apply (mem_finiteWeightInitial_iff V x).mpr
  intro i
  exact finiteWeightInitialPiece_mono hUV i
    ((mem_finiteWeightInitial_iff U x).mp hx i)

end Monotonicity

section CoordinatewiseSemilinearMap

variable {R S : Type*} [Ring R] [Ring S]
variable {σ : R →+* S} [RingHomSurjective σ]
variable {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {N : Fin n → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]

/-- The semilinear map of finite products induced coordinate by coordinate. -/
def finiteWeightPiMap (f : ∀ i, M i →ₛₗ[σ] N i) :
    (∀ i, M i) →ₛₗ[σ] (∀ i, N i) where
  toFun x i := f i (x i)
  map_add' x y := by
    funext i
    exact (f i).map_add (x i) (y i)
  map_smul' c x := by
    funext i
    exact (f i).map_smulₛₗ c (x i)

@[simp]
theorem finiteWeightPiMap_apply (f : ∀ i, M i →ₛₗ[σ] N i)
    (x : ∀ i, M i) (i : Fin n) : finiteWeightPiMap f x i = f i (x i) := rfl

@[simp]
theorem finiteWeightPiMap_single (f : ∀ i, M i →ₛₗ[σ] N i)
    (i : Fin n) (v : M i) :
    finiteWeightPiMap f (Pi.single i v) = Pi.single i (f i v) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Coordinatewise maps commute with every strict-prefix projection. -/
theorem finiteWeightPiMap_prefixProjection
    (f : ∀ i, M i →ₛₗ[σ] N i) (k : ℕ) (x : ∀ i, M i) :
    finiteWeightPiMap f (finiteWeightPrefixProjection R M k x) =
      finiteWeightPrefixProjection S N k (finiteWeightPiMap f x) := by
  ext i
  by_cases hi : i.val < k <;>
    simp [finiteWeightPrefixProjection_apply, hi]

/-- Membership in the kernel of a coordinatewise map is detected in every
coordinate. -/
theorem mem_ker_finiteWeightPiMap_iff
    (f : ∀ i, M i →ₛₗ[σ] N i) (x : ∀ i, M i) :
    x ∈ LinearMap.ker (finiteWeightPiMap f) ↔
      ∀ i, x i ∈ LinearMap.ker (f i) := by
  constructor
  · intro hx i
    apply LinearMap.mem_ker.mpr
    have hxi := congrFun (LinearMap.mem_ker.mp hx) i
    exact hxi
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext i
    exact LinearMap.mem_ker.mp (hx i)

/-- Coordinatewise surjectivity gives surjectivity of the product map.  The
initial-quotient theorem below does not require this stronger hypothesis. -/
theorem finiteWeightPiMap_surjective
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (finiteWeightPiMap f) := by
  classical
  intro y
  choose x hx using fun i => hf i (y i)
  exact ⟨x, funext hx⟩

/-- Coordinatewise initial pieces commute with a coordinatewise semilinear
map once every vector killed by the full map already belongs to `U`.

For the reverse inclusion, lift an element producing a target initial
coordinate and subtract its full strict prefix.  That prefix is killed by the
map, hence belongs to `U`; the corrected lift is still in `U` and has its
strict prefix equal to zero. -/
theorem map_finiteWeightInitialPiece_eq_finiteWeightInitialPiece_map
    (f : ∀ i, M i →ₛₗ[σ] N i) (U : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ U) (i : Fin n) :
    (finiteWeightInitialPiece U i).map (f i) =
      finiteWeightInitialPiece (U.map (finiteWeightPiMap f)) i := by
  apply le_antisymm
  · rintro y ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxv⟩ := hv
    change x i = v at hxv
    refine ⟨finiteWeightPiMap f x, ⟨⟨x, hx.1, rfl⟩, ?_⟩, ?_⟩
    · apply LinearMap.mem_ker.mpr
      rw [← finiteWeightPiMap_prefixProjection]
      rw [LinearMap.mem_ker.mp hx.2, map_zero]
    · change f i (x i) = f i v
      exact congrArg (f i) hxv
  · rintro v ⟨y, hy, hyv⟩
    obtain ⟨x, hx, hxy⟩ := hy.1
    let p : ∀ j, M j := finiteWeightPrefixProjection R M i.val x
    have hpker : p ∈ LinearMap.ker (finiteWeightPiMap f) := by
      apply LinearMap.mem_ker.mpr
      dsimp only [p]
      rw [finiteWeightPiMap_prefixProjection, hxy]
      exact LinearMap.mem_ker.mp hy.2
    have hpU : p ∈ U := hker hpker
    let w : ∀ j, M j := x - p
    have hwU : w ∈ U := U.sub_mem hx hpU
    have hwzero : finiteWeightPrefixProjection R M i.val w = 0 := by
      dsimp only [w, p]
      rw [map_sub, finiteWeightPrefixProjection_idempotent, sub_self]
    have hwPiece : w i ∈ finiteWeightInitialPiece U i :=
      ⟨w, ⟨hwU, LinearMap.mem_ker.mpr hwzero⟩, rfl⟩
    refine ⟨w i, hwPiece, ?_⟩
    change f i (w i) = v
    have hwi : w i = x i := by
      dsimp only [w, p]
      simp [finiteWeightPrefixProjection_apply]
    have hxyi : f i (x i) = y i := congrFun hxy i
    change y i = v at hyv
    rw [hwi, hxyi, hyv]

/-- Full finite-weight initial formation commutes with a coordinatewise
semilinear map whenever its kernel is contained in the source submodule.
Neither the full map nor its coordinate maps need be surjective. -/
theorem map_finiteWeightInitial_eq_finiteWeightInitial_map
    (f : ∀ i, M i →ₛₗ[σ] N i) (U : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ U) :
    (finiteWeightInitial U).map (finiteWeightPiMap f) =
      finiteWeightInitial (U.map (finiteWeightPiMap f)) := by
  classical
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply (mem_finiteWeightInitial_iff (U.map (finiteWeightPiMap f)) _).mpr
    intro i
    rw [← map_finiteWeightInitialPiece_eq_finiteWeightInitialPiece_map f U hker i]
    exact ⟨x i, (mem_finiteWeightInitial_iff U x).mp hx i, rfl⟩
  · intro y hy
    rw [← LinearMap.sum_single_apply N y]
    apply ((finiteWeightInitial U).map (finiteWeightPiMap f)).sum_mem
    intro i hi
    have hyi := (mem_finiteWeightInitial_iff
      (U.map (finiteWeightPiMap f)) y).mp hy i
    rw [← map_finiteWeightInitialPiece_eq_finiteWeightInitialPiece_map
      f U hker i] at hyi
    obtain ⟨v, hv, hfv⟩ := hyi
    refine ⟨Pi.single i v, single_mem_finiteWeightInitial U i hv, ?_⟩
    rw [finiteWeightPiMap_single, hfv]

end CoordinatewiseSemilinearMap

section HomogeneousQuotient

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The denominator seen in one finite-weight coordinate: a vector belongs
when its single-coordinate embedding belongs to the global denominator. -/
def finiteWeightCoordinateSubmodule (D : Submodule R (∀ i, M i)) (i : Fin n) :
    Submodule R (M i) := D.comap (LinearMap.single R M i)

@[simp]
theorem mem_finiteWeightCoordinateSubmodule_iff
    (D : Submodule R (∀ i, M i)) (i : Fin n) (v : M i) :
    v ∈ finiteWeightCoordinateSubmodule D i ↔ Pi.single i v ∈ D := Iff.rfl

/-- A coordinatewise homogeneous denominator is exactly the product of its
coordinate denominators. -/
theorem finiteWeightHomogeneous_eq_pi_coordinateSubmodule
    (D : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D) :
    D = Submodule.pi Set.univ (finiteWeightCoordinateSubmodule D) := by
  classical
  apply le_antisymm
  · intro x hx
    apply (Submodule.mem_pi).mpr
    intro i hi
    exact (mem_finiteWeightCoordinateSubmodule_iff D i (x i)).mpr
      (hD x hx i)
  · intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply D.sum_mem
    intro i hi
    exact (mem_finiteWeightCoordinateSubmodule_iff D i (x i)).mp
      ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))

/-- For a homogeneous denominator, the coordinate denominator is also its
actual least-weight piece at that coordinate. -/
theorem finiteWeightInitialPiece_eq_coordinateSubmodule_of_homogeneous
    (D : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D) (i : Fin n) :
    finiteWeightInitialPiece D i = finiteWeightCoordinateSubmodule D i := by
  classical
  apply le_antisymm
  · rintro v ⟨x, hx, hxv⟩
    change x i = v at hxv
    rw [← hxv]
    exact (mem_finiteWeightCoordinateSubmodule_iff D i (x i)).mpr
      (hD x hx.1 i)
  · intro v hv
    refine ⟨Pi.single i v,
      ⟨(mem_finiteWeightCoordinateSubmodule_iff D i v).mp hv, ?_⟩, ?_⟩
    · apply LinearMap.mem_ker.mpr
      simp [finiteWeightPrefixProjection_single]
    · simp

/-- The concrete coordinatewise quotient map associated with a homogeneous
finite-weight denominator.  Its definition does not require homogeneity. -/
def finiteWeightCoordinateQuotientMap (D : Submodule R (∀ i, M i)) :
    (∀ i, M i) →ₗ[R] (∀ i, M i ⧸ finiteWeightCoordinateSubmodule D i) :=
  finiteWeightPiMap (fun i => (finiteWeightCoordinateSubmodule D i).mkQ)

@[simp]
theorem finiteWeightCoordinateQuotientMap_apply
    (D : Submodule R (∀ i, M i)) (x : ∀ i, M i) (i : Fin n) :
    finiteWeightCoordinateQuotientMap D x i =
      Submodule.Quotient.mk (x i) := rfl

/-- Homogeneity identifies the kernel of the coordinatewise quotient map
with the original global denominator. -/
theorem ker_finiteWeightCoordinateQuotientMap
    (D : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D) :
    LinearMap.ker (finiteWeightCoordinateQuotientMap D) = D := by
  have hDpi := finiteWeightHomogeneous_eq_pi_coordinateSubmodule D hD
  ext x
  constructor
  · intro hx
    rw [hDpi]
    apply (Submodule.mem_pi).mpr
    intro i hi
    have hxi := (mem_ker_finiteWeightPiMap_iff
      (fun i => (finiteWeightCoordinateSubmodule D i).mkQ) x).mp hx i
    simpa only [Submodule.ker_mkQ] using hxi
  · intro hx
    apply (mem_ker_finiteWeightPiMap_iff
      (fun i => (finiteWeightCoordinateSubmodule D i).mkQ) x).mpr
    intro i
    rw [Submodule.ker_mkQ]
    exact (Submodule.mem_pi.mp (hDpi.le hx)) i (Set.mem_univ i)

/-- The quotient by a homogeneous finite-weight denominator is the product
of the coordinate quotients. -/
def finiteWeightHomogeneousQuotientEquiv
    (D : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D) :
    ((∀ i, M i) ⧸ D) ≃ₗ[R]
      (∀ i, M i ⧸ finiteWeightCoordinateSubmodule D i) :=
  (Submodule.quotEquivOfEq D
      (Submodule.pi Set.univ (finiteWeightCoordinateSubmodule D))
      (finiteWeightHomogeneous_eq_pi_coordinateSubmodule D hD)).trans
    (Submodule.quotientPi (finiteWeightCoordinateSubmodule D))

@[simp]
theorem finiteWeightHomogeneousQuotientEquiv_mk
    (D : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D)
    (x : ∀ i, M i) :
    finiteWeightHomogeneousQuotientEquiv D hD (Submodule.Quotient.mk x) =
      fun i => Submodule.Quotient.mk (x i) := by
  classical
  simp only [finiteWeightHomogeneousQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  rfl

/-- Composing the ordinary quotient map with the homogeneous quotient
equivalence gives the literal coordinatewise quotient map. -/
theorem finiteWeightHomogeneousQuotientEquiv_comp_mkQ
    (D : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D) :
    (finiteWeightHomogeneousQuotientEquiv D hD).toLinearMap.comp D.mkQ =
      finiteWeightCoordinateQuotientMap D := by
  apply LinearMap.ext
  intro x
  funext i
  exact congrFun (finiteWeightHomogeneousQuotientEquiv_mk D hD x) i

/-- The concrete homogeneous quotient commutes with full finite-weight
initial formation as soon as its denominator lies in `U`. -/
theorem map_finiteWeightInitial_eq_finiteWeightInitial_map_coordinateQuotient
    (D U : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D) (hDU : D ≤ U) :
    (finiteWeightInitial U).map (finiteWeightCoordinateQuotientMap D) =
      finiteWeightInitial (U.map (finiteWeightCoordinateQuotientMap D)) := by
  apply map_finiteWeightInitial_eq_finiteWeightInitial_map
  change LinearMap.ker (finiteWeightCoordinateQuotientMap D) ≤ U
  rw [ker_finiteWeightCoordinateQuotientMap D hD]
  exact hDU

end HomogeneousQuotient

section QuotientCorrespondence

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Equality of quotient images lifts to equality of submodules when both
submodules contain the denominator. -/
theorem eq_of_map_mkQ_eq_map_mkQ (D U V' : Submodule R V)
    (hDU : D ≤ U) (hDV : D ≤ V')
    (hmap : U.map D.mkQ = V'.map D.mkQ) : U = V' := by
  have hcomap := congrArg (fun W : Submodule R (V ⧸ D) => W.comap D.mkQ) hmap
  simpa only [Submodule.comap_map_mkQ, sup_eq_right.mpr hDU,
    sup_eq_right.mpr hDV] using hcomap

/-- The quotient map is injective on the interval of submodules containing
its denominator. -/
theorem map_mkQ_eq_map_mkQ_iff (D U V' : Submodule R V)
    (hDU : D ≤ U) (hDV : D ≤ V') :
    U.map D.mkQ = V'.map D.mkQ ↔ U = V' := by
  constructor
  · exact eq_of_map_mkQ_eq_map_mkQ D U V' hDU hDV
  · rintro rfl
    rfl

end QuotientCorrespondence

end AbelFormalization
