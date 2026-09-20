import AbelFormalization.FiniteWeightQuotient
import AbelFormalization.FiniteWeightIteration
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

set_option autoImplicit false

/-!
# Finite-weight initial formation and localization

Localization of a finite product is performed coordinatewise.  Clearing one
denominator from the entire lower prefix proves that the full finite-weight
initial submodule commutes with localization.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The coordinatewise localization map on a finite product of modules. -/
def finiteWeightLocalizationMap (S : Submonoid R) :
    (∀ i, M i) →ₗ[R] (∀ i, LocalizedModule S (M i)) :=
  LinearMap.pi fun i =>
    (LocalizedModule.mkLinearMap S (M i)).comp (LinearMap.proj i)

instance finiteWeightLocalizationMap_isLocalizedModule (S : Submonoid R) :
    IsLocalizedModule S (finiteWeightLocalizationMap (M := M) S) := by
  unfold finiteWeightLocalizationMap
  infer_instance

@[simp]
theorem finiteWeightLocalizationMap_apply (S : Submonoid R)
    (x : ∀ i, M i) (i : Fin n) :
    finiteWeightLocalizationMap (M := M) S x i =
      LocalizedModule.mkLinearMap S (M i) (x i) := rfl

/-- A fraction in the product localization is evaluated coordinatewise. -/
theorem finiteWeightLocalizationMap_mk'_apply (S : Submonoid R)
    (x : ∀ i, M i) (s : S) (i : Fin n) :
    IsLocalizedModule.mk' (finiteWeightLocalizationMap (M := M) S) x s i =
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (M i)) (x i) s := by
  apply IsLocalizedModule.smul_injective
    (LocalizedModule.mkLinearMap S (M i)) s
  change s •
      (IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S) x s i) =
    s • IsLocalizedModule.mk'
      (LocalizedModule.mkLinearMap S (M i)) (x i) s
  rw [← Pi.smul_apply, IsLocalizedModule.mk'_cancel',
    IsLocalizedModule.mk'_cancel']
  rfl

/-- Coordinatewise localization commutes with every finite prefix
projection, including on fractions with a common denominator. -/
theorem finiteWeightLocalizationMap_mk'_prefix (S : Submonoid R)
    (k : ℕ) (x : ∀ i, M i) (s : S) :
    IsLocalizedModule.mk' (finiteWeightLocalizationMap (M := M) S)
        (finiteWeightPrefixProjection R M k x) s =
      finiteWeightPrefixProjection (Localization S)
        (fun i => LocalizedModule S (M i)) k
        (IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S) x s) := by
  ext i
  rw [finiteWeightLocalizationMap_mk'_apply]
  by_cases hi : i.val < k
  · simp [finiteWeightPrefixProjection_apply, hi,
      finiteWeightLocalizationMap_mk'_apply]
  · simp [finiteWeightPrefixProjection_apply, hi]

/-- Full least-weight initial formation commutes with localization of a
finite product.  The reverse inclusion clears a single denominator from the
entire lower prefix, rather than clearing its coordinates separately. -/
theorem localized_finiteWeightInitial (S : Submonoid R)
    (U : Submodule R (∀ i, M i)) :
    (finiteWeightInitial U).localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) =
      finiteWeightInitial (R := Localization S)
        (U.localized' (Localization S) S
          (finiteWeightLocalizationMap (M := M) S)) := by
  classical
  apply le_antisymm
  · intro y hy
    rcases (Submodule.mem_localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S)
      (finiteWeightInitial U) y).mp hy with
      ⟨x, hx, s, rfl⟩
    apply (mem_finiteWeightInitial_iff _ _).mpr
    intro i
    rcases (mem_finiteWeightInitial_iff U x).mp hx i with
      ⟨v, hv, hvi⟩
    refine ⟨IsLocalizedModule.mk'
      (finiteWeightLocalizationMap (M := M) S) v s, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact ⟨v, hv.1, s, rfl⟩
      · apply LinearMap.mem_ker.mpr
        rw [← finiteWeightLocalizationMap_mk'_prefix,
          LinearMap.mem_ker.mp hv.2, IsLocalizedModule.mk'_zero]
    · change (IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S) v s) i =
        (IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S) x s) i
      rw [finiteWeightLocalizationMap_mk'_apply,
        finiteWeightLocalizationMap_mk'_apply]
      change v i = x i at hvi
      rw [hvi]
  · intro y hy
    rw [← LinearMap.sum_single_apply
      (fun i => LocalizedModule S (M i)) y]
    apply Submodule.sum_mem
    intro i hi
    rcases (mem_finiteWeightInitial_iff _ y).mp hy i with
      ⟨v', hv', hv'i⟩
    rcases (Submodule.mem_localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S) U v').mp hv'.1 with
      ⟨v, hv, s, hvs⟩
    have hzero : IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S)
        (finiteWeightPrefixProjection R M i.val v) s = 0 := by
      rw [finiteWeightLocalizationMap_mk'_prefix, hvs,
        LinearMap.mem_ker.mp hv'.2]
    obtain ⟨t, ht⟩ :=
      (IsLocalizedModule.mk'_eq_zero'
        (finiteWeightLocalizationMap (M := M) S) s).mp hzero
    change (t : R) • finiteWeightPrefixProjection R M i.val v = 0 at ht
    let w : ∀ i, M i := (t : R) • v
    have hwU : w ∈ U := U.smul_mem (t : R) hv
    have hwprefix : finiteWeightPrefixProjection R M i.val w = 0 := by
      change finiteWeightPrefixProjection R M i.val ((t : R) • v) = 0
      rw [map_smul, ht]
    have hwi : (t : R) • v i ∈ finiteWeightInitialPiece U i := by
      refine ⟨w, ⟨hwU, LinearMap.mem_ker.mpr hwprefix⟩, ?_⟩
      simp [w]
    have hsource : Pi.single i ((t : R) • v i) ∈ finiteWeightInitial U :=
      single_mem_finiteWeightInitial U i hwi
    have hyrepr : IsLocalizedModule.mk'
        (LocalizedModule.mkLinearMap S (M i)) (v i) s = y i := by
      change v' i = y i at hv'i
      calc
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (M i))
            (v i) s =
            IsLocalizedModule.mk'
              (finiteWeightLocalizationMap (M := M) S) v s i :=
          (finiteWeightLocalizationMap_mk'_apply S v s i).symm
        _ = v' i := congrFun hvs i
        _ = y i := hv'i
    refine ⟨Pi.single i ((t : R) • v i), hsource, t * s, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      rw [finiteWeightLocalizationMap_mk'_apply,
        Pi.single_eq_same, Pi.single_eq_same,
        ← Submonoid.smul_def,
        IsLocalizedModule.mk'_cancel_left, hyrepr]
    · simp [finiteWeightLocalizationMap_mk'_apply, hji]

/-! ## Transport of a triangular equivalence -/

/-- The linear equivalence on the product of localized coordinates induced
by a linear equivalence before localization. -/
def finiteWeightLocalizedEquiv (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i)) :
    (∀ i, LocalizedModule S (M i)) ≃ₗ[Localization S]
      (∀ i, LocalizedModule S (M i)) :=
  IsLocalizedModule.mapEquiv S
    (finiteWeightLocalizationMap (M := M) S)
    (finiteWeightLocalizationMap (M := M) S)
    (Localization S) J

/-- The localized equivalence applies the original equivalence to the
numerator and leaves a common denominator unchanged. -/
@[simp]
theorem finiteWeightLocalizedEquiv_mk'
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (x : ∀ i, M i) (s : S) :
    finiteWeightLocalizedEquiv (M := M) S J
        (IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S) x s) =
      IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S) (J x) s := by
  change
    IsLocalizedModule.mapExtendScalars S
        (finiteWeightLocalizationMap (M := M) S)
        (finiteWeightLocalizationMap (M := M) S)
        (Localization S) J.toLinearMap
        (IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S) x s) = _
  rw [IsLocalizedModule.mapExtendScalars_apply_apply,
    IsLocalizedModule.map_mk']
  rfl

/-- The product localization of a single-coordinate vector is the
corresponding single-coordinate localized fraction. -/
theorem finiteWeightLocalizationMap_mk'_single
    (S : Submonoid R) (i : Fin n) (v : M i) (s : S) :
    IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S) (Pi.single i v) s =
      Pi.single i
        (IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap S (M i)) v s) := by
  classical
  ext j
  rw [finiteWeightLocalizationMap_mk'_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Coordinatewise homogeneity is preserved by localization. -/
theorem finiteWeightLocalized_homogeneous
    (S : Submonoid R)
    (U : Submodule R (∀ i, M i))
    (hU : ∀ x ∈ U, ∀ i, Pi.single i (x i) ∈ U) :
    ∀ x ∈ U.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S), ∀ i,
      Pi.single i (x i) ∈
        U.localized' (Localization S) S
          (finiteWeightLocalizationMap (M := M) S) := by
  intro x hx i
  rcases (Submodule.mem_localized' (Localization S) S
    (finiteWeightLocalizationMap (M := M) S) U x).mp hx with
    ⟨u, hu, s, rfl⟩
  rw [finiteWeightLocalizationMap_mk'_apply,
    ← finiteWeightLocalizationMap_mk'_single]
  exact ⟨Pi.single i (u i), hU u hu i, s, rfl⟩

/-- A convenient specialization of `finiteWeightLocalizedEquiv_mk'` to a
single-coordinate localized fraction. -/
@[simp]
theorem finiteWeightLocalizedEquiv_single_mk'
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (i : Fin n) (v : M i) (s : S) :
    finiteWeightLocalizedEquiv (M := M) S J
        (Pi.single i
          (IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap S (M i)) v s)) =
      IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S)
        (J (Pi.single i v)) s := by
  rw [← finiteWeightLocalizationMap_mk'_single,
    finiteWeightLocalizedEquiv_mk']

/-- Localization preserves the lower-triangular hypothesis on a finite
weight product. -/
theorem finiteWeightLocalizedEquiv_triangular
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i),
      J (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection R M i.val (J (Pi.single i v))) :
    ∀ i (v : LocalizedModule S (M i)),
      finiteWeightLocalizedEquiv (M := M) S J (Pi.single i v) =
        Pi.single i v +
          finiteWeightPrefixProjection (Localization S)
            (fun i ↦ LocalizedModule S (M i)) i.val
            (finiteWeightLocalizedEquiv (M := M) S J
              (Pi.single i v)) := by
  intro i v'
  obtain ⟨⟨v, s⟩, rfl⟩ :=
    IsLocalizedModule.mk'_surjective S
      (LocalizedModule.mkLinearMap S (M i)) v'
  calc
    finiteWeightLocalizedEquiv (M := M) S J
        (Pi.single i
          (IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap S (M i)) v s)) =
      IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S)
        (J (Pi.single i v)) s :=
      finiteWeightLocalizedEquiv_single_mk' S J i v s
    _ = IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S)
        (Pi.single i v +
          finiteWeightPrefixProjection R M i.val
            (J (Pi.single i v))) s :=
      congrArg
        (fun x : ∀ i, M i ↦
          IsLocalizedModule.mk'
            (finiteWeightLocalizationMap (M := M) S) x s)
        (htri i v)
    _ = IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S)
          (Pi.single i v) s +
        IsLocalizedModule.mk'
          (finiteWeightLocalizationMap (M := M) S)
          (finiteWeightPrefixProjection R M i.val
            (J (Pi.single i v))) s := by
      rw [IsLocalizedModule.mk'_add]
    _ = Pi.single i
          (IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap S (M i)) v s) +
        finiteWeightPrefixProjection (Localization S)
          (fun i ↦ LocalizedModule S (M i)) i.val
          (IsLocalizedModule.mk'
            (finiteWeightLocalizationMap (M := M) S)
            (J (Pi.single i v)) s) := by
      rw [finiteWeightLocalizationMap_mk'_single,
        finiteWeightLocalizationMap_mk'_prefix]
    _ = Pi.single i
          (IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap S (M i)) v s) +
        finiteWeightPrefixProjection (Localization S)
          (fun i ↦ LocalizedModule S (M i)) i.val
          (finiteWeightLocalizedEquiv (M := M) S J
            (Pi.single i
              (IsLocalizedModule.mk'
                (LocalizedModule.mkLinearMap S (M i)) v s))) := by
      rw [finiteWeightLocalizedEquiv_single_mk']

/-- Localizing the image of a submodule under `J` is the image of the
localized submodule under the induced localized equivalence. -/
theorem localized_map_eq_map_finiteWeightLocalizedEquiv
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (U : Submodule R (∀ i, M i)) :
    (U.map J.toLinearMap).localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) =
      (U.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S)).map
          (finiteWeightLocalizedEquiv (M := M) S J).toLinearMap := by
  apply le_antisymm
  · intro y hy
    rcases (Submodule.mem_localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S)
      (U.map J.toLinearMap) y).mp hy with ⟨z, hz, s, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨IsLocalizedModule.mk'
      (finiteWeightLocalizationMap (M := M) S) x s, ?_, ?_⟩
    · exact ⟨x, hx, s, rfl⟩
    · exact finiteWeightLocalizedEquiv_mk' S J x s
  · rintro y ⟨y', hy', rfl⟩
    rcases (Submodule.mem_localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S) U y').mp hy' with
      ⟨x, hx, s, rfl⟩
    change finiteWeightLocalizedEquiv (M := M) S J
      (IsLocalizedModule.mk'
        (finiteWeightLocalizationMap (M := M) S) x s) ∈ _
    rw [finiteWeightLocalizedEquiv_mk']
    exact ⟨J x, ⟨x, hx, rfl⟩, s, rfl⟩

/-- A finite-weight descent step commutes with coordinatewise
localization. -/
theorem localized_finiteWeightDescentStep
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (U : Submodule R (∀ i, M i)) :
    (finiteWeightDescentStep J U).localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) =
      finiteWeightDescentStep
        (finiteWeightLocalizedEquiv (M := M) S J)
        (U.localized' (Localization S) S
          (finiteWeightLocalizationMap (M := M) S)) := by
  unfold finiteWeightDescentStep
  rw [localized_finiteWeightInitial,
    localized_map_eq_map_finiteWeightLocalizedEquiv]

/-- Every finite-weight descent iterate commutes with coordinatewise
localization. -/
theorem localized_finiteWeightDescentIterate
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N₀ : Submodule R (∀ i, M i)) (j : ℕ) :
    (finiteWeightDescentIterate J N₀ j).localized'
        (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) =
      finiteWeightDescentIterate
        (finiteWeightLocalizedEquiv (M := M) S J)
        (N₀.localized' (Localization S) S
          (finiteWeightLocalizationMap (M := M) S)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change
        (finiteWeightDescentStep J
          (finiteWeightDescentIterate J N₀ j)).localized'
            (Localization S) S
            (finiteWeightLocalizationMap (M := M) S) =
          finiteWeightDescentStep
            (finiteWeightLocalizedEquiv (M := M) S J)
            (finiteWeightDescentIterate
              (finiteWeightLocalizedEquiv (M := M) S J)
              (N₀.localized' (Localization S) S
                (finiteWeightLocalizationMap (M := M) S)) j)
      rw [localized_finiteWeightDescentStep, ih]

end AbelFormalization
