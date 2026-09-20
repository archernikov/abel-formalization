import AbelFormalization.LaurentIdealTools
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Homogeneous ideals of genuine multivariate Laurent polynomial rings

The exponent grading is the actual identity grading on an additive group
algebra. The finite-rank
height theorem uses the actual group `Fin h → ℤ`, split one coordinate at a
time, with no assumed localization or ideal-extension conclusion.
-/

noncomputable section

namespace AbelFormalization

section GroupAlgebra

variable (R G : Type*) [CommRing R] [AddCommGroup G]

/-- The coefficient inclusion into a commutative additive group algebra. -/
def groupAlgebraC : R →+* AddMonoidAlgebra R G :=
  AddMonoidAlgebra.singleZeroRingHom

@[simp] theorem groupAlgebraC_apply (a : R) :
    groupAlgebraC R G a = AddMonoidAlgebra.single 0 a := rfl

variable {R G}

/-- Multiplication by an inverse group monomial produces weight zero. -/
theorem groupAlgebra_inverse_single_mul (g : G) (a : R) :
    AddMonoidAlgebra.single (-g) (1 : R) * AddMonoidAlgebra.single g a =
      groupAlgebraC R G a := by simp

omit [AddCommGroup G] in
/-- For the identity grading, homogeneous elements have single-point support. -/
theorem groupAlgebra_homogeneous_iff_single (f : AddMonoidAlgebra R G) :
    SetLike.IsHomogeneousElem (AddMonoidAlgebra.grade R) f ↔
      ∃ g : G, ∃ a : R, AddMonoidAlgebra.single g a = f := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := (AddMonoidAlgebra.mem_grade_iff' R g f).mp hg
    exact ⟨g, a, ha⟩
  · rintro ⟨g, a, rfl⟩
    exact ⟨g, AddMonoidAlgebra.single_mem_grade g a⟩

/-- The coefficient subring is exactly the full weight-zero component. -/
theorem groupAlgebra_mem_grade_zero_iff (f : AddMonoidAlgebra R G) :
    f ∈ AddMonoidAlgebra.grade R (0 : G) ↔
      ∃ a : R, groupAlgebraC R G a = f := by
  exact AddMonoidAlgebra.mem_grade_iff' R 0 f

/-- Every homogeneous ideal element belongs to the extension of the actual
weight-zero contraction. -/
theorem groupAlgebra_homogeneous_mem_map_comap
    (K : Ideal (AddMonoidAlgebra R G)) {f : AddMonoidAlgebra R G}
    (hhom : SetLike.IsHomogeneousElem (AddMonoidAlgebra.grade R) f)
    (hf : f ∈ K) :
    f ∈ (K.comap (groupAlgebraC R G)).map (groupAlgebraC R G) := by
  obtain ⟨g, a, rfl⟩ := (groupAlgebra_homogeneous_iff_single f).mp hhom
  have ha : groupAlgebraC R G a ∈ K := by
    simpa only [groupAlgebra_inverse_single_mul] using
      K.mul_mem_left (AddMonoidAlgebra.single (-g) 1) hf
  have hm := ((K.comap (groupAlgebraC R G)).map (groupAlgebraC R G)).mul_mem_right
    (AddMonoidAlgebra.single g 1) (Ideal.mem_map_of_mem (groupAlgebraC R G) ha)
  simpa using hm

/-- Identity-homogeneous group-algebra ideals are extended from their
coefficient contractions, without Noetherianity or domain hypotheses. -/
theorem groupAlgebra_homogeneousIdeal_eq_map_comap [DecidableEq G]
    (K : Ideal (AddMonoidAlgebra R G))
    (hK : K.IsHomogeneous (AddMonoidAlgebra.grade R)) :
    K = (K.comap (groupAlgebraC R G)).map (groupAlgebraC R G) := by
  obtain ⟨s, hs⟩ := (Ideal.IsHomogeneous.iff_exists (AddMonoidAlgebra.grade R) K).mp hK
  apply le_antisymm
  · calc
      K = Ideal.span ((↑) '' s) := hs
      _ ≤ (K.comap (groupAlgebraC R G)).map (groupAlgebraC R G) := by
        apply Ideal.span_le.mpr
        rintro f ⟨g, hg, rfl⟩
        apply groupAlgebra_homogeneous_mem_map_comap K g.property
        rw [hs]
        exact Ideal.subset_span ⟨g, hg, rfl⟩
  · exact Ideal.map_comap_le

/-- Coefficient membership characterizes any coefficient-extended ideal. -/
theorem groupAlgebra_mem_map_C_iff (I : Ideal R) (f : AddMonoidAlgebra R G) :
    f ∈ I.map (groupAlgebraC R G) ↔ ∀ g : G, f.coeff g ∈ I := by
  classical
  let L : AddMonoidAlgebra R G →+* AddMonoidAlgebra (R ⧸ I) G :=
    AddMonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I)
  have hker : I.map (groupAlgebraC R G) ≤ RingHom.ker L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change L (AddMonoidAlgebra.single 0 a) = 0
    simp only [L, AddMonoidAlgebra.mapRingHom_single,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, AddMonoidAlgebra.single_zero]
  constructor
  · intro hf g
    have hzero : L f = 0 := hker hf
    have he := congrArg (fun q : AddMonoidAlgebra (R ⧸ I) G => q.coeff g) hzero
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [L, AddMonoidAlgebra.coeff_mapRingHom,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he
  · intro hf
    rw [← AddMonoidAlgebra.sum_coeff_single f]
    change (∑ g ∈ f.coeff.support, AddMonoidAlgebra.single g (f.coeff g)) ∈
      I.map (groupAlgebraC R G)
    apply Ideal.sum_mem
    intro g hg
    have hm := (I.map (groupAlgebraC R G)).mul_mem_right
      (AddMonoidAlgebra.single g 1) (Ideal.mem_map_of_mem (groupAlgebraC R G) (hf g))
    simpa using hm

theorem groupAlgebra_homogeneousIdeal_coeff_mem [DecidableEq G]
    (K : Ideal (AddMonoidAlgebra R G))
    (hK : K.IsHomogeneous (AddMonoidAlgebra.grade R))
    {f : AddMonoidAlgebra R G} (hf : f ∈ K) (g : G) :
    f.coeff g ∈ K.comap (groupAlgebraC R G) := by
  rw [groupAlgebra_homogeneousIdeal_eq_map_comap K hK] at hf
  exact (groupAlgebra_mem_map_C_iff _ f).mp hf g

end GroupAlgebra

section FiniteRank

variable (R : Type*) [CommRing R]

/-- Split off the first integer Laurent exponent. -/
def finLaurentExponentSucc (h : ℕ) :
    (Fin (h + 1) → ℤ) ≃+ (ℤ × (Fin h → ℤ)) where
  toFun d := (d 0, fun i => d i.succ)
  invFun d := Fin.cons d.1 d.2
  left_inv d := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv d := by rcases d with ⟨a, d⟩; rfl
  map_add' d e := rfl

/-- Genuine multivariate Laurent polynomials are iterated literal Laurent
polynomials, by the explicit split of their exponent groups. -/
def multivariateLaurentSuccEquiv (h : ℕ) :
    AddMonoidAlgebra R (Fin (h + 1) → ℤ) ≃ₐ[R]
      LaurentPolynomial (AddMonoidAlgebra R (Fin h → ℤ)) :=
  (AddMonoidAlgebra.domCongr R R (finLaurentExponentSucc h)).trans
    (AddMonoidAlgebra.curryAlgEquiv R)

@[simp] theorem multivariateLaurentSuccEquiv_single (h : ℕ)
    (d : Fin (h + 1) → ℤ) (a : R) :
    multivariateLaurentSuccEquiv R h (AddMonoidAlgebra.single d a) =
      AddMonoidAlgebra.single (d 0) (AddMonoidAlgebra.single (fun i => d i.succ) a) := by
  simp [multivariateLaurentSuccEquiv, finLaurentExponentSucc]

theorem multivariateLaurentSuccEquiv_comp_C (h : ℕ) :
    (multivariateLaurentSuccEquiv R h).toRingHom.comp
      (groupAlgebraC R (Fin (h + 1) → ℤ)) =
    LaurentPolynomial.C.comp (groupAlgebraC R (Fin h → ℤ)) := by
  apply RingHom.ext
  intro a
  change multivariateLaurentSuccEquiv R h (AddMonoidAlgebra.single 0 a) =
    AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 a)
  rw [multivariateLaurentSuccEquiv_single]
  rfl

variable [IsNoetherianRing R]

/-- The actual finite-rank group algebra is Noetherian, proved by the
explicit Laurent decomposition. -/
theorem multivariateLaurent_isNoetherian (h : ℕ) :
    IsNoetherianRing (AddMonoidAlgebra R (Fin h → ℤ)) := by
  induction h with
  | zero =>
      exact isNoetherianRing_of_ringEquiv R
        (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).symm.toRingEquiv
  | succ h ih =>
      let : IsNoetherianRing (AddMonoidAlgebra R (Fin h → ℤ)) := ih
      let : IsNoetherianRing (LaurentPolynomial (AddMonoidAlgebra R (Fin h → ℤ))) :=
        IsLocalization.isNoetherianRing
          (Submonoid.powers (Polynomial.X : Polynomial (AddMonoidAlgebra R (Fin h → ℤ))))
          _ inferInstance
      exact isNoetherianRing_of_ringEquiv _
        (multivariateLaurentSuccEquiv R h).symm.toRingEquiv

/-- Coefficient extension to a genuine finite multivariate Laurent ring
preserves height for every ideal, including the unit ideal. -/
theorem multivariateLaurent_height_map_C (h : ℕ) (I : Ideal R) :
    (I.map (groupAlgebraC R (Fin h → ℤ))).height = I.height := by
  induction h with
  | zero =>
      have he : (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).symm.toRingHom =
          groupAlgebraC R (Fin 0 → ℤ) := by
        apply RingHom.ext
        intro a
        exact AddMonoidAlgebra.uniqueAlgEquiv_symm_apply R (Fin 0 → ℤ) a
      rw [← he]
      exact (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).symm.toRingEquiv.height_map I
  | succ h ih =>
      let : IsNoetherianRing (AddMonoidAlgebra R (Fin h → ℤ)) :=
        multivariateLaurent_isNoetherian R h
      let e := multivariateLaurentSuccEquiv R h
      calc
        (I.map (groupAlgebraC R (Fin (h + 1) → ℤ))).height =
            ((I.map (groupAlgebraC R (Fin (h + 1) → ℤ))).map e.toRingHom).height :=
          (e.toRingEquiv.height_map _).symm
        _ = ((I.map (groupAlgebraC R (Fin h → ℤ))).map LaurentPolynomial.C).height := by
          rw [Ideal.map_map, multivariateLaurentSuccEquiv_comp_C, ← Ideal.map_map]
        _ = (I.map (groupAlgebraC R (Fin h → ℤ))).height :=
          laurentPolynomialIdeal_height_map_C _
        _ = I.height := ih

/-- The standard multigraded homogeneous Laurent ideal is extended from
its entire weight-zero coefficient contraction, with exactly the same height.
This covers the manuscript's independent-weight Laurent applications. -/
theorem multivariateLaurent_homogeneousIdeal_height (h : ℕ)
    (K : Ideal (AddMonoidAlgebra R (Fin h → ℤ)))
    (hK : K.IsHomogeneous (AddMonoidAlgebra.grade R)) :
    K.height = (K.comap (groupAlgebraC R (Fin h → ℤ))).height := by
  calc
    K.height = ((K.comap (groupAlgebraC R (Fin h → ℤ))).map
        (groupAlgebraC R (Fin h → ℤ))).height :=
      congrArg Ideal.height (groupAlgebra_homogeneousIdeal_eq_map_comap K hK)
    _ = (K.comap (groupAlgebraC R (Fin h → ℤ))).height :=
      multivariateLaurent_height_map_C R h _

end FiniteRank

end AbelFormalization
