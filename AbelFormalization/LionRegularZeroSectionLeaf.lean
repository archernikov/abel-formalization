import AbelFormalization.LionCarpetedLeaf

/-!
# Regular zero-section leaves

Lion's Lemma 4 covers its critical trace by finitely many leaves obtained as
follows.  Choose a subtuple `h` of critical-form coefficients, append it to
the old leaf equations `f`, restrict to the regular locus of `(f,h)`, and
take the zero fiber.  This file packages exactly that construction.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q s : ℕ}

/-- The regular zero section cut out by a family-valued tuple `h` on a
carpeted leaf.  Its defining equations are `(f,h)`, so its codimension is
`q+s`; Lion's Lemma 3 supplies the carpet on the regular locus. -/
def regularZeroSectionLeaf
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (h : RealEuclidean n → RealEuclidean s)
    (hh : FunctionTupleInFamily G h) :
    LionCarpetedLeaf G n (q + s) where
  U := L.regularLocus h
  isOpen_U := L.regularLocus_isOpen hG hsmooth hderiv h hh
  delta := L.regularCarpet h
  isCarpet := L.regularCarpet_isLionCarpetOn hG hsmooth hderiv h hh
  delta_mem := L.regularCarpet_mem hG hderiv h hh
  equations := L.definingTupleAppend h
  equations_mem := L.definingTupleAppend_mem h hh
  fderiv_surjective := fun _x hx ↦ hx.2

@[simp]
theorem regularZeroSectionLeaf_U
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (h : RealEuclidean n → RealEuclidean s)
    (hh : FunctionTupleInFamily G h) :
    (L.regularZeroSectionLeaf hG hsmooth hderiv h hh).U =
      L.regularLocus h :=
  rfl

@[simp]
theorem regularZeroSectionLeaf_delta
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (h : RealEuclidean n → RealEuclidean s)
    (hh : FunctionTupleInFamily G h) :
    (L.regularZeroSectionLeaf hG hsmooth hderiv h hh).delta =
      L.regularCarpet h :=
  rfl

@[simp]
theorem regularZeroSectionLeaf_equations
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (h : RealEuclidean n → RealEuclidean s)
    (hh : FunctionTupleInFamily G h) :
    (L.regularZeroSectionLeaf hG hsmooth hderiv h hh).equations =
      L.definingTupleAppend h :=
  rfl

/-- Exact source description: the new leaf consists of points of the old
leaf where the selected coefficient tuple vanishes and `(f,h)` has full
rank. -/
theorem regularZeroSectionLeaf_carrier
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (h : RealEuclidean n → RealEuclidean s)
    (hh : FunctionTupleInFamily G h) :
    (L.regularZeroSectionLeaf hG hsmooth hderiv h hh).carrier =
      {x | x ∈ L.carrier ∧ h x = 0 ∧
        Function.Surjective (fderiv ℝ (L.definingTupleAppend h) x)} := by
  ext x
  simp only [carrier, regularZeroSectionLeaf, regularLocus,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hxU, hxsurj⟩, htuple⟩
    have hfzero : L.equations x = 0 := by
      funext i
      have hi := congrFun htuple (Fin.castAdd s i)
      simpa using hi
    have hhzero : h x = 0 := by
      funext j
      have hj := congrFun htuple (Fin.natAdd q j)
      simpa using hj
    exact ⟨⟨hxU, hfzero⟩, hhzero, hxsurj⟩
  · rintro ⟨⟨hxU, hfzero⟩, hhzero, hxsurj⟩
    refine ⟨⟨hxU, hxsurj⟩, ?_⟩
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa using congrFun hfzero i
    · simpa using congrFun hhzero j

/-- Set-theoretic form matching the notation `F⁻¹(0) ∩ U_F` in the
paper. -/
theorem regularZeroSectionLeaf_carrier_eq_inter
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (h : RealEuclidean n → RealEuclidean s)
    (hh : FunctionTupleInFamily G h) :
    (L.regularZeroSectionLeaf hG hsmooth hderiv h hh).carrier =
      (L.carrier ∩ h ⁻¹' {(0 : RealEuclidean s)}) ∩
        L.regularLocus h := by
  rw [L.regularZeroSectionLeaf_carrier hG hsmooth hderiv h hh]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff, regularLocus]
  constructor
  · rintro ⟨hxcarrier, hhzero, hsurj⟩
    exact ⟨⟨hxcarrier, hhzero⟩, hxcarrier.1, hsurj⟩
  · rintro ⟨⟨hxcarrier, hhzero⟩, _hxU, hsurj⟩
    exact ⟨hxcarrier, hhzero, hsurj⟩

end LionCarpetedLeaf

end AbelFormalization
