import AbelFormalization.PolynomialGermIdentities
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false

/-!
# Renaming independent symbols in polynomial-valued analytic germs

The polynomial-valued germ homomorphism commutes with arbitrary maps of
symbols, including noninjective ones. Consequently, the chosen polynomial
representatives of a finite family give representatives for its flat
unit-variable augmentation by literal pointwise ring operations.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

section GenericGerms

variable {E R ι τ : Type*} [CommSemiring R]

/-- Independent symbols are represented by constant polynomial-valued
functions. -/
@[simp]
theorem polynomialGermHom_X (l : Filter E) (i : ι) :
    polynomialGermHom l (MvPolynomial.X i : MvPolynomial ι (Germ l R)) =
      ((fun _ : E => (MvPolynomial.X i : MvPolynomial ι R)) :
        Germ l (MvPolynomial ι R)) := by
  simp only [polynomialGermHom, MvPolynomial.eval₂Hom_X', germConstRingHom_apply]

@[simp]
theorem polynomialGermHom_one (l : Filter E) :
    polynomialGermHom l (1 : MvPolynomial ι (Germ l R)) =
      ((fun _ : E => (1 : MvPolynomial ι R)) : Germ l (MvPolynomial ι R)) :=
  map_one (polynomialGermHom l)

/-- Naturality of the polynomial-valued germ construction with respect to
an arbitrary renaming of independent polynomial symbols. -/
theorem polynomialGermHom_rename (l : Filter E) (r : ι → τ)
    (P : MvPolynomial ι (Germ l R)) :
    polynomialGermHom l (MvPolynomial.rename r P) =
      germMapRingHom l (MvPolynomial.rename r).toRingHom
        (polynomialGermHom l P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    refine Germ.inductionOn c ?_
    intro a
    rw [MvPolynomial.rename_monomial, polynomialGermHom_monomial_coe,
      polynomialGermHom_monomial_coe, germMapRingHom_coe]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun w => (MvPolynomial.rename_monomial r d (a w)).symm
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]

end GenericGerms

section AnalyticPolynomialGerms

variable {E ι τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp]
theorem analyticPolynomialGermHom_X (x : E) (i : ι) :
    analyticPolynomialGermHom x
        (MvPolynomial.X i : MvPolynomial ι (AnalyticGermAt x)) =
      ((fun _ : E => (MvPolynomial.X i : MvPolynomial ι ℝ)) :
        Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  simpa only [analyticPolynomialGermHom, RingHom.comp_apply, MvPolynomial.map_X] using
    (polynomialGermHom_X (R := ℝ) (𝓝 x) i)

@[simp]
theorem analyticPolynomialGermHom_one (x : E) :
    analyticPolynomialGermHom x (1 : MvPolynomial ι (AnalyticGermAt x)) =
      ((fun _ : E => (1 : MvPolynomial ι ℝ)) : Germ (𝓝 x) (MvPolynomial ι ℝ)) :=
  map_one (analyticPolynomialGermHom x)

/-- The canonical map for actual analytic coefficient germs commutes with
renaming the independent polynomial symbols. -/
theorem analyticPolynomialGermHom_rename (x : E) (r : ι → τ)
    (P : MvPolynomial ι (AnalyticGermAt x)) :
    analyticPolynomialGermHom x (MvPolynomial.rename r P) =
      germMapRingHom (𝓝 x) (MvPolynomial.rename r).toRingHom
        (analyticPolynomialGermHom x P) := by
  unfold analyticPolynomialGermHom
  rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_rename]
  exact polynomialGermHom_rename (𝓝 x) r _

/-- Any chosen polynomial-valued representative remains a representative
after the same pointwise renaming of symbols. -/
theorem analyticPolynomialGermHom_rename_of (x : E) (r : ι → τ)
    {P : MvPolynomial ι (AnalyticGermAt x)} {F : E → MvPolynomial ι ℝ}
    (hF : analyticPolynomialGermHom x P =
      (F : Germ (𝓝 x) (MvPolynomial ι ℝ))) :
    analyticPolynomialGermHom x (MvPolynomial.rename r P) =
      ((fun w => MvPolynomial.rename r (F w)) : Germ (𝓝 x) (MvPolynomial τ ℝ)) := by
  calc
    analyticPolynomialGermHom x (MvPolynomial.rename r P) =
        germMapRingHom (𝓝 x) (MvPolynomial.rename r).toRingHom
          (analyticPolynomialGermHom x P) := analyticPolynomialGermHom_rename x r P
    _ = germMapRingHom (𝓝 x) (MvPolynomial.rename r).toRingHom
        (F : Germ (𝓝 x) (MvPolynomial ι ℝ)) :=
      congrArg (germMapRingHom (𝓝 x) (MvPolynomial.rename r).toRingHom) hF
    _ = _ := germMapRingHom_coe (𝓝 x) (MvPolynomial.rename r).toRingHom F

/-- The relation adjoining the inverse of a polynomial has the literal
representative obtained by adjoining one new independent symbol. -/
theorem analyticPolynomialGermHom_unitRelation_of (x : E)
    {d : MvPolynomial ι (AnalyticGermAt x)} {dF : E → MvPolynomial ι ℝ}
    (hd : analyticPolynomialGermHom x d =
      (dF : Germ (𝓝 x) (MvPolynomial ι ℝ))) :
    analyticPolynomialGermHom x
        (MvPolynomial.X none * MvPolynomial.rename some d - 1) =
      ((fun w => MvPolynomial.X none * MvPolynomial.rename some (dF w) - 1) :
        Germ (𝓝 x) (MvPolynomial (Option ι) ℝ)) := by
  rw [map_sub, map_mul, analyticPolynomialGermHom_X,
    analyticPolynomialGermHom_rename_of x some hd, analyticPolynomialGermHom_one]
  simpa only [map_mul] using!
    (map_sub (Germ.coeRingHom (𝓝 x))
      ((fun _ : E => (MvPolynomial.X none : MvPolynomial (Option ι) ℝ)) *
        (fun w => MvPolynomial.rename some (dF w)))
      (fun _ : E => (1 : MvPolynomial (Option ι) ℝ))).symm

/-- One original finite family of representatives and one denominator
representative give all representatives of the flat augmented tuple. The
identity is in germs of polynomials and makes no assertion of simultaneous
nearby evaluation of the entire ring of analytic germs. -/
theorem analyticPolynomialGermHom_flatUnitAugmentedTuple (x : E) {n : ℕ}
    (P : Fin n → MvPolynomial ι (AnalyticGermAt x))
    (d : MvPolynomial ι (AnalyticGermAt x))
    (F : Fin n → E → MvPolynomial ι ℝ) (dF : E → MvPolynomial ι ℝ)
    (hF : ∀ i, analyticPolynomialGermHom x (P i) =
      (F i : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hd : analyticPolynomialGermHom x d =
      (dF : Germ (𝓝 x) (MvPolynomial ι ℝ))) :
    ∀ i : Fin (n + 1),
      analyticPolynomialGermHom x
          (Fin.cons (α := fun _ : Fin (n + 1) => MvPolynomial (Option ι) (AnalyticGermAt x))
            (MvPolynomial.X none * MvPolynomial.rename some d - 1)
            (fun j => MvPolynomial.rename some (P j)) i) =
        ((fun w =>
          Fin.cons (α := fun _ : Fin (n + 1) => MvPolynomial (Option ι) ℝ)
            (MvPolynomial.X none * MvPolynomial.rename some (dF w) - 1)
            (fun j => MvPolynomial.rename some (F j w)) i) :
          Germ (𝓝 x) (MvPolynomial (Option ι) ℝ)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using analyticPolynomialGermHom_unitRelation_of x hd
  · simpa only [Fin.cons_succ] using analyticPolynomialGermHom_rename_of x some (hF j)

end AnalyticPolynomialGerms

end AbelFormalization
