import AbelFormalization.LaurentRescaling

/-!
# Rescaling polynomial variables by arbitrary group Laurent monomials

The construction is an actual exponent shear, with no domain, finite-variable, or order assumption.
For G = Fin h → ℤ it supplies the independent Laurent-coordinate substitutions
used in the paper's central-ideal construction.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {R ι G : Type*} [CommSemiring R] [AddCommGroup G]

/-- The additive shear of a group Laurent exponent by a polynomial weight. -/
def groupLaurentExponentShear (ω : ι → G) :
    (G × (ι →₀ ℕ)) ≃+ (G × (ι →₀ ℕ)) where
  toFun a := (a.1 + Finsupp.weight ω a.2, a.2)
  invFun a := (a.1 - Finsupp.weight ω a.2, a.2)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

@[simp] theorem groupLaurentExponentShear_apply (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) :
    groupLaurentExponentShear ω (g, d) = (g + Finsupp.weight ω d, d) := rfl

@[simp] theorem groupLaurentExponentShear_symm_apply (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) :
    (groupLaurentExponentShear ω).symm (g, d) =
      (g - Finsupp.weight ω d, d) := rfl

/-- Flatten the Laurent and polynomial indices without altering coefficients. -/
def groupLaurentPolynomialFlatten :
    AddMonoidAlgebra (MvPolynomial ι R) G ≃ₐ[R]
      AddMonoidAlgebra R (G × (ι →₀ ℕ)) :=
  (AddMonoidAlgebra.curryAlgEquiv R).symm

@[simp] theorem groupLaurentPolynomialFlatten_coeff
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) (g : G) (d : ι →₀ ℕ) :
    (groupLaurentPolynomialFlatten f).coeff (g, d) = (f.coeff g).coeff d := rfl

@[simp] theorem groupLaurentPolynomialFlatten_symm_coeff
    (f : AddMonoidAlgebra R (G × (ι →₀ ℕ))) (g : G) (d : ι →₀ ℕ) :
    ((groupLaurentPolynomialFlatten.symm f).coeff g).coeff d = f.coeff (g, d) := rfl

@[simp] theorem groupLaurentPolynomialFlatten_single_monomial
    (g : G) (d : ι →₀ ℕ) (c : R) :
    groupLaurentPolynomialFlatten (AddMonoidAlgebra.single g (MvPolynomial.monomial d c)) =
      AddMonoidAlgebra.single (g, d) c := by
  rw [← MvPolynomial.single_eq_monomial]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single g d c

@[simp] theorem groupLaurentPolynomialFlatten_symm_single
    (g : G) (d : ι →₀ ℕ) (c : R) :
    groupLaurentPolynomialFlatten.symm (AddMonoidAlgebra.single (g, d) c) =
      AddMonoidAlgebra.single g (MvPolynomial.monomial d c) := by
  rw [← groupLaurentPolynomialFlatten_single_monomial]
  exact groupLaurentPolynomialFlatten.symm_apply_apply _

/-- Rescale each polynomial variable zᵢ by the Laurent monomial of exponent ωᵢ.
The Laurent variables and the base coefficient ring are fixed. -/
def groupLaurentWeightRescaling (ω : ι → G) :
    AddMonoidAlgebra (MvPolynomial ι R) G ≃ₐ[R]
      AddMonoidAlgebra (MvPolynomial ι R) G :=
  groupLaurentPolynomialFlatten.trans
    ((AddMonoidAlgebra.domCongr R R (groupLaurentExponentShear ω)).trans
      groupLaurentPolynomialFlatten.symm)

@[simp] theorem groupLaurentWeightRescaling_single_monomial (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) (c : R) :
    groupLaurentWeightRescaling ω (AddMonoidAlgebra.single g (MvPolynomial.monomial d c)) =
      AddMonoidAlgebra.single (g + Finsupp.weight ω d) (MvPolynomial.monomial d c) := by
  simp [groupLaurentWeightRescaling]

/-- Each output exponent pair has exactly one input coefficient. -/
@[simp] theorem groupLaurentWeightRescaling_coeff (ω : ι → G)
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) (g : G) (d : ι →₀ ℕ) :
    ((groupLaurentWeightRescaling ω f).coeff g).coeff d =
      (f.coeff (g - Finsupp.weight ω d)).coeff d := by
  simp [groupLaurentWeightRescaling]

@[simp] theorem groupLaurentWeightRescaling_symm_single_monomial (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) (c : R) :
    (groupLaurentWeightRescaling ω).symm
      (AddMonoidAlgebra.single g (MvPolynomial.monomial d c)) =
      AddMonoidAlgebra.single (g - Finsupp.weight ω d) (MvPolynomial.monomial d c) := by
  apply (groupLaurentWeightRescaling ω).injective
  simp

@[simp] theorem groupLaurentWeightRescaling_single_one (ω : ι → G) (g : G) :
    groupLaurentWeightRescaling (R := R) ω (AddMonoidAlgebra.single g 1) =
      AddMonoidAlgebra.single g 1 := by
  simpa only [← MvPolynomial.one_def, map_zero, add_zero] using
    groupLaurentWeightRescaling_single_monomial (R := R) ω g 0 1

@[simp] theorem groupLaurentWeightRescaling_single_C (ω : ι → G) (c : R) :
    groupLaurentWeightRescaling ω (AddMonoidAlgebra.single 0 (MvPolynomial.C c)) =
      AddMonoidAlgebra.single 0 (MvPolynomial.C c) := by
  simpa only [← MvPolynomial.C_apply, map_zero, add_zero] using
    groupLaurentWeightRescaling_single_monomial ω 0 0 c

@[simp] theorem groupLaurentWeightRescaling_single_X (ω : ι → G) (i : ι) :
    groupLaurentWeightRescaling (R := R) ω (AddMonoidAlgebra.single 0 (MvPolynomial.X i)) =
      AddMonoidAlgebra.single (ω i) (MvPolynomial.X i) := by
  simpa only [← MvPolynomial.X_pow_eq_monomial, pow_one, zero_add,
    Finsupp.weight_single, one_smul] using
    groupLaurentWeightRescaling_single_monomial (R := R) ω 0 (Finsupp.single i 1) 1

theorem group_finsupp_weight_neg (ω : ι → G) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => -ω i) d = -Finsupp.weight ω d := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib]

theorem group_finsupp_weight_add (ω ν : ι → G) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => ω i + ν i) d =
      Finsupp.weight ω d + Finsupp.weight ν d := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_add_distrib]

/-- The inverse substitution has exactly the opposite weights. -/
theorem groupLaurentWeightRescaling_symm (ω : ι → G) :
    (groupLaurentWeightRescaling (R := R) ω).symm =
      groupLaurentWeightRescaling (fun i => -ω i) := by
  apply AlgEquiv.ext
  intro f
  apply (groupLaurentWeightRescaling ω).injective
  rw [AlgEquiv.apply_symm_apply]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply MvPolynomial.ext
  intro d
  simp only [groupLaurentWeightRescaling_coeff, group_finsupp_weight_neg,
    sub_neg_eq_add, sub_add_cancel]

/-- Composing actual rescalings adds their group-valued weights. -/
theorem groupLaurentWeightRescaling_trans (ω ν : ι → G) :
    (groupLaurentWeightRescaling (R := R) ω).trans (groupLaurentWeightRescaling ν) =
      groupLaurentWeightRescaling (fun i => ω i + ν i) := by
  apply AlgEquiv.ext
  intro f
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply MvPolynomial.ext
  intro d
  change ((groupLaurentWeightRescaling ν (groupLaurentWeightRescaling ω f)).coeff g).coeff d = _
  simp only [groupLaurentWeightRescaling_coeff, group_finsupp_weight_add]
  congr 2
  abel_nf

end AbelFormalization
